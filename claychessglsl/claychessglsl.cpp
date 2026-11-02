//Perft
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX

#include <windows.h>
#include <GL/glew.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
#include <thread>
#include <atomic>
#include <mutex>
#include <iostream>
#include <sstream>
#include <cctype>
#include <limits>

#pragma comment(lib, "opengl32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")
// 工程还需要链接 GLEW：glew32.lib（或你的静态 GLEW 配置）

// wglext constants kept local so this file does not require <GL/wglew.h>.
#ifndef WGL_CONTEXT_MAJOR_VERSION_ARB
#define WGL_CONTEXT_MAJOR_VERSION_ARB 0x2091
#endif
#ifndef WGL_CONTEXT_MINOR_VERSION_ARB
#define WGL_CONTEXT_MINOR_VERSION_ARB 0x2092
#endif
#ifndef WGL_CONTEXT_FLAGS_ARB
#define WGL_CONTEXT_FLAGS_ARB 0x2094
#endif
#ifndef WGL_CONTEXT_PROFILE_MASK_ARB
#define WGL_CONTEXT_PROFILE_MASK_ARB 0x9126
#endif
#ifndef WGL_CONTEXT_CORE_PROFILE_BIT_ARB
#define WGL_CONTEXT_CORE_PROFILE_BIT_ARB 0x00000001
#endif

typedef HGLRC(WINAPI* PFNWGLCREATECONTEXTATTRIBSARBPROC_LOCAL)(HDC, HGLRC, const int*);

static HWND  g_hwnd = nullptr;
static HDC   g_hdc = nullptr;
static HGLRC g_glrc = nullptr;
static bool  g_running = true;

static int g_winW = 800;
static int g_winH = 600;

// ============================================================
// CPU game state
// 0 empty; 1..6 white P N B R Q K; -1..-6 black p n b r q k
// ============================================================
static int8_t g_board[64] = {};
static int    g_sideToMove = 1;
static int    g_castling = 15; // WK=1 WQ=2 BK=4 BQ=8
static int    g_epSq = -1;
static int    g_fromSq = -1;
static bool   g_gameOver = false;

static bool g_hasPendingClick = false;
static int  g_pendingSq = -1;
static bool g_boardTextureDirty = true;

// ============================================================
// Console search request
// ============================================================
static std::atomic<int>  g_searchDepthRequest{ 0 };
static std::atomic<bool> g_consoleRunning{ false };
static std::mutex        g_consoleMutex;

// ============================================================
// OpenGL visualization resources
// ============================================================
static GLuint g_quadVAO = 0;
static GLuint g_quadVBO = 0;
static GLuint g_visProg = 0;
static GLuint g_blitProg = 0;
static GLuint g_boardTex = 0;
static GLuint g_visTex = 0;
static GLuint g_visMaskTex = 0;
static GLuint g_visFbo = 0;

static GLint g_visLocBoard = -1;
static GLint g_visLocFrom = -1;
static GLint g_visLocSide = -1;
static GLint g_visLocCastling = -1;
static GLint g_visLocEp = -1;
static GLint g_visLocWhiteKing = -1;
static GLint g_visLocBlackKing = -1;
static GLint g_blitLocVis = -1;

// ============================================================
// Compute/SSBO search resources
// ============================================================
static GLuint g_expandProg = 0;
static GLuint g_countProg = 0;

static GLint  g_expandLocBasePosition = -1;
static GLint  g_expandLocPositionCount = -1;
static GLint  g_expandLocOutputCapacity = -1;
static GLint  g_expandLocCountOnly = -1;

static GLint  g_countLocBasePosition = -1;
static GLint  g_countLocPositionCount = -1;

static GLuint g_frontierSSBO[2] = { 0, 0 };
static uint64_t g_frontierCapacity[2] = { 0, 0 }; // number of GpuPosition records
static GLuint g_counterSSBO = 0;
static GLuint g_maxDispatchGroupsX = 65535;

// Full-frontier design is intentionally clamped here.
// depth=6 from the initial position stores the depth-5 frontier (~4.86M positions)
// and counts depth-6 leaves without storing them. Going one level deeper would need
// to materialize roughly 119M positions and several GB of VRAM.
static constexpr int kMaxGpuFrontierDepth = 6;
static constexpr uint64_t kInitialBranchCapacityFactor = 32;

// GPU format: 8 packed board words (8 squares/word, 4 bits/square) + one metadata word.
// 9 * uint32 = 36 bytes. GLSL std430 struct contains only uint scalars/array, so stride is 36.
struct GpuPosition {
    uint32_t board[8];
    uint32_t meta;
};
static_assert(sizeof(GpuPosition) == 36, "GpuPosition must be exactly 36 bytes");

struct GpuCounters {
    uint32_t outCount;
    uint32_t overflow;
    uint32_t leafLo;
    uint32_t leafHi;
};
static_assert(sizeof(GpuCounters) == 16, "GpuCounters size mismatch");

struct SearchStats {
    uint64_t computeDispatches = 0;
    uint64_t expandedFrontierPositions = 0;
    uint64_t generatedPositions = 0;
    uint64_t retryPasses = 0;
    uint64_t peakFrontier = 1;
    uint64_t peakAllocatedBytes = 0;
};

// ============================================================
// Utilities
// ============================================================
static void Fatal(const char* msg) {
    MessageBoxA(nullptr, msg, "Fatal", MB_ICONERROR | MB_OK);
    ExitProcess(1);
}

static void PrintConsoleLine(const std::string& s) {
    std::lock_guard<std::mutex> lock(g_consoleMutex);
    std::cout << s << std::endl;
}

static int sqX(int sq) { return sq & 7; }
static int sqY(int sq) { return sq >> 3; }
static int sqOf(int x, int y) { return (y << 3) | x; }
static int sideOf(int p) { return (p > 0) ? 1 : ((p < 0) ? -1 : 0); }
static int absP(int p) { return (p < 0) ? -p : p; }

static int FindKingSqCPU(int side) {
    const int target = 6 * side;
    for (int sq = 0; sq < 64; ++sq) {
        if ((int)g_board[sq] == target) return sq;
    }
    return -1;
}

static void SetTitle(const std::string& s) {
    if (g_hwnd) SetWindowTextA(g_hwnd, s.c_str());
}

static void UpdateTitleStatus(const char* status) {
    std::string t = (g_sideToMove == 1) ? "White to move" : "Black to move";
    if (status && status[0]) {
        t += " | ";
        t += status;
    }
    t += " | Click: select+move | R: reset | B: search4 | console: search N";
    SetTitle(t);
}

static void CheckGLError(const char* where) {
    GLenum e = glGetError();
    if (e == GL_NO_ERROR) return;

    char buf[256];
    std::snprintf(buf, sizeof(buf), "OpenGL error 0x%04X at %s", (unsigned)e, where);
    Fatal(buf);
}

// ============================================================
// Win32 + explicit OpenGL 4.3 context
// ============================================================
static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_CLOSE:
        DestroyWindow(hwnd);
        return 0;

    case WM_DESTROY:
        g_running = false;
        PostQuitMessage(0);
        return 0;

    case WM_SIZE: {
        int w = LOWORD(lParam);
        int h = HIWORD(lParam);
        if (w > 0 && h > 0) {
            g_winW = w;
            g_winH = h;
        }
        return 0;
    }

    case WM_LBUTTONDOWN: {
        int mx = (int)(short)LOWORD(lParam);
        int my = (int)(short)HIWORD(lParam);

        RECT rc{};
        GetClientRect(hwnd, &rc);
        int cw = rc.right - rc.left;
        int ch = rc.bottom - rc.top;
        if (cw <= 0 || ch <= 0) return 0;

        int x = (mx * 8) / cw;
        int y = ((ch - 1 - my) * 8) / ch;
        x = std::clamp(x, 0, 7);
        y = std::clamp(y, 0, 7);

        g_pendingSq = sqOf(x, y);
        g_hasPendingClick = true;
        return 0;
    }

    case WM_KEYDOWN:
        if (wParam == 'R') {
            g_pendingSq = -999;
            g_hasPendingClick = true;
        }
        if (wParam == 'B') {
            g_searchDepthRequest.store(4);
        }
        return 0;

    default:
        return DefWindowProc(hwnd, msg, wParam, lParam);
    }
}

static void CreateWindowAndContext43() {
    HINSTANCE hInst = GetModuleHandle(nullptr);

    WNDCLASSA wc{};
    wc.style = CS_OWNDC;
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.lpszClassName = "GLWinClassChessCompute43";
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);

    if (!RegisterClassA(&wc)) Fatal("RegisterClass failed.");

    DWORD style = WS_OVERLAPPEDWINDOW;
    RECT rc{ 0, 0, g_winW, g_winH };
    AdjustWindowRect(&rc, style, FALSE);

    g_hwnd = CreateWindowA(
        wc.lpszClassName,
        "GLSL Chess - GL4.3 SSBO Frontier 32-Lane",
        style,
        CW_USEDEFAULT, CW_USEDEFAULT,
        rc.right - rc.left,
        rc.bottom - rc.top,
        nullptr, nullptr, hInst, nullptr
    );
    if (!g_hwnd) Fatal("CreateWindow failed.");

    g_hdc = GetDC(g_hwnd);
    if (!g_hdc) Fatal("GetDC failed.");

    PIXELFORMATDESCRIPTOR pfd{};
    pfd.nSize = sizeof(pfd);
    pfd.nVersion = 1;
    pfd.dwFlags = PFD_DRAW_TO_WINDOW | PFD_SUPPORT_OPENGL | PFD_DOUBLEBUFFER;
    pfd.iPixelType = PFD_TYPE_RGBA;
    pfd.cColorBits = 32;
    pfd.cDepthBits = 24;
    pfd.cStencilBits = 8;
    pfd.iLayerType = PFD_MAIN_PLANE;

    int pf = ChoosePixelFormat(g_hdc, &pfd);
    if (!pf) Fatal("ChoosePixelFormat failed.");
    if (!SetPixelFormat(g_hdc, pf, &pfd)) Fatal("SetPixelFormat failed.");

    // Bootstrap context only to obtain wglCreateContextAttribsARB.
    HGLRC temp = wglCreateContext(g_hdc);
    if (!temp) Fatal("Temporary wglCreateContext failed.");
    if (!wglMakeCurrent(g_hdc, temp)) Fatal("Temporary wglMakeCurrent failed.");

    glewExperimental = GL_TRUE;
    GLenum ge = glewInit();
    glGetError();
    if (ge != GLEW_OK) {
        Fatal(reinterpret_cast<const char*>(glewGetErrorString(ge)));
    }

    auto createAttribs = reinterpret_cast<PFNWGLCREATECONTEXTATTRIBSARBPROC_LOCAL>(
        wglGetProcAddress("wglCreateContextAttribsARB")
        );
    if (!createAttribs) {
        Fatal("WGL_ARB_create_context is unavailable. OpenGL 4.3 context cannot be requested.");
    }

    const int attribs[] = {
        WGL_CONTEXT_MAJOR_VERSION_ARB, 4,
        WGL_CONTEXT_MINOR_VERSION_ARB, 3,
        WGL_CONTEXT_PROFILE_MASK_ARB, WGL_CONTEXT_CORE_PROFILE_BIT_ARB,
        0
    };

    HGLRC modern = createAttribs(g_hdc, nullptr, attribs);
    if (!modern) {
        Fatal("Failed to create OpenGL 4.3 core context. Check GPU/driver OpenGL 4.3 support.");
    }

    wglMakeCurrent(nullptr, nullptr);
    wglDeleteContext(temp);

    if (!wglMakeCurrent(g_hdc, modern)) Fatal("wglMakeCurrent(OpenGL 4.3) failed.");
    g_glrc = modern;

    glewExperimental = GL_TRUE;
    ge = glewInit();
    glGetError();
    if (ge != GLEW_OK) {
        Fatal(reinterpret_cast<const char*>(glewGetErrorString(ge)));
    }

    int major = 0, minor = 0;
    glGetIntegerv(GL_MAJOR_VERSION, &major);
    glGetIntegerv(GL_MINOR_VERSION, &minor);
    if (major < 4 || (major == 4 && minor < 3)) {
        Fatal("The active OpenGL context is below 4.3.");
    }

    GLint maxGroups = 0;
    glGetIntegeri_v(GL_MAX_COMPUTE_WORK_GROUP_COUNT, 0, &maxGroups);
    if (maxGroups > 0) g_maxDispatchGroupsX = (GLuint)maxGroups;

    GLint maxInvocations = 0;
    glGetIntegerv(GL_MAX_COMPUTE_WORK_GROUP_INVOCATIONS, &maxInvocations);
    if (maxInvocations < 64) {
        Fatal("GL_MAX_COMPUTE_WORK_GROUP_INVOCATIONS is below 64.");
    }

    ShowWindow(g_hwnd, SW_SHOW);

    std::ostringstream oss;
    oss << "[GL] " << reinterpret_cast<const char*>(glGetString(GL_VERSION))
        << " | " << reinterpret_cast<const char*>(glGetString(GL_RENDERER))
        << " | max dispatch X=" << g_maxDispatchGroupsX;
    PrintConsoleLine(oss.str());
}

// ============================================================
// Shader helpers
// ============================================================
static GLuint CompileShader(GLenum type, const char* src) {
    GLuint sh = glCreateShader(type);
    glShaderSource(sh, 1, &src, nullptr);
    glCompileShader(sh);

    GLint ok = 0;
    glGetShaderiv(sh, GL_COMPILE_STATUS, &ok);
    if (!ok) {
        GLint len = 0;
        glGetShaderiv(sh, GL_INFO_LOG_LENGTH, &len);
        std::string log((size_t)std::max(1, len), '\0');
        glGetShaderInfoLog(sh, (GLsizei)log.size(), nullptr, log.data());

        std::string msg = "Shader compile failed:\n";
        msg += log;
        Fatal(msg.c_str());
    }
    return sh;
}

static GLuint LinkProgram2(GLuint a, GLuint b) {
    GLuint p = glCreateProgram();
    glAttachShader(p, a);
    glAttachShader(p, b);
    glLinkProgram(p);

    GLint ok = 0;
    glGetProgramiv(p, GL_LINK_STATUS, &ok);
    if (!ok) {
        GLint len = 0;
        glGetProgramiv(p, GL_INFO_LOG_LENGTH, &len);
        std::string log((size_t)std::max(1, len), '\0');
        glGetProgramInfoLog(p, (GLsizei)log.size(), nullptr, log.data());
        std::string msg = "Program link failed:\n";
        msg += log;
        Fatal(msg.c_str());
    }
    return p;
}

static GLuint LinkProgram1(GLuint sh) {
    GLuint p = glCreateProgram();
    glAttachShader(p, sh);
    glLinkProgram(p);

    GLint ok = 0;
    glGetProgramiv(p, GL_LINK_STATUS, &ok);
    if (!ok) {
        GLint len = 0;
        glGetProgramiv(p, GL_INFO_LOG_LENGTH, &len);
        std::string log((size_t)std::max(1, len), '\0');
        glGetProgramInfoLog(p, (GLsizei)log.size(), nullptr, log.data());
        std::string msg = "Program link failed:\n";
        msg += log;
        Fatal(msg.c_str());
    }
    return p;
}

static GLuint BuildGraphicsProgram(const char* vsSrc, const char* fsSrc) {
    GLuint vs = CompileShader(GL_VERTEX_SHADER, vsSrc);
    GLuint fs = CompileShader(GL_FRAGMENT_SHADER, fsSrc);
    GLuint p = LinkProgram2(vs, fs);
    glDeleteShader(vs);
    glDeleteShader(fs);
    return p;
}

static GLuint BuildComputeProgram(const char* csSrc) {
    GLuint cs = CompileShader(GL_COMPUTE_SHADER, csSrc);
    GLuint p = LinkProgram1(cs);
    glDeleteShader(cs);
    return p;
}

static GLuint BuildComputeProgramParts(const char* const* parts, GLsizei partCount) {
    GLuint cs = glCreateShader(GL_COMPUTE_SHADER);
    glShaderSource(cs, partCount, parts, nullptr);
    glCompileShader(cs);

    GLint ok = 0;
    glGetShaderiv(cs, GL_COMPILE_STATUS, &ok);
    if (!ok) {
        GLint len = 0;
        glGetShaderiv(cs, GL_INFO_LOG_LENGTH, &len);
        std::string log((size_t)std::max(1, len), '\0');
        glGetShaderInfoLog(cs, (GLsizei)log.size(), nullptr, log.data());
        std::string msg = "Compute shader compile failed:\n";
        msg += log;
        Fatal(msg.c_str());
    }

    GLuint p = LinkProgram1(cs);
    glDeleteShader(cs);
    return p;
}

// ============================================================
// Visualization geometry / texture / FBO
// ============================================================
static void InitQuad() {
    const float v[] = {
        -1.f, -1.f,   0.f, 0.f,
         1.f, -1.f,   1.f, 0.f,
         1.f,  1.f,   1.f, 1.f,
        -1.f, -1.f,   0.f, 0.f,
         1.f,  1.f,   1.f, 1.f,
        -1.f,  1.f,   0.f, 1.f,
    };

    glGenVertexArrays(1, &g_quadVAO);
    glGenBuffers(1, &g_quadVBO);

    glBindVertexArray(g_quadVAO);
    glBindBuffer(GL_ARRAY_BUFFER, g_quadVBO);
    glBufferData(GL_ARRAY_BUFFER, sizeof(v), v, GL_STATIC_DRAW);

    glEnableVertexAttribArray(0);
    glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), (void*)0);
    glEnableVertexAttribArray(1);
    glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), (void*)(2 * sizeof(float)));

    glBindBuffer(GL_ARRAY_BUFFER, 0);
    glBindVertexArray(0);
}

static void UploadBoardToTexture() {
    if (!g_boardTex) {
        glGenTextures(1, &g_boardTex);
        glBindTexture(GL_TEXTURE_2D, g_boardTex);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
        glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
        glTexImage2D(GL_TEXTURE_2D, 0, GL_R8I, 8, 8, 0, GL_RED_INTEGER, GL_BYTE, g_board);
    }
    else {
        glBindTexture(GL_TEXTURE_2D, g_boardTex);
        glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
        glTexSubImage2D(GL_TEXTURE_2D, 0, 0, 0, 8, 8, GL_RED_INTEGER, GL_BYTE, g_board);
    }
    glBindTexture(GL_TEXTURE_2D, 0);
    g_boardTextureDirty = false;
}

static void MarkBoardDirty() { g_boardTextureDirty = true; }
static void EnsureBoardUploaded() {
    if (g_boardTextureDirty || !g_boardTex) UploadBoardToTexture();
}

static void InitVisualizationFBO() {
    glGenTextures(1, &g_visTex);
    glBindTexture(GL_TEXTURE_2D, g_visTex);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA8, 8, 8, 0, GL_RGBA, GL_UNSIGNED_BYTE, nullptr);

    glGenTextures(1, &g_visMaskTex);
    glBindTexture(GL_TEXTURE_2D, g_visMaskTex);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_R8UI, 8, 8, 0, GL_RED_INTEGER, GL_UNSIGNED_BYTE, nullptr);

    glGenFramebuffers(1, &g_visFbo);
    glBindFramebuffer(GL_FRAMEBUFFER, g_visFbo);
    glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, g_visTex, 0);
    glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT1, GL_TEXTURE_2D, g_visMaskTex, 0);
    const GLenum bufs[2] = { GL_COLOR_ATTACHMENT0, GL_COLOR_ATTACHMENT1 };
    glDrawBuffers(2, bufs);

    if (glCheckFramebufferStatus(GL_FRAMEBUFFER) != GL_FRAMEBUFFER_COMPLETE) {
        Fatal("Visualization FBO incomplete.");
    }

    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    glBindTexture(GL_TEXTURE_2D, 0);
}

// ============================================================
// Visualization shaders (OpenGL 4.3 context, GLSL 430)
// ============================================================
static const char* kQuadVS = R"GLSL(
#version 430 core
layout(location=0) in vec2 aPos;
layout(location=1) in vec2 aUV;
out vec2 vUV;
void main() {
    vUV = aUV;
    gl_Position = vec4(aPos, 0.0, 1.0);
}
)GLSL";

static const char* kVisFS = R"GLSL(
#version 430 core
uniform isampler2D uBoard;
uniform int uFromSq;
uniform int uSideToMove;
uniform int uCastling;
uniform int uEpSq;
uniform int uWhiteKingSq;
uniform int uBlackKingSq;

layout(location=0) out vec4 FragColor;
layout(location=1) out uvec4 MaskOut;

int sideOf(int p){ return (p>0)?1:((p<0)?-1:0); }
int absP(int p){ return (p<0)?-p:p; }
ivec2 sqToXY(int sq){ return ivec2(sq & 7, sq >> 3); }
int xyToSq(ivec2 p){ return (p.y<<3) | p.x; }
bool inBoard(ivec2 p){ return p.x>=0 && p.x<8 && p.y>=0 && p.y<8; }

int pieceAt(int sq){
    if(sq<0 || sq>=64) return 0;
    return texelFetch(uBoard, sqToXY(sq), 0).r;
}

int pieceAtAny(int sq, int mvFrom, int mvTo){
    if(mvFrom < 0) return pieceAt(sq);

    int moving = pieceAt(mvFrom);
    int side = sideOf(moving);
    ivec2 a = sqToXY(mvFrom);
    ivec2 b = sqToXY(mvTo);

    if(absP(moving)==1){
        int dir = (side==1)?1:-1;
        if(mvTo==uEpSq && b.x!=a.x && pieceAt(mvTo)==0){
            int capSq = xyToSq(ivec2(b.x, b.y-dir));
            if(sq==capSq) return 0;
        }
    }

    if(absP(moving)==6 && a.y==b.y && abs(b.x-a.x)==2){
        int rookFrom=-1, rookTo=-1;
        if(side==1  && mvFrom==4  && mvTo==6 ){ rookFrom=7;  rookTo=5;  }
        if(side==1  && mvFrom==4  && mvTo==2 ){ rookFrom=0;  rookTo=3;  }
        if(side==-1 && mvFrom==60 && mvTo==62){ rookFrom=63; rookTo=61; }
        if(side==-1 && mvFrom==60 && mvTo==58){ rookFrom=56; rookTo=59; }
        if(rookFrom>=0){
            if(sq==rookFrom) return 0;
            if(sq==rookTo) return 4*side;
        }
    }

    if(sq==mvFrom) return 0;
    if(sq==mvTo) return moving;
    return pieceAt(sq);
}

bool rayClearAny(int fromSq, int toSq, ivec2 step, int mvFrom, int mvTo){
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq), p=a+step;
    while(p.x!=b.x || p.y!=b.y){
        if(pieceAtAny(xyToSq(p), mvFrom, mvTo)!=0) return false;
        p+=step;
    }
    return true;
}

bool squareAttackedAny(int targetSq, int bySide, int mvFrom, int mvTo){
    ivec2 t=sqToXY(targetSq);

    int py=t.y-bySide;
    if(py>=0 && py<8){
        ivec2 p1=ivec2(t.x-1,py), p2=ivec2(t.x+1,py);
        if(inBoard(p1) && pieceAtAny(xyToSq(p1),mvFrom,mvTo)==bySide) return true;
        if(inBoard(p2) && pieceAtAny(xyToSq(p2),mvFrom,mvTo)==bySide) return true;
    }

    const ivec2 KN[8]=ivec2[8](
        ivec2(1,2),ivec2(2,1),ivec2(2,-1),ivec2(1,-2),
        ivec2(-1,-2),ivec2(-2,-1),ivec2(-2,1),ivec2(-1,2));
    for(int i=0;i<8;i++){
        ivec2 p=t+KN[i];
        if(inBoard(p) && pieceAtAny(xyToSq(p),mvFrom,mvTo)==2*bySide) return true;
    }

    for(int dy=-1;dy<=1;dy++) for(int dx=-1;dx<=1;dx++){
        if(dx==0 && dy==0) continue;
        ivec2 p=t+ivec2(dx,dy);
        if(inBoard(p) && pieceAtAny(xyToSq(p),mvFrom,mvTo)==6*bySide) return true;
    }

    const ivec2 DIAG[4]=ivec2[4](ivec2(1,1),ivec2(1,-1),ivec2(-1,1),ivec2(-1,-1));
    for(int i=0;i<4;i++){
        ivec2 p=t+DIAG[i];
        while(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(pc!=0){
                if(sideOf(pc)==bySide){ int ap=absP(pc); if(ap==3 || ap==5) return true; }
                break;
            }
            p+=DIAG[i];
        }
    }

    const ivec2 ORTH[4]=ivec2[4](ivec2(1,0),ivec2(-1,0),ivec2(0,1),ivec2(0,-1));
    for(int i=0;i<4;i++){
        ivec2 p=t+ORTH[i];
        while(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(pc!=0){
                if(sideOf(pc)==bySide){ int ap=absP(pc); if(ap==4 || ap==5) return true; }
                break;
            }
            p+=ORTH[i];
        }
    }
    return false;
}

int kingSqAny(int side, int mvFrom, int mvTo){
    int baseSq=(side==1)?uWhiteKingSq:uBlackKingSq;
    if(mvFrom>=0 && pieceAt(mvFrom)==6*side) return mvTo;
    return baseSq;
}

bool kingInCheckAny(int side, int mvFrom, int mvTo){
    int ksq=kingSqAny(side,mvFrom,mvTo);
    return (ksq<0) ? true : squareAttackedAny(ksq,-side,mvFrom,mvTo);
}

bool pseudoLegal(int fromSq, int toSq){
    if(fromSq<0 || fromSq>=64 || toSq<0 || toSq>=64 || fromSq==toSq) return false;
    int p=pieceAt(fromSq);
    if(p==0) return false;
    int side=sideOf(p);
    if(side!=uSideToMove) return false;
    int t=pieceAt(toSq);
    if(t!=0 && sideOf(t)==side) return false;
    if(t!=0 && absP(t)==6) return false;

    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);
    int dx=b.x-a.x, dy=b.y-a.y, ap=absP(p);

    if(ap==2){ int ax=abs(dx), ay=abs(dy); return (ax==1&&ay==2)||(ax==2&&ay==1); }
    if(ap==3){
        if(abs(dx)!=abs(dy)) return false;
        return rayClearAny(fromSq,toSq,ivec2((dx>0)?1:-1,(dy>0)?1:-1),-1,-1);
    }
    if(ap==4){
        if(dx!=0 && dy!=0) return false;
        ivec2 st=ivec2((dx>0)?1:((dx<0)?-1:0),(dy>0)?1:((dy<0)?-1:0));
        return rayClearAny(fromSq,toSq,st,-1,-1);
    }
    if(ap==5){
        bool diag=abs(dx)==abs(dy), line=(dx==0||dy==0);
        if(!diag && !line) return false;
        ivec2 st=ivec2((dx>0)?1:((dx<0)?-1:0),(dy>0)?1:((dy<0)?-1:0));
        return rayClearAny(fromSq,toSq,st,-1,-1);
    }
    if(ap==6){
        if(abs(dx)<=1 && abs(dy)<=1) return true;
        if(dy==0 && abs(dx)==2){
            if(side==1 && fromSq!=4) return false;
            if(side==-1 && fromSq!=60) return false;
            if(side==1 && !(toSq==2||toSq==6)) return false;
            if(side==-1 && !(toSq==58||toSq==62)) return false;
            if(side==1 && toSq==6){
                if((uCastling&1)==0 || pieceAt(7)!=4 || pieceAt(5)!=0 || pieceAt(6)!=0) return false;
                return true;
            }
            if(side==1 && toSq==2){
                if((uCastling&2)==0 || pieceAt(0)!=4 || pieceAt(1)!=0 || pieceAt(2)!=0 || pieceAt(3)!=0) return false;
                return true;
            }
            if(side==-1 && toSq==62){
                if((uCastling&4)==0 || pieceAt(63)!=-4 || pieceAt(61)!=0 || pieceAt(62)!=0) return false;
                return true;
            }
            if(side==-1 && toSq==58){
                if((uCastling&8)==0 || pieceAt(56)!=-4 || pieceAt(57)!=0 || pieceAt(58)!=0 || pieceAt(59)!=0) return false;
                return true;
            }
        }
        return false;
    }
    if(ap==1){
        int dir=(side==1)?1:-1;
        int startRank=(side==1)?1:6;
        if(abs(dx)==1 && dy==dir){
            if(t!=0 && sideOf(t)==-side) return true;
            if(uEpSq>=0 && toSq==uEpSq && t==0){
                ivec2 cap=ivec2(b.x,b.y-dir);
                if(inBoard(cap) && pieceAt(xyToSq(cap))==-side) return true;
            }
            return false;
        }
        if(dx==0){
            if(t!=0) return false;
            if(dy==dir) return true;
            if(a.y==startRank && dy==2*dir){
                return pieceAt(xyToSq(ivec2(a.x,a.y+dir)))==0;
            }
        }
        return false;
    }
    return false;
}

bool legalMove(int fromSq, int toSq){
    if(!pseudoLegal(fromSq,toSq)) return false;
    int moving=pieceAt(fromSq), side=sideOf(moving);
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);

    if(absP(moving)==6 && a.y==b.y && abs(b.x-a.x)==2){
        if(kingInCheckAny(side,-1,-1)) return false;
        int midSq=-1;
        if(side==1 && fromSq==4 && toSq==6) midSq=5;
        if(side==1 && fromSq==4 && toSq==2) midSq=3;
        if(side==-1 && fromSq==60 && toSq==62) midSq=61;
        if(side==-1 && fromSq==60 && toSq==58) midSq=59;
        if(midSq>=0){
            if(squareAttackedAny(midSq,-side,-1,-1)) return false;
            if(squareAttackedAny(toSq,-side,-1,-1)) return false;
        }
    }
    return !kingInCheckAny(side,fromSq,toSq);
}

vec3 pieceColor(int p){
    int s=sideOf(p), ap=absP(p);
    vec3 c=(ap==1)?vec3(0.35,0.55,0.95):
           (ap==2)?vec3(0.55,0.35,0.95):
           (ap==3)?vec3(0.35,0.95,0.55):
           (ap==4)?vec3(0.95,0.55,0.35):
           (ap==5)?vec3(0.95,0.35,0.55):vec3(0.95,0.95,0.35);
    return (s==1)?mix(c,vec3(1.0),0.25):mix(c,vec3(0.0),0.35);
}

void main(){
    ivec2 cell=ivec2(gl_FragCoord.xy);
    int toSq=cell.y*8+cell.x;

    if(uFromSq==-2){
        uint v=kingInCheckAny(uSideToMove,-1,-1)?1u:0u;
        MaskOut=uvec4(v,0u,0u,0u);
        FragColor=vec4(float(v),0.0,0.0,1.0);
        return;
    }

    bool dark=((cell.x+cell.y)&1)==1;
    vec3 base=dark?vec3(0.20,0.22,0.25):vec3(0.82,0.83,0.85);
    base=(uSideToMove==1)?mix(base,vec3(0.90,0.90,1.0),0.06):mix(base,vec3(1.0,0.90,0.90),0.06);
    int pc=pieceAt(toSq);
    vec3 col=base;
    if(pc!=0) col=mix(col,pieceColor(pc),0.55);

    uint ok=0u;
    if(uFromSq>=0 && uFromSq<64 && legalMove(uFromSq,toSq)) ok=1u;
    MaskOut=uvec4(ok,0u,0u,0u);
    if(ok==1u) col=mix(col,vec3(0.15,0.85,0.25),0.65);
    if(toSq==uFromSq) col=mix(col,vec3(0.95,0.85,0.15),0.75);
    FragColor=vec4(col,1.0);
}
)GLSL";

static const char* kBlitFS = R"GLSL(
#version 430 core
in vec2 vUV;
uniform sampler2D uVis;
out vec4 FragColor;
void main(){ FragColor=texture(uVis,vUV); }
)GLSL";

// ============================================================
// Expansion compute shader: one 32-lane workgroup (one NVIDIA warp) per position.
// Each lane handles two from-squares: lid and lid+32. Each from-square scans 64 targets.
// A workgroup uses one atomicAdd to reserve all of its children in the output frontier.
// ============================================================
static const char* kExpandCSPart1 = R"GLSL(
#version 430 core
layout(local_size_x=32, local_size_y=1, local_size_z=1) in;

struct Position {
    uint board[8];
    uint meta;
};

layout(std430, binding=0) readonly buffer InputPositions {
    Position inPos[];
};
layout(std430, binding=1) writeonly buffer OutputPositions {
    Position outPos[];
};
layout(std430, binding=2) buffer CounterBuffer {
    uint outCount;
    uint overflow;
    uint leafLo;
    uint leafHi;
};

uniform uint uBasePosition;
uniform uint uPositionCount;
uniform uint uOutputCapacity;
uniform int  uCountOnly;

shared uint sBoard[8];
shared uint sMeta;
shared int  sSide;
shared int  sCastling;
shared int  sEpSq;
shared int  sWhiteKingSq;
shared int  sBlackKingSq;
shared uint sCounts32[32];
shared uint sOffsets32[32];
shared uint sBaseOut;
shared uint sTotalOut;

int sideOfPiece(int p){
    if(p==0) return 0;
    return (p<=6)?1:-1;
}
int absPiece(int p){
    if(p==0) return 0;
    return (p<=6)?p:(p-6);
}
int encodePiece(int side, int ap){ return (side==1)?ap:(ap+6); }

int pieceAt(int sq){
    if(sq<0 || sq>=64) return 0;

    // NVIDIA's GLSL linker can emit C1068 for dynamically indexing
    // a shared array here even though sq is range-checked above.
    // Select a statically indexed word instead.
    int wi = sq >> 3;
    uint w = 0u;
    switch(wi){
        case 0: w = sBoard[0]; break;
        case 1: w = sBoard[1]; break;
        case 2: w = sBoard[2]; break;
        case 3: w = sBoard[3]; break;
        case 4: w = sBoard[4]; break;
        case 5: w = sBoard[5]; break;
        case 6: w = sBoard[6]; break;
        default: w = sBoard[7]; break;
    }

    uint sh=uint((sq&7)*4);
    return int((w>>sh)&15u);
}

ivec2 sqToXY(int sq){ return ivec2(sq&7,sq>>3); }
int xyToSq(ivec2 p){ return (p.y<<3)|p.x; }
bool inBoard(ivec2 p){ return p.x>=0 && p.x<8 && p.y>=0 && p.y<8; }

int pieceAtAny(int sq, int mvFrom, int mvTo){
    if(mvFrom<0) return pieceAt(sq);

    int moving=pieceAt(mvFrom);
    int side=sideOfPiece(moving);
    ivec2 a=sqToXY(mvFrom), b=sqToXY(mvTo);

    if(absPiece(moving)==1){
        int dir=(side==1)?1:-1;
        if(mvTo==sEpSq && b.x!=a.x && pieceAt(mvTo)==0){
            int capSq=xyToSq(ivec2(b.x,b.y-dir));
            if(sq==capSq) return 0;
        }
    }

    if(absPiece(moving)==6 && a.y==b.y && abs(b.x-a.x)==2){
        int rookFrom=-1, rookTo=-1;
        if(side==1  && mvFrom==4  && mvTo==6 ){ rookFrom=7; rookTo=5; }
        if(side==1  && mvFrom==4  && mvTo==2 ){ rookFrom=0; rookTo=3; }
        if(side==-1 && mvFrom==60 && mvTo==62){ rookFrom=63; rookTo=61; }
        if(side==-1 && mvFrom==60 && mvTo==58){ rookFrom=56; rookTo=59; }
        if(rookFrom>=0){
            if(sq==rookFrom) return 0;
            if(sq==rookTo) return encodePiece(side,4);
        }
    }

    if(sq==mvFrom) return 0;
    if(sq==mvTo) return moving;
    return pieceAt(sq);
}

bool rayClearAny(int fromSq, int toSq, ivec2 step, int mvFrom, int mvTo){
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq), p=a+step;
    while(p.x!=b.x || p.y!=b.y){
        if(pieceAtAny(xyToSq(p),mvFrom,mvTo)!=0) return false;
        p+=step;
    }
    return true;
}

bool squareAttackedAny(int targetSq, int bySide, int mvFrom, int mvTo){
    ivec2 t=sqToXY(targetSq);

    int py=t.y-bySide;
    if(py>=0 && py<8){
        ivec2 p1=ivec2(t.x-1,py), p2=ivec2(t.x+1,py);
        if(inBoard(p1)){
            int pc=pieceAtAny(xyToSq(p1),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==1) return true;
        }
        if(inBoard(p2)){
            int pc=pieceAtAny(xyToSq(p2),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==1) return true;
        }
    }

    const ivec2 KN[8]=ivec2[8](
        ivec2(1,2),ivec2(2,1),ivec2(2,-1),ivec2(1,-2),
        ivec2(-1,-2),ivec2(-2,-1),ivec2(-2,1),ivec2(-1,2));
    for(int i=0;i<8;i++){
        ivec2 p=t+KN[i];
        if(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==2) return true;
        }
    }

    for(int dy=-1;dy<=1;dy++) for(int dx=-1;dx<=1;dx++){
        if(dx==0 && dy==0) continue;
        ivec2 p=t+ivec2(dx,dy);
        if(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==6) return true;
        }
    }

    const ivec2 DIAG[4]=ivec2[4](ivec2(1,1),ivec2(1,-1),ivec2(-1,1),ivec2(-1,-1));
    for(int i=0;i<4;i++){
        ivec2 p=t+DIAG[i];
        while(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(pc!=0){
                if(sideOfPiece(pc)==bySide){
                    int ap=absPiece(pc);
                    if(ap==3 || ap==5) return true;
                }
                break;
            }
            p+=DIAG[i];
        }
    }

    const ivec2 ORTH[4]=ivec2[4](ivec2(1,0),ivec2(-1,0),ivec2(0,1),ivec2(0,-1));
    for(int i=0;i<4;i++){
        ivec2 p=t+ORTH[i];
        while(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(pc!=0){
                if(sideOfPiece(pc)==bySide){
                    int ap=absPiece(pc);
                    if(ap==4 || ap==5) return true;
                }
                break;
            }
            p+=ORTH[i];
        }
    }
    return false;
}

int kingSqAny(int side, int mvFrom, int mvTo){
    int baseSq=(side==1)?sWhiteKingSq:sBlackKingSq;
    if(mvFrom>=0){
        int moving=pieceAt(mvFrom);
        if(sideOfPiece(moving)==side && absPiece(moving)==6) return mvTo;
    }
    return baseSq;
}

bool kingInCheckAny(int side, int mvFrom, int mvTo){
    int ksq=kingSqAny(side,mvFrom,mvTo);
    return (ksq<0)?true:squareAttackedAny(ksq,-side,mvFrom,mvTo);
}

)GLSL";

static const char* kExpandCSPart2 = R"GLSL(bool pseudoLegal(int fromSq, int toSq){
    if(fromSq<0 || fromSq>=64 || toSq<0 || toSq>=64 || fromSq==toSq) return false;
    int p=pieceAt(fromSq);
    if(p==0 || sideOfPiece(p)!=sSide) return false;
    int t=pieceAt(toSq);
    if(t!=0 && sideOfPiece(t)==sSide) return false;
    if(t!=0 && absPiece(t)==6) return false;

    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);
    int dx=b.x-a.x, dy=b.y-a.y, ap=absPiece(p);

    if(ap==2){ int ax=abs(dx), ay=abs(dy); return (ax==1&&ay==2)||(ax==2&&ay==1); }
    if(ap==3){
        if(abs(dx)!=abs(dy)) return false;
        return rayClearAny(fromSq,toSq,ivec2((dx>0)?1:-1,(dy>0)?1:-1),-1,-1);
    }
    if(ap==4){
        if(dx!=0 && dy!=0) return false;
        ivec2 st=ivec2((dx>0)?1:((dx<0)?-1:0),(dy>0)?1:((dy<0)?-1:0));
        return rayClearAny(fromSq,toSq,st,-1,-1);
    }
    if(ap==5){
        bool diag=abs(dx)==abs(dy), line=(dx==0||dy==0);
        if(!diag && !line) return false;
        ivec2 st=ivec2((dx>0)?1:((dx<0)?-1:0),(dy>0)?1:((dy<0)?-1:0));
        return rayClearAny(fromSq,toSq,st,-1,-1);
    }
    if(ap==6){
        if(abs(dx)<=1 && abs(dy)<=1) return true;
        if(dy==0 && abs(dx)==2){
            if(sSide==1 && fromSq!=4) return false;
            if(sSide==-1 && fromSq!=60) return false;
            if(sSide==1 && !(toSq==2||toSq==6)) return false;
            if(sSide==-1 && !(toSq==58||toSq==62)) return false;
            if(sSide==1 && toSq==6){
                int r=pieceAt(7);
                if((sCastling&1)==0 || sideOfPiece(r)!=1 || absPiece(r)!=4 || pieceAt(5)!=0 || pieceAt(6)!=0) return false;
                return true;
            }
            if(sSide==1 && toSq==2){
                int r=pieceAt(0);
                if((sCastling&2)==0 || sideOfPiece(r)!=1 || absPiece(r)!=4 || pieceAt(1)!=0 || pieceAt(2)!=0 || pieceAt(3)!=0) return false;
                return true;
            }
            if(sSide==-1 && toSq==62){
                int r=pieceAt(63);
                if((sCastling&4)==0 || sideOfPiece(r)!=-1 || absPiece(r)!=4 || pieceAt(61)!=0 || pieceAt(62)!=0) return false;
                return true;
            }
            if(sSide==-1 && toSq==58){
                int r=pieceAt(56);
                if((sCastling&8)==0 || sideOfPiece(r)!=-1 || absPiece(r)!=4 || pieceAt(57)!=0 || pieceAt(58)!=0 || pieceAt(59)!=0) return false;
                return true;
            }
        }
        return false;
    }
    if(ap==1){
        int dir=(sSide==1)?1:-1;
        int startRank=(sSide==1)?1:6;
        if(abs(dx)==1 && dy==dir){
            if(t!=0 && sideOfPiece(t)==-sSide) return true;
            if(sEpSq>=0 && toSq==sEpSq && t==0){
                ivec2 cap=ivec2(b.x,b.y-dir);
                if(inBoard(cap)){
                    int pc=pieceAt(xyToSq(cap));
                    if(sideOfPiece(pc)==-sSide && absPiece(pc)==1) return true;
                }
            }
            return false;
        }
        if(dx==0){
            if(t!=0) return false;
            if(dy==dir) return true;
            if(a.y==startRank && dy==2*dir){
                return pieceAt(xyToSq(ivec2(a.x,a.y+dir)))==0;
            }
        }
        return false;
    }
    return false;
}

bool legalMove(int fromSq, int toSq){
    if(!pseudoLegal(fromSq,toSq)) return false;
    int moving=pieceAt(fromSq), side=sideOfPiece(moving);
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);

    if(absPiece(moving)==6 && a.y==b.y && abs(b.x-a.x)==2){
        if(kingInCheckAny(side,-1,-1)) return false;
        int midSq=-1;
        if(side==1 && fromSq==4 && toSq==6) midSq=5;
        if(side==1 && fromSq==4 && toSq==2) midSq=3;
        if(side==-1 && fromSq==60 && toSq==62) midSq=61;
        if(side==-1 && fromSq==60 && toSq==58) midSq=59;
        if(midSq>=0){
            if(squareAttackedAny(midSq,-side,-1,-1)) return false;
            if(squareAttackedAny(toSq,-side,-1,-1)) return false;
        }
    }
    return !kingInCheckAny(side,fromSq,toSq);
}

uint packMeta(int side, int castling, int epSq, int wk, int bk){
    uint sideBit=(side==-1)?1u:0u;
    uint epCode=(epSq<0)?0u:uint(epSq+1);
    return sideBit |
           (uint(castling&15)<<1u) |
           ((epCode&127u)<<5u) |
           ((uint(wk)&63u)<<12u) |
           ((uint(bk)&63u)<<18u);
}

void setPiece(inout Position p, int sq, int piece){
    if(sq<0 || sq>=64) return;

    int wi=sq>>3;
    uint sh=uint((sq&7)*4);
    uint mask=15u<<sh;
    uint bits=(uint(piece)&15u)<<sh;

    // Keep all Position.board accesses statically indexed as well.
    switch(wi){
        case 0: p.board[0]=(p.board[0]&~mask)|bits; break;
        case 1: p.board[1]=(p.board[1]&~mask)|bits; break;
        case 2: p.board[2]=(p.board[2]&~mask)|bits; break;
        case 3: p.board[3]=(p.board[3]&~mask)|bits; break;
        case 4: p.board[4]=(p.board[4]&~mask)|bits; break;
        case 5: p.board[5]=(p.board[5]&~mask)|bits; break;
        case 6: p.board[6]=(p.board[6]&~mask)|bits; break;
        default: p.board[7]=(p.board[7]&~mask)|bits; break;
    }
}

bool isPromotionMove(int fromSq, int toSq){
    int moving=pieceAt(fromSq);
    if(absPiece(moving)!=1) return false;
    int rank=toSq>>3;
    return (sSide==1)?(rank==7):(rank==0);
}

void writeChild(uint dst, int fromSq, int toSq, int promotionAbs){
    if(dst>=uOutputCapacity) return;

    Position c;
    c.board[0]=sBoard[0];
    c.board[1]=sBoard[1];
    c.board[2]=sBoard[2];
    c.board[3]=sBoard[3];
    c.board[4]=sBoard[4];
    c.board[5]=sBoard[5];
    c.board[6]=sBoard[6];
    c.board[7]=sBoard[7];

    int moving=pieceAt(fromSq);
    int captured=pieceAt(toSq);
    int side=sideOfPiece(moving);
    int ap=absPiece(moving);
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);

    int castling=sCastling;
    int epSq=-1;
    int wk=sWhiteKingSq;
    int bk=sBlackKingSq;

    if(ap==6){
        if(side==1) castling&=~3;
        else castling&=~12;
    }
    if(ap==4){
        if(side==1){
            if(fromSq==7) castling&=~1;
            if(fromSq==0) castling&=~2;
        }else{
            if(fromSq==63) castling&=~4;
            if(fromSq==56) castling&=~8;
        }
    }
    if(captured!=0 && absPiece(captured)==4){
        int cs=sideOfPiece(captured);
        if(cs==1){
            if(toSq==7) castling&=~1;
            if(toSq==0) castling&=~2;
        }else{
            if(toSq==63) castling&=~4;
            if(toSq==56) castling&=~8;
        }
    }

    // en passant capture
    if(ap==1 && toSq==sEpSq && captured==0 && a.x!=b.x){
        int dir=(side==1)?1:-1;
        int capSq=toSq-dir*8;
        if(capSq>=0 && capSq<64) setPiece(c,capSq,0);
    }

    // castling rook relocation
    if(ap==6 && a.y==b.y && abs(b.x-a.x)==2){
        if(side==1 && fromSq==4 && toSq==6){ setPiece(c,7,0); setPiece(c,5,encodePiece(1,4)); }
        if(side==1 && fromSq==4 && toSq==2){ setPiece(c,0,0); setPiece(c,3,encodePiece(1,4)); }
        if(side==-1 && fromSq==60 && toSq==62){ setPiece(c,63,0); setPiece(c,61,encodePiece(-1,4)); }
        if(side==-1 && fromSq==60 && toSq==58){ setPiece(c,56,0); setPiece(c,59,encodePiece(-1,4)); }
    }

    setPiece(c,fromSq,0);
    int placed=moving;
    if(promotionAbs>=2 && promotionAbs<=5) placed=encodePiece(side,promotionAbs);
    setPiece(c,toSq,placed);

    if(ap==1 && a.x==b.x && abs(b.y-a.y)==2){
        int dir=(side==1)?1:-1;
        epSq=fromSq+dir*8;
    }

    if(ap==6){
        if(side==1) wk=toSq;
        else bk=toSq;
    }

    c.meta=packMeta(-side,castling,epSq,wk,bk);

    outPos[dst].board[0]=c.board[0];
    outPos[dst].board[1]=c.board[1];
    outPos[dst].board[2]=c.board[2];
    outPos[dst].board[3]=c.board[3];
    outPos[dst].board[4]=c.board[4];
    outPos[dst].board[5]=c.board[5];
    outPos[dst].board[6]=c.board[6];
    outPos[dst].board[7]=c.board[7];
    outPos[dst].meta=c.meta;
}

void addLeafCount(uint n){
    if(n==0u) return;
    uint old=atomicAdd(leafLo,n);
    if(old > 0xffffffffu - n) atomicAdd(leafHi,1u);
}

void buildMaskForFrom(int fromSq, out uint maskLo, out uint maskHi, out uint childCount){
    maskLo=0u;
    maskHi=0u;
    childCount=0u;

    int moving=pieceAt(fromSq);
    if(moving==0 || sideOfPiece(moving)!=sSide) return;

    for(int toSq=0;toSq<64;toSq++){
        if(!legalMove(fromSq,toSq)) continue;
        if(toSq<32) maskLo|=(1u<<uint(toSq));
        else maskHi|=(1u<<uint(toSq-32));
        childCount += isPromotionMove(fromSq,toSq) ? 4u : 1u;
    }
}

void emitMask(inout uint dst, int fromSq, uint maskLo, uint maskHi){
    uint m=maskLo;
    while(m!=0u){
        int bit=findLSB(m);
        int toSq=bit;
        m&=(m-1u);
        if(isPromotionMove(fromSq,toSq)){
            writeChild(dst++,fromSq,toSq,2);
            writeChild(dst++,fromSq,toSq,3);
            writeChild(dst++,fromSq,toSq,4);
            writeChild(dst++,fromSq,toSq,5);
        }else{
            writeChild(dst++,fromSq,toSq,0);
        }
    }

    m=maskHi;
    while(m!=0u){
        int bit=findLSB(m);
        int toSq=bit+32;
        m&=(m-1u);
        if(isPromotionMove(fromSq,toSq)){
            writeChild(dst++,fromSq,toSq,2);
            writeChild(dst++,fromSq,toSq,3);
            writeChild(dst++,fromSq,toSq,4);
            writeChild(dst++,fromSq,toSq,5);
        }else{
            writeChild(dst++,fromSq,toSq,0);
        }
    }
}

void main(){
    uint lid=gl_LocalInvocationID.x;
    uint posIndex=uBasePosition+gl_WorkGroupID.x;
    if(posIndex>=uPositionCount) return;

    if(lid==0u){
        // Static indexes avoid NVIDIA C1068 during link-time optimization.
        sBoard[0]=inPos[posIndex].board[0];
        sBoard[1]=inPos[posIndex].board[1];
        sBoard[2]=inPos[posIndex].board[2];
        sBoard[3]=inPos[posIndex].board[3];
        sBoard[4]=inPos[posIndex].board[4];
        sBoard[5]=inPos[posIndex].board[5];
        sBoard[6]=inPos[posIndex].board[6];
        sBoard[7]=inPos[posIndex].board[7];
        sMeta=inPos[posIndex].meta;
        sSide=((sMeta&1u)!=0u)?-1:1;
        sCastling=int((sMeta>>1u)&15u);
        uint epCode=(sMeta>>5u)&127u;
        sEpSq=(epCode==0u)?-1:int(epCode-1u);
        sWhiteKingSq=int((sMeta>>12u)&63u);
        sBlackKingSq=int((sMeta>>18u)&63u);
    }
    barrier();

    // One warp covers all 64 origin squares as two halves.
    int fromA=int(lid);
    int fromB=fromA+32;

    uint maskLoA, maskHiA, countA;
    uint maskLoB, maskHiB, countB;
    buildMaskForFrom(fromA,maskLoA,maskHiA,countA);
    buildMaskForFrom(fromB,maskLoB,maskHiB,countB);

    uint laneCount=countA+countB;
    sCounts32[lid]=laneCount;
    barrier();

    if(lid==0u){
        uint sum=0u;
        for(uint i=0u;i<32u;i++){
            sOffsets32[i]=sum;
            sum+=sCounts32[i];
        }
        sTotalOut=sum;

        if(uCountOnly!=0){
            addLeafCount(sum);
            sBaseOut=0u;
        }else{
            uint base=atomicAdd(outCount,sum);
            sBaseOut=base;
            if(base>=uOutputCapacity || sum>uOutputCapacity-base){
                atomicExchange(overflow,1u);
            }
        }
    }
    barrier();

    if(uCountOnly!=0) return;

    uint dst=sBaseOut+sOffsets32[lid];
    emitMask(dst,fromA,maskLoA,maskHiA);
    emitMask(dst,fromB,maskLoB,maskHiB);
}
)GLSL";

// Dedicated final-ply counter: smaller shader, one 32-lane NVIDIA warp per position.
static const char* kCountCS = R"GLSL(
#version 430 core
layout(local_size_x=32, local_size_y=1, local_size_z=1) in;

struct Position {
    uint board[8];
    uint meta;
};

layout(std430, binding=0) readonly buffer InputPositions {
    Position inPos[];
};
layout(std430, binding=2) buffer CounterBuffer {
    uint outCount;
    uint overflow;
    uint leafLo;
    uint leafHi;
};

uniform uint uBasePosition;
uniform uint uPositionCount;

shared uint sBoard[8];
shared uint sMeta;
shared int  sSide;
shared int  sCastling;
shared int  sEpSq;
shared int  sWhiteKingSq;
shared int  sBlackKingSq;
shared uint sCounts32[32];

int sideOfPiece(int p){
    if(p==0) return 0;
    return (p<=6)?1:-1;
}
int absPiece(int p){
    if(p==0) return 0;
    return (p<=6)?p:(p-6);
}
int encodePiece(int side, int ap){ return (side==1)?ap:(ap+6); }

int pieceAt(int sq){
    if(sq<0 || sq>=64) return 0;

    // NVIDIA's GLSL linker can emit C1068 for dynamically indexing
    // a shared array here even though sq is range-checked above.
    // Select a statically indexed word instead.
    int wi = sq >> 3;
    uint w = 0u;
    switch(wi){
        case 0: w = sBoard[0]; break;
        case 1: w = sBoard[1]; break;
        case 2: w = sBoard[2]; break;
        case 3: w = sBoard[3]; break;
        case 4: w = sBoard[4]; break;
        case 5: w = sBoard[5]; break;
        case 6: w = sBoard[6]; break;
        default: w = sBoard[7]; break;
    }

    uint sh=uint((sq&7)*4);
    return int((w>>sh)&15u);
}

ivec2 sqToXY(int sq){ return ivec2(sq&7,sq>>3); }
int xyToSq(ivec2 p){ return (p.y<<3)|p.x; }
bool inBoard(ivec2 p){ return p.x>=0 && p.x<8 && p.y>=0 && p.y<8; }

int pieceAtAny(int sq, int mvFrom, int mvTo){
    if(mvFrom<0) return pieceAt(sq);

    int moving=pieceAt(mvFrom);
    int side=sideOfPiece(moving);
    ivec2 a=sqToXY(mvFrom), b=sqToXY(mvTo);

    if(absPiece(moving)==1){
        int dir=(side==1)?1:-1;
        if(mvTo==sEpSq && b.x!=a.x && pieceAt(mvTo)==0){
            int capSq=xyToSq(ivec2(b.x,b.y-dir));
            if(sq==capSq) return 0;
        }
    }

    if(absPiece(moving)==6 && a.y==b.y && abs(b.x-a.x)==2){
        int rookFrom=-1, rookTo=-1;
        if(side==1  && mvFrom==4  && mvTo==6 ){ rookFrom=7; rookTo=5; }
        if(side==1  && mvFrom==4  && mvTo==2 ){ rookFrom=0; rookTo=3; }
        if(side==-1 && mvFrom==60 && mvTo==62){ rookFrom=63; rookTo=61; }
        if(side==-1 && mvFrom==60 && mvTo==58){ rookFrom=56; rookTo=59; }
        if(rookFrom>=0){
            if(sq==rookFrom) return 0;
            if(sq==rookTo) return encodePiece(side,4);
        }
    }

    if(sq==mvFrom) return 0;
    if(sq==mvTo) return moving;
    return pieceAt(sq);
}

bool rayClearAny(int fromSq, int toSq, ivec2 step, int mvFrom, int mvTo){
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq), p=a+step;
    while(p.x!=b.x || p.y!=b.y){
        if(pieceAtAny(xyToSq(p),mvFrom,mvTo)!=0) return false;
        p+=step;
    }
    return true;
}

bool squareAttackedAny(int targetSq, int bySide, int mvFrom, int mvTo){
    ivec2 t=sqToXY(targetSq);

    int py=t.y-bySide;
    if(py>=0 && py<8){
        ivec2 p1=ivec2(t.x-1,py), p2=ivec2(t.x+1,py);
        if(inBoard(p1)){
            int pc=pieceAtAny(xyToSq(p1),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==1) return true;
        }
        if(inBoard(p2)){
            int pc=pieceAtAny(xyToSq(p2),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==1) return true;
        }
    }

    const ivec2 KN[8]=ivec2[8](
        ivec2(1,2),ivec2(2,1),ivec2(2,-1),ivec2(1,-2),
        ivec2(-1,-2),ivec2(-2,-1),ivec2(-2,1),ivec2(-1,2));
    for(int i=0;i<8;i++){
        ivec2 p=t+KN[i];
        if(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==2) return true;
        }
    }

    for(int dy=-1;dy<=1;dy++) for(int dx=-1;dx<=1;dx++){
        if(dx==0 && dy==0) continue;
        ivec2 p=t+ivec2(dx,dy);
        if(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(sideOfPiece(pc)==bySide && absPiece(pc)==6) return true;
        }
    }

    const ivec2 DIAG[4]=ivec2[4](ivec2(1,1),ivec2(1,-1),ivec2(-1,1),ivec2(-1,-1));
    for(int i=0;i<4;i++){
        ivec2 p=t+DIAG[i];
        while(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(pc!=0){
                if(sideOfPiece(pc)==bySide){
                    int ap=absPiece(pc);
                    if(ap==3 || ap==5) return true;
                }
                break;
            }
            p+=DIAG[i];
        }
    }

    const ivec2 ORTH[4]=ivec2[4](ivec2(1,0),ivec2(-1,0),ivec2(0,1),ivec2(0,-1));
    for(int i=0;i<4;i++){
        ivec2 p=t+ORTH[i];
        while(inBoard(p)){
            int pc=pieceAtAny(xyToSq(p),mvFrom,mvTo);
            if(pc!=0){
                if(sideOfPiece(pc)==bySide){
                    int ap=absPiece(pc);
                    if(ap==4 || ap==5) return true;
                }
                break;
            }
            p+=ORTH[i];
        }
    }
    return false;
}

int kingSqAny(int side, int mvFrom, int mvTo){
    int baseSq=(side==1)?sWhiteKingSq:sBlackKingSq;
    if(mvFrom>=0){
        int moving=pieceAt(mvFrom);
        if(sideOfPiece(moving)==side && absPiece(moving)==6) return mvTo;
    }
    return baseSq;
}

bool kingInCheckAny(int side, int mvFrom, int mvTo){
    int ksq=kingSqAny(side,mvFrom,mvTo);
    return (ksq<0)?true:squareAttackedAny(ksq,-side,mvFrom,mvTo);
}

bool pseudoLegal(int fromSq, int toSq){
    if(fromSq<0 || fromSq>=64 || toSq<0 || toSq>=64 || fromSq==toSq) return false;
    int p=pieceAt(fromSq);
    if(p==0 || sideOfPiece(p)!=sSide) return false;
    int t=pieceAt(toSq);
    if(t!=0 && sideOfPiece(t)==sSide) return false;
    if(t!=0 && absPiece(t)==6) return false;

    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);
    int dx=b.x-a.x, dy=b.y-a.y, ap=absPiece(p);

    if(ap==2){ int ax=abs(dx), ay=abs(dy); return (ax==1&&ay==2)||(ax==2&&ay==1); }
    if(ap==3){
        if(abs(dx)!=abs(dy)) return false;
        return rayClearAny(fromSq,toSq,ivec2((dx>0)?1:-1,(dy>0)?1:-1),-1,-1);
    }
    if(ap==4){
        if(dx!=0 && dy!=0) return false;
        ivec2 st=ivec2((dx>0)?1:((dx<0)?-1:0),(dy>0)?1:((dy<0)?-1:0));
        return rayClearAny(fromSq,toSq,st,-1,-1);
    }
    if(ap==5){
        bool diag=abs(dx)==abs(dy), line=(dx==0||dy==0);
        if(!diag && !line) return false;
        ivec2 st=ivec2((dx>0)?1:((dx<0)?-1:0),(dy>0)?1:((dy<0)?-1:0));
        return rayClearAny(fromSq,toSq,st,-1,-1);
    }
    if(ap==6){
        if(abs(dx)<=1 && abs(dy)<=1) return true;
        if(dy==0 && abs(dx)==2){
            if(sSide==1 && fromSq!=4) return false;
            if(sSide==-1 && fromSq!=60) return false;
            if(sSide==1 && !(toSq==2||toSq==6)) return false;
            if(sSide==-1 && !(toSq==58||toSq==62)) return false;
            if(sSide==1 && toSq==6){
                int r=pieceAt(7);
                if((sCastling&1)==0 || sideOfPiece(r)!=1 || absPiece(r)!=4 || pieceAt(5)!=0 || pieceAt(6)!=0) return false;
                return true;
            }
            if(sSide==1 && toSq==2){
                int r=pieceAt(0);
                if((sCastling&2)==0 || sideOfPiece(r)!=1 || absPiece(r)!=4 || pieceAt(1)!=0 || pieceAt(2)!=0 || pieceAt(3)!=0) return false;
                return true;
            }
            if(sSide==-1 && toSq==62){
                int r=pieceAt(63);
                if((sCastling&4)==0 || sideOfPiece(r)!=-1 || absPiece(r)!=4 || pieceAt(61)!=0 || pieceAt(62)!=0) return false;
                return true;
            }
            if(sSide==-1 && toSq==58){
                int r=pieceAt(56);
                if((sCastling&8)==0 || sideOfPiece(r)!=-1 || absPiece(r)!=4 || pieceAt(57)!=0 || pieceAt(58)!=0 || pieceAt(59)!=0) return false;
                return true;
            }
        }
        return false;
    }
    if(ap==1){
        int dir=(sSide==1)?1:-1;
        int startRank=(sSide==1)?1:6;
        if(abs(dx)==1 && dy==dir){
            if(t!=0 && sideOfPiece(t)==-sSide) return true;
            if(sEpSq>=0 && toSq==sEpSq && t==0){
                ivec2 cap=ivec2(b.x,b.y-dir);
                if(inBoard(cap)){
                    int pc=pieceAt(xyToSq(cap));
                    if(sideOfPiece(pc)==-sSide && absPiece(pc)==1) return true;
                }
            }
            return false;
        }
        if(dx==0){
            if(t!=0) return false;
            if(dy==dir) return true;
            if(a.y==startRank && dy==2*dir){
                return pieceAt(xyToSq(ivec2(a.x,a.y+dir)))==0;
            }
        }
        return false;
    }
    return false;
}

bool legalMove(int fromSq, int toSq){
    if(!pseudoLegal(fromSq,toSq)) return false;
    int moving=pieceAt(fromSq), side=sideOfPiece(moving);
    ivec2 a=sqToXY(fromSq), b=sqToXY(toSq);

    if(absPiece(moving)==6 && a.y==b.y && abs(b.x-a.x)==2){
        if(kingInCheckAny(side,-1,-1)) return false;
        int midSq=-1;
        if(side==1 && fromSq==4 && toSq==6) midSq=5;
        if(side==1 && fromSq==4 && toSq==2) midSq=3;
        if(side==-1 && fromSq==60 && toSq==62) midSq=61;
        if(side==-1 && fromSq==60 && toSq==58) midSq=59;
        if(midSq>=0){
            if(squareAttackedAny(midSq,-side,-1,-1)) return false;
            if(squareAttackedAny(toSq,-side,-1,-1)) return false;
        }
    }
    return !kingInCheckAny(side,fromSq,toSq);
}


bool isPromotionMoveCount(int fromSq, int toSq){
    int moving=pieceAt(fromSq);
    if(absPiece(moving)!=1) return false;
    int rank=toSq>>3;
    return (sSide==1)?(rank==7):(rank==0);
}

uint countFromSquare(int fromSq){
    int moving=pieceAt(fromSq);
    if(moving==0 || sideOfPiece(moving)!=sSide) return 0u;

    uint n=0u;
    for(int toSq=0; toSq<64; ++toSq){
        if(legalMove(fromSq,toSq)){
            n += isPromotionMoveCount(fromSq,toSq) ? 4u : 1u;
        }
    }
    return n;
}

void addLeafCount32(uint n){
    if(n==0u) return;
    uint old=atomicAdd(leafLo,n);
    if(old > 0xffffffffu - n) atomicAdd(leafHi,1u);
}

void main(){
    uint lid=gl_LocalInvocationID.x;
    uint posIndex=uBasePosition+gl_WorkGroupID.x;
    if(posIndex>=uPositionCount) return;

    if(lid==0u){
        sBoard[0]=inPos[posIndex].board[0];
        sBoard[1]=inPos[posIndex].board[1];
        sBoard[2]=inPos[posIndex].board[2];
        sBoard[3]=inPos[posIndex].board[3];
        sBoard[4]=inPos[posIndex].board[4];
        sBoard[5]=inPos[posIndex].board[5];
        sBoard[6]=inPos[posIndex].board[6];
        sBoard[7]=inPos[posIndex].board[7];
        sMeta=inPos[posIndex].meta;
        sSide=((sMeta&1u)!=0u)?-1:1;
        sCastling=int((sMeta>>1u)&15u);
        uint epCode=(sMeta>>5u)&127u;
        sEpSq=(epCode==0u)?-1:int(epCode-1u);
        sWhiteKingSq=int((sMeta>>12u)&63u);
        sBlackKingSq=int((sMeta>>18u)&63u);
    }
    barrier();

    // One NVIDIA-sized warp handles all 64 from-squares as two 32-square halves.
    uint localCount=countFromSquare(int(lid));
    localCount+=countFromSquare(int(lid)+32);
    sCounts32[lid]=localCount;
    barrier();

    if(lid==0u){
        uint sum=0u;
        for(uint i=0u;i<32u;++i) sum+=sCounts32[i];
        addLeafCount32(sum);
    }
}
)GLSL";

static void InitShaders() {
    PrintConsoleLine("[SHADER] build visualization program...");
    g_visProg = BuildGraphicsProgram(kQuadVS, kVisFS);

    PrintConsoleLine("[SHADER] build blit program...");
    g_blitProg = BuildGraphicsProgram(kQuadVS, kBlitFS);

    // Both search kernels now use 32-lane workgroups (one NVIDIA-sized warp).
    // Expansion keeps the proven legal-move logic and only changes work distribution.
    // Final count remains a separate small shader to avoid giant-kernel driver issues.
    PrintConsoleLine("[SHADER] build 32-lane frontier expansion kernel...");
    {
        const char* parts[] = { kExpandCSPart1, kExpandCSPart2 };
        g_expandProg = BuildComputeProgramParts(parts, 2);
    }
    PrintConsoleLine("[SHADER] 32-lane expansion kernel ready.");

    PrintConsoleLine("[SHADER] build 32-lane final-count kernel...");
    g_countProg = BuildComputeProgram(kCountCS);
    PrintConsoleLine("[SHADER] final-count kernel ready.");

    glUseProgram(g_visProg);
    g_visLocBoard = glGetUniformLocation(g_visProg, "uBoard");
    g_visLocFrom = glGetUniformLocation(g_visProg, "uFromSq");
    g_visLocSide = glGetUniformLocation(g_visProg, "uSideToMove");
    g_visLocCastling = glGetUniformLocation(g_visProg, "uCastling");
    g_visLocEp = glGetUniformLocation(g_visProg, "uEpSq");
    g_visLocWhiteKing = glGetUniformLocation(g_visProg, "uWhiteKingSq");
    g_visLocBlackKing = glGetUniformLocation(g_visProg, "uBlackKingSq");
    glUniform1i(g_visLocBoard, 0);

    glUseProgram(g_blitProg);
    g_blitLocVis = glGetUniformLocation(g_blitProg, "uVis");
    glUniform1i(g_blitLocVis, 0);

    glUseProgram(g_expandProg);
    g_expandLocBasePosition = glGetUniformLocation(g_expandProg, "uBasePosition");
    g_expandLocPositionCount = glGetUniformLocation(g_expandProg, "uPositionCount");
    g_expandLocOutputCapacity = glGetUniformLocation(g_expandProg, "uOutputCapacity");
    g_expandLocCountOnly = glGetUniformLocation(g_expandProg, "uCountOnly");

    glUseProgram(g_countProg);
    g_countLocBasePosition = glGetUniformLocation(g_countProg, "uBasePosition");
    g_countLocPositionCount = glGetUniformLocation(g_countProg, "uPositionCount");

    glUseProgram(0);
}

// ============================================================
// Compute buffers / packing
// ============================================================
static uint32_t EncodePieceCPU(int p) {
    if (p == 0) return 0;
    return (p > 0) ? (uint32_t)p : (uint32_t)(6 + (-p));
}

static uint32_t PackMetaCPU(int side, int castling, int epSq, int wk, int bk) {
    uint32_t sideBit = (side == -1) ? 1u : 0u;
    uint32_t epCode = (epSq < 0) ? 0u : (uint32_t)(epSq + 1);
    return sideBit |
        ((uint32_t)(castling & 15) << 1u) |
        ((epCode & 127u) << 5u) |
        (((uint32_t)wk & 63u) << 12u) |
        (((uint32_t)bk & 63u) << 18u);
}

static GpuPosition MakeGpuRootPosition() {
    GpuPosition p{};
    for (int sq = 0; sq < 64; ++sq) {
        uint32_t ep = EncodePieceCPU((int)g_board[sq]);
        int wi = sq >> 3;
        int sh = (sq & 7) * 4;
        p.board[wi] |= (ep & 15u) << sh;
    }
    int wk = FindKingSqCPU(1);
    int bk = FindKingSqCPU(-1);
    if (wk < 0 || bk < 0) Fatal("Cannot start GPU search: missing king.");
    p.meta = PackMetaCPU(g_sideToMove, g_castling, g_epSq, wk, bk);
    return p;
}

static uint64_t BufferBytesForCapacity(uint64_t cap) {
    if (cap > (std::numeric_limits<uint64_t>::max() / sizeof(GpuPosition))) {
        Fatal("SSBO capacity overflow.");
    }
    return cap * sizeof(GpuPosition);
}

static void AllocateFrontierBuffer(int index, uint64_t capacity) {
    if (capacity < 1) capacity = 1;
    if (capacity > (uint64_t)std::numeric_limits<GLsizeiptr>::max() / sizeof(GpuPosition)) {
        Fatal("Requested SSBO is too large for GLsizeiptr.");
    }

    if (!g_frontierSSBO[index]) glGenBuffers(1, &g_frontierSSBO[index]);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, g_frontierSSBO[index]);

    // Clear a stale GL error before allocation so OOM reporting is meaningful.
    while (glGetError() != GL_NO_ERROR) {}

    GLsizeiptr bytes = (GLsizeiptr)(capacity * sizeof(GpuPosition));
    glBufferData(GL_SHADER_STORAGE_BUFFER, bytes, nullptr, GL_DYNAMIC_COPY);
    GLenum e = glGetError();
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, 0);

    if (e != GL_NO_ERROR) {
        std::ostringstream oss;
        oss << "Failed to allocate frontier SSBO: " << (unsigned long long)bytes
            << " bytes (OpenGL error 0x" << std::hex << (unsigned)e << ").";
        Fatal(oss.str().c_str());
    }
    g_frontierCapacity[index] = capacity;
}

static void EnsureFrontierCapacity(int index, uint64_t needed) {
    if (needed <= g_frontierCapacity[index]) return;
    AllocateFrontierBuffer(index, needed);
}

static void InitComputeBuffers() {
    glGenBuffers(1, &g_frontierSSBO[0]);
    glGenBuffers(1, &g_frontierSSBO[1]);
    g_frontierCapacity[0] = 0;
    g_frontierCapacity[1] = 0;
    AllocateFrontierBuffer(0, 1);
    AllocateFrontierBuffer(1, 1024);

    glGenBuffers(1, &g_counterSSBO);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, g_counterSSBO);
    GpuCounters zero{};
    glBufferData(GL_SHADER_STORAGE_BUFFER, sizeof(zero), &zero, GL_DYNAMIC_COPY);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, 0);
}

static void ResetGpuCounters() {
    GpuCounters zero{};
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, g_counterSSBO);
    glBufferSubData(GL_SHADER_STORAGE_BUFFER, 0, sizeof(zero), &zero);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, 0);
}

static GpuCounters ReadGpuCounters() {
    GpuCounters c{};
    glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT | GL_BUFFER_UPDATE_BARRIER_BIT);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, g_counterSSBO);
    glGetBufferSubData(GL_SHADER_STORAGE_BUFFER, 0, sizeof(c), &c);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, 0);
    return c;
}

static void UploadRootToBuffer(int index) {
    GpuPosition root = MakeGpuRootPosition();
    EnsureFrontierCapacity(index, 1);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, g_frontierSSBO[index]);
    glBufferSubData(GL_SHADER_STORAGE_BUFFER, 0, sizeof(root), &root);
    glBindBuffer(GL_SHADER_STORAGE_BUFFER, 0);
}

static void DispatchExpandPass(
    int inIndex,
    int outIndex,
    uint64_t positionCount,
    uint64_t outputCapacity,
    SearchStats& stats)
{
    if (positionCount == 0) return;
    if (positionCount > 0xffffffffull) Fatal("Frontier position count exceeds 32-bit shader indexing.");
    if (outputCapacity > 0xffffffffull) Fatal("Output capacity exceeds 32-bit shader indexing.");

    glUseProgram(g_expandProg);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, g_frontierSSBO[inIndex]);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, g_frontierSSBO[outIndex]);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 2, g_counterSSBO);

    glUniform1ui(g_expandLocPositionCount, (GLuint)positionCount);
    glUniform1ui(g_expandLocOutputCapacity, (GLuint)outputCapacity);
    // The expansion shader is the already-proven stable kernel. It still has
    // this uniform, but expansion always uses false.
    glUniform1i(g_expandLocCountOnly, 0);

    uint64_t base = 0;
    while (base < positionCount) {
        uint64_t remain = positionCount - base;
        GLuint groups = (GLuint)std::min<uint64_t>(remain, g_maxDispatchGroupsX);
        glUniform1ui(g_expandLocBasePosition, (GLuint)base);
        glDispatchCompute(groups, 1, 1);
        stats.computeDispatches++;
        base += groups;
    }

    glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, 0);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, 0);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 2, 0);
    glUseProgram(0);
}

static void DispatchCountPass(
    int inIndex,
    uint64_t positionCount,
    SearchStats& stats)
{
    if (positionCount == 0) return;
    if (positionCount > 0xffffffffull) Fatal("Frontier position count exceeds 32-bit shader indexing.");

    glUseProgram(g_countProg);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, g_frontierSSBO[inIndex]);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 2, g_counterSSBO);
    glUniform1ui(g_countLocPositionCount, (GLuint)positionCount);

    uint64_t base = 0;
    while (base < positionCount) {
        uint64_t remain = positionCount - base;
        GLuint groups = (GLuint)std::min<uint64_t>(remain, g_maxDispatchGroupsX);
        glUniform1ui(g_countLocBasePosition, (GLuint)base);
        glDispatchCompute(groups, 1, 1);
        stats.computeDispatches++;
        base += groups;
    }

    glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, 0);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 2, 0);
    glUseProgram(0);
}

static uint64_t CurrentAllocatedFrontierBytes() {
    return BufferBytesForCapacity(g_frontierCapacity[0]) + BufferBytesForCapacity(g_frontierCapacity[1]);
}

static uint64_t ExpandFrontierGpu(
    int inIndex,
    int outIndex,
    uint64_t currentCount,
    uint64_t suggestedCapacity,
    SearchStats& stats)
{
    uint64_t cap = std::max<uint64_t>(suggestedCapacity, 1);

    for (;;) {
        if (cap > 0xffffffffull) Fatal("Required frontier is too large for this implementation.");
        EnsureFrontierCapacity(outIndex, cap);
        stats.peakAllocatedBytes = std::max(stats.peakAllocatedBytes, CurrentAllocatedFrontierBytes());

        ResetGpuCounters();
        DispatchExpandPass(inIndex, outIndex, currentCount, cap, stats);
        GpuCounters c = ReadGpuCounters();

        uint64_t actual = c.outCount;
        if (c.overflow == 0 && actual <= cap) {
            stats.generatedPositions += actual;
            stats.peakFrontier = std::max(stats.peakFrontier, actual);
            return actual;
        }

        stats.retryPasses++;
        uint64_t newCap = std::max<uint64_t>(actual, cap * 2ull);
        if (newCap <= cap) Fatal("Frontier capacity growth overflow.");

        std::ostringstream oss;
        oss << "[SEARCH] frontier overflow: capacity=" << (unsigned long long)cap
            << " actual=" << (unsigned long long)actual
            << " -> realloc=" << (unsigned long long)newCap;
        PrintConsoleLine(oss.str());
        cap = newCap;
    }
}

static uint64_t CountFinalLayerGpu(int inIndex, uint64_t currentCount, SearchStats& stats) {
    ResetGpuCounters();
    DispatchCountPass(inIndex, currentCount, stats);
    GpuCounters c = ReadGpuCounters();
    return (uint64_t)c.leafLo | ((uint64_t)c.leafHi << 32ull);
}

// ============================================================
// GPU frontier perft
// ============================================================
static void RunSearchBenchmark(int depth) {
    if (depth < 1) depth = 1;
    if (depth > kMaxGpuFrontierDepth) {
        std::ostringstream oss;
        oss << "[SEARCH] full-frontier mode clamps depth to " << kMaxGpuFrontierDepth
            << " because deeper searches materialize enormous intermediate frontiers.";
        PrintConsoleLine(oss.str());
        depth = kMaxGpuFrontierDepth;
    }

    char startBuf[256];
    std::snprintf(
        startBuf,
        sizeof(startBuf),
        "[SEARCH] start depth=%d | GL4.3 SSBO frontier + 32-lane expand/count ...",
        depth
    );
    PrintConsoleLine(startBuf);
    UpdateTitleStatus(startBuf);

    SearchStats stats{};
    auto t0 = std::chrono::high_resolution_clock::now();

    int inIndex = 0;
    int outIndex = 1;
    UploadRootToBuffer(inIndex);

    uint64_t currentCount = 1;
    stats.peakFrontier = 1;
    stats.peakAllocatedBytes = CurrentAllocatedFrontierBytes();

    uint64_t nodes = 0;

    if (depth == 1) {
        nodes = CountFinalLayerGpu(inIndex, currentCount, stats);
    }
    else {
        // Materialize levels 1..depth-1. The final ply is counted directly on GPU.
        for (int ply = 1; ply < depth; ++ply) {
            bool nextIsFinalInput = (ply == depth - 1);

            uint64_t suggested = 0;
            if (currentCount > 0xffffffffull / kInitialBranchCapacityFactor) {
                suggested = 0xffffffffull;
            }
            else {
                suggested = std::max<uint64_t>(1024, currentCount * kInitialBranchCapacityFactor);
            }

            stats.expandedFrontierPositions += currentCount;
            uint64_t nextCount = ExpandFrontierGpu(
                inIndex,
                outIndex,
                currentCount,
                suggested,
                stats
            );

            {
                std::ostringstream oss;
                oss << "[SEARCH] ply " << ply
                    << " frontier: " << (unsigned long long)currentCount
                    << " -> " << (unsigned long long)nextCount;
                PrintConsoleLine(oss.str());
            }

            std::swap(inIndex, outIndex);
            currentCount = nextCount;

            if (currentCount == 0) {
                nodes = 0;
                break;
            }

            if (nextIsFinalInput) {
                stats.expandedFrontierPositions += currentCount;
                nodes = CountFinalLayerGpu(inIndex, currentCount, stats);
            }
        }
    }

    glFinish();
    auto t1 = std::chrono::high_resolution_clock::now();

    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
    double sec = ms / 1000.0;
    double nps = (sec > 0.0) ? ((double)nodes / sec) : 0.0;
    double frontierPerSec = (sec > 0.0) ? ((double)stats.expandedFrontierPositions / sec) : 0.0;
    double peakMB = (double)stats.peakAllocatedBytes / (1024.0 * 1024.0);

    char result[768];
    std::snprintf(
        result,
        sizeof(result),
        "[SEARCH] depth=%d nodes=%llu time=%.3f ms nps=%.0f dispatches=%llu expanded_positions=%llu expanded/s=%.0f generated_frontier=%llu retries=%llu peak_frontier=%llu peak_ssbo=%.1f MiB",
        depth,
        (unsigned long long)nodes,
        ms,
        nps,
        (unsigned long long)stats.computeDispatches,
        (unsigned long long)stats.expandedFrontierPositions,
        frontierPerSec,
        (unsigned long long)stats.generatedPositions,
        (unsigned long long)stats.retryPasses,
        (unsigned long long)stats.peakFrontier,
        peakMB
    );
    PrintConsoleLine(result);

    char title[256];
    std::snprintf(
        title,
        sizeof(title),
        "COMPUTE d=%d nodes=%llu time=%.1fms nps=%.0f",
        depth,
        (unsigned long long)nodes,
        ms,
        nps
    );
    UpdateTitleStatus(title);
}

// ============================================================
// CPU game setup / move application
// ============================================================
static void ResetGame() {
    std::fill(std::begin(g_board), std::end(g_board), 0);

    const int8_t wBack[8] = { 4,2,3,5,6,3,2,4 };
    const int8_t bBack[8] = { -4,-2,-3,-5,-6,-3,-2,-4 };
    for (int x = 0; x < 8; ++x) {
        g_board[sqOf(x, 0)] = wBack[x];
        g_board[sqOf(x, 1)] = 1;
        g_board[sqOf(x, 6)] = -1;
        g_board[sqOf(x, 7)] = bBack[x];
    }

    g_sideToMove = 1;
    g_castling = 15;
    g_epSq = -1;
    g_fromSq = -1;
    g_gameOver = false;
    MarkBoardDirty();
    EnsureBoardUploaded();
    UpdateTitleStatus("");
}

static void UpdateCastlingRightsOnMove(int from, int to, int8_t moving, int8_t capturedBeforeMove) {
    int s = sideOf(moving);
    int ap = absP(moving);

    if (ap == 6) {
        if (s == 1) g_castling &= ~3;
        else        g_castling &= ~12;
    }
    if (ap == 4) {
        if (s == 1) {
            if (from == 7) g_castling &= ~1;
            if (from == 0) g_castling &= ~2;
        }
        else {
            if (from == 63) g_castling &= ~4;
            if (from == 56) g_castling &= ~8;
        }
    }
    if (absP(capturedBeforeMove) == 4) {
        int cs = sideOf(capturedBeforeMove);
        if (cs == 1) {
            if (to == 7) g_castling &= ~1;
            if (to == 0) g_castling &= ~2;
        }
        else if (cs == -1) {
            if (to == 63) g_castling &= ~4;
            if (to == 56) g_castling &= ~8;
        }
    }
}

static void ApplyMoveCPU(int from, int to) {
    int8_t moving = g_board[from];
    int8_t captured = g_board[to];
    int s = sideOf(moving);
    int ap = absP(moving);
    int fx = sqX(from), fy = sqY(from);
    int tx = sqX(to), ty = sqY(to);

    int oldEp = g_epSq;
    g_epSq = -1;
    UpdateCastlingRightsOnMove(from, to, moving, captured);

    if (ap == 1 && to == oldEp && captured == 0 && std::abs(tx - fx) == 1) {
        int dir = (s == 1) ? 1 : -1;
        int capSq = to - dir * 8;
        if (capSq >= 0 && capSq < 64) g_board[capSq] = 0;
    }

    if (ap == 6 && fy == ty && std::abs(tx - fx) == 2) {
        if (s == 1 && from == 4 && to == 6) { g_board[7] = 0; g_board[5] = 4; }
        if (s == 1 && from == 4 && to == 2) { g_board[0] = 0; g_board[3] = 4; }
        if (s == -1 && from == 60 && to == 62) { g_board[63] = 0; g_board[61] = -4; }
        if (s == -1 && from == 60 && to == 58) { g_board[56] = 0; g_board[59] = -4; }
    }

    g_board[to] = moving;
    g_board[from] = 0;

    if (ap == 1 && fx == tx && std::abs(ty - fy) == 2) {
        int dir = (s == 1) ? 1 : -1;
        g_epSq = from + dir * 8;
    }

    // Interactive GUI keeps the original behavior: auto-promote to queen.
    if (ap == 1 && ((s == 1 && ty == 7) || (s == -1 && ty == 0))) {
        g_board[to] = (int8_t)(5 * s);
    }

    g_sideToMove = -g_sideToMove;
    MarkBoardDirty();
    EnsureBoardUploaded();
}

// ============================================================
// Visualization legality / game-state queries
// ============================================================
static void RenderVisToFBO(int fromSq, int side) {
    EnsureBoardUploaded();

    glBindFramebuffer(GL_FRAMEBUFFER, g_visFbo);
    glViewport(0, 0, 8, 8);
    glUseProgram(g_visProg);
    glActiveTexture(GL_TEXTURE0);
    glBindTexture(GL_TEXTURE_2D, g_boardTex);

    glUniform1i(g_visLocFrom, fromSq);
    glUniform1i(g_visLocSide, side);
    glUniform1i(g_visLocCastling, g_castling);
    glUniform1i(g_visLocEp, g_epSq);
    glUniform1i(g_visLocWhiteKing, FindKingSqCPU(1));
    glUniform1i(g_visLocBlackKing, FindKingSqCPU(-1));

    glBindVertexArray(g_quadVAO);
    glDrawArrays(GL_TRIANGLES, 0, 6);
    glBindVertexArray(0);

    glBindTexture(GL_TEXTURE_2D, 0);
    glUseProgram(0);
}

static uint8_t ReadVisMaskAt(int sq) {
    uint8_t v = 0;
    glBindFramebuffer(GL_FRAMEBUFFER, g_visFbo);
    glReadBuffer(GL_COLOR_ATTACHMENT1);
    glPixelStorei(GL_PACK_ALIGNMENT, 1);
    glReadPixels(sqX(sq), sqY(sq), 1, 1, GL_RED_INTEGER, GL_UNSIGNED_BYTE, &v);
    glReadBuffer(GL_COLOR_ATTACHMENT0);
    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    return v;
}

static bool GPU_IsMoveLegal(int from, int to, int side) {
    RenderVisToFBO(from, side);
    return ReadVisMaskAt(to) != 0;
}

static bool GPU_IsKingInCheck(int side) {
    RenderVisToFBO(-2, side);
    return ReadVisMaskAt(0) != 0;
}

static bool GPU_HasAnyLegalMove(int side) {
    for (int from = 0; from < 64; ++from) {
        int p = g_board[from];
        if (p == 0 || sideOf(p) != side) continue;

        RenderVisToFBO(from, side);
        uint8_t row[64]{};
        glBindFramebuffer(GL_FRAMEBUFFER, g_visFbo);
        glReadBuffer(GL_COLOR_ATTACHMENT1);
        glPixelStorei(GL_PACK_ALIGNMENT, 1);
        glReadPixels(0, 0, 8, 8, GL_RED_INTEGER, GL_UNSIGNED_BYTE, row);
        glReadBuffer(GL_COLOR_ATTACHMENT0);
        glBindFramebuffer(GL_FRAMEBUFFER, 0);

        for (uint8_t v : row) if (v) return true;
    }
    return false;
}

static void EvaluateGameStateAndTitle() {
    bool inCheck = GPU_IsKingInCheck(g_sideToMove);
    bool hasMove = GPU_HasAnyLegalMove(g_sideToMove);

    if (!hasMove) {
        g_gameOver = true;
        UpdateTitleStatus(inCheck ? "CHECKMATE" : "STALEMATE");
    }
    else {
        UpdateTitleStatus(inCheck ? "CHECK" : "");
    }
}

static void HandleClickSquare(int sq) {
    if (sq == -999) {
        ResetGame();
        return;
    }
    if (g_gameOver || sq < 0 || sq >= 64) return;

    int8_t p = g_board[sq];
    if (g_fromSq < 0) {
        if (p != 0 && sideOf(p) == g_sideToMove) g_fromSq = sq;
        return;
    }
    if (sq == g_fromSq) {
        g_fromSq = -1;
        return;
    }
    if (p != 0 && sideOf(p) == g_sideToMove) {
        g_fromSq = sq;
        return;
    }

    if (GPU_IsMoveLegal(g_fromSq, sq, g_sideToMove)) {
        ApplyMoveCPU(g_fromSq, sq);
        g_fromSq = -1;
        EvaluateGameStateAndTitle();
    }
}

// ============================================================
// Rendering
// ============================================================
static void RenderFrame() {
    glDisable(GL_DEPTH_TEST);

    RenderVisToFBO(g_fromSq, g_sideToMove);
    glBindFramebuffer(GL_FRAMEBUFFER, 0);

    glViewport(0, 0, g_winW, g_winH);
    glClearColor(0.08f, 0.09f, 0.10f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glUseProgram(g_blitProg);
    glActiveTexture(GL_TEXTURE0);
    glBindTexture(GL_TEXTURE_2D, g_visTex);
    glBindVertexArray(g_quadVAO);
    glDrawArrays(GL_TRIANGLES, 0, 6);
    glBindVertexArray(0);
    glBindTexture(GL_TEXTURE_2D, 0);
    glUseProgram(0);

    SwapBuffers(g_hdc);
}

// ============================================================
// Console
// ============================================================
static void ConsoleThreadMain() {
    PrintConsoleLine("Commands:");
    PrintConsoleLine("  search N  : GPU-frontier perft/search, N half-moves (max 6)");
    PrintConsoleLine("  perft N   : same as search N");
    PrintConsoleLine("  help      : show help");
    PrintConsoleLine("  quit      : close program");
    PrintConsoleLine("Keyboard:");
    PrintConsoleLine("  B         : quick search 4");
    PrintConsoleLine("");

    std::string line;
    while (g_consoleRunning.load()) {
        if (!std::getline(std::cin, line)) {
            Sleep(10);
            continue;
        }

        std::istringstream iss(line);
        std::string cmd;
        iss >> cmd;
        std::transform(cmd.begin(), cmd.end(), cmd.begin(), [](unsigned char c) {
            return (char)std::tolower(c);
            });

        if (cmd.empty()) continue;

        if (cmd == "search" || cmd == "perft") {
            int depth = 0;
            iss >> depth;
            if (depth <= 0) {
                PrintConsoleLine("Usage: search 5");
                continue;
            }
            g_searchDepthRequest.store(depth);

            char buf[128];
            std::snprintf(buf, sizeof(buf), "[SEARCH] queued depth=%d", depth);
            PrintConsoleLine(buf);
        }
        else if (cmd == "help") {
            PrintConsoleLine("OpenGL 4.3 Compute + SSBO full-GPU-frontier search.");
            PrintConsoleLine("The final ply is counted on GPU without materializing its child frontier.");
            PrintConsoleLine("Depth is capped at 6 to avoid multi-GB intermediate frontiers.");
        }
        else if (cmd == "quit" || cmd == "exit") {
            g_running = false;
            if (g_hwnd) PostMessageA(g_hwnd, WM_CLOSE, 0, 0);
            break;
        }
        else {
            PrintConsoleLine("Unknown command. Type: help");
        }
    }
}

static void InitCommandConsole() {
    if (GetConsoleWindow() == nullptr) AllocConsole();

    FILE* fp = nullptr;
    freopen_s(&fp, "CONIN$", "r", stdin);
    freopen_s(&fp, "CONOUT$", "w", stdout);
    freopen_s(&fp, "CONOUT$", "w", stderr);

    g_consoleRunning.store(true);
    std::thread(ConsoleThreadMain).detach();
}

// ============================================================
// Cleanup
// ============================================================
static void Cleanup() {
    g_consoleRunning.store(false);

    if (g_expandProg) glDeleteProgram(g_expandProg);
    if (g_countProg) glDeleteProgram(g_countProg);
    if (g_visProg) glDeleteProgram(g_visProg);
    if (g_blitProg) glDeleteProgram(g_blitProg);

    if (g_frontierSSBO[0]) glDeleteBuffers(1, &g_frontierSSBO[0]);
    if (g_frontierSSBO[1]) glDeleteBuffers(1, &g_frontierSSBO[1]);
    if (g_counterSSBO) glDeleteBuffers(1, &g_counterSSBO);

    if (g_boardTex) glDeleteTextures(1, &g_boardTex);
    if (g_visTex) glDeleteTextures(1, &g_visTex);
    if (g_visMaskTex) glDeleteTextures(1, &g_visMaskTex);
    if (g_visFbo) glDeleteFramebuffers(1, &g_visFbo);

    if (g_quadVBO) glDeleteBuffers(1, &g_quadVBO);
    if (g_quadVAO) glDeleteVertexArrays(1, &g_quadVAO);

    if (g_glrc) {
        wglMakeCurrent(nullptr, nullptr);
        wglDeleteContext(g_glrc);
        g_glrc = nullptr;
    }
    if (g_hwnd && g_hdc) {
        ReleaseDC(g_hwnd, g_hdc);
        g_hdc = nullptr;
    }
    if (g_hwnd) {
        DestroyWindow(g_hwnd);
        g_hwnd = nullptr;
    }
}

// ============================================================
// Entry
// ============================================================
int main() {
    CreateWindowAndContext43();
    InitCommandConsole();

    InitQuad();
    InitVisualizationFBO();
    InitShaders();
    InitComputeBuffers();
    ResetGame();
    EvaluateGameStateAndTitle();

    MSG msg{};
    while (g_running) {
        while (PeekMessage(&msg, nullptr, 0, 0, PM_REMOVE)) {
            TranslateMessage(&msg);
            DispatchMessage(&msg);
        }

        if (g_hasPendingClick) {
            int sq = g_pendingSq;
            g_hasPendingClick = false;
            g_pendingSq = -1;
            HandleClickSquare(sq);
        }

        int depth = g_searchDepthRequest.exchange(0);
        if (depth > 0) RunSearchBenchmark(depth);

        RenderFrame();
        Sleep(1);
    }

    Cleanup();
    return 0;
}
