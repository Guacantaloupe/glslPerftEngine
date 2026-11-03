GLSL Chess — GPU Frontier Perft (NVIDIA Compiler Workaround)
An experimental GPU-accelerated chess move-generation and Perft project written in C++ and GLSL 4.30, using OpenGL 4.3 compute shaders, shader storage buffer objects (SSBOs), and a native Win32 chessboard interface.
While attempting to implement a minimax search for my HCE (hand-crafted evaluation function), I decided to try using GLSL—only to run into a bug in the NVIDIA compiler. This code is a version that bypasses that bug.

The current  implementation is a GPU Perft / legal-move enumeration engine, not yet a complete HCE-based minimax chess engine. It explores legal move sequences and counts leaf nodes; it does not evaluate positions or choose the best move.
Background
The project began as an experiment in accelerating chess search with GPU compute shaders. During development, an NVIDIA GLSL compiler/linker issue could produce an C1068: array index out of bounds error, even where the shader performed range checks on accesses to a packed board array.

This version avoids the problematic dynamic indexing pattern by using constant-index switch cases when reading and writing the eight packed board words. It also avoids the earlier, very large piece-specific/fused shader design in favor of separate expansion and final-count compute kernels.

The workaround is implemented in the provided source; it should not be interpreted as proof that the underlying driver/compiler issue has been fixed. Behavior can vary by GPU and driver version.
What It Does
- Displays an interactive chessboard in a native Win32 window.
- Supports mouse-based move selection and uses GPU-rendered legality information for move interaction.
- Implements chess move generation and legality checks, including castling, en passant, promotion handling in search, and king-in-check checks.
- Encodes each search position into 36 bytes: eight 32-bit packed board words plus one 32-bit metadata word.
- Expands a frontier of chess positions using OpenGL compute shaders and SSBOs.
- Uses 32 compute invocations per workgroup to cooperatively process a position.
- Counts the final search ply directly on the GPU without storing all final child positions.
- Reports Perft node counts, elapsed time, nodes per second, dispatch counts, frontier sizes, retries, and peak allocated frontier memory.
Architecture
Current chess position (CPU)
             |
             v
   Pack into GpuPosition
   8 x uint32 board + meta
             |
             v
      Input frontier SSBO
             |
             v
    32-lane expansion kernel
    (legal move enumeration)
             |
             v
      Output frontier SSBO
             |
             +---- repeat for intermediate plies ----+
             |
             v
     32-lane final count kernel
             |
             v
      GPU leaf-node counter
             |
             v
       CPU statistics output
The expansion and final-count stages are separate GLSL compute programs. Intermediate levels are materialized in GPU buffers; the last level is counted without allocating a full final frontier. The program reads back small counters rather than transferring every position to the CPU.
Packed position format
struct GpuPosition {
    uint32_t board[8];
    uint32_t meta;
};
Each board word holds eight 4-bit piece codes, representing 64 squares in total. Metadata stores the side to move, castling rights, en passant square, and king-square information. The structure is 36 bytes, matching the GLSL std430 representation used by this project.
NVIDIA GLSL compiler workaround
A problematic pattern is dynamic indexing of a small packed array:
// Pattern avoided in this project:
uint word = sBoard[sq >> 3];
The code instead selects a constant-indexed element:
int wi = sq >> 3;
uint word = 0u;
switch (wi) {
    case 0: word = sBoard[0]; break;
    case 1: word = sBoard[1]; break;
    case 2: word = sBoard[2]; break;
    case 3: word = sBoard[3]; break;
    case 4: word = sBoard[4]; break;
    case 5: word = sBoard[5]; break;
    case 6: word = sBoard[6]; break;
    default: word = sBoard[7]; break;
}
The same constant-indexing approach is applied when modifying packed position data. The shader checks square bounds before reading the packed board
