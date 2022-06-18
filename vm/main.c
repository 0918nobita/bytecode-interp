#include<stdio.h>

#include "common.h"
#include "chunk.h"
#include "debug.h"

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    Chunk chunk;
    initChunk(&chunk);
    writeChunk(&chunk, OP_RETURN);

    disassembleChunk(&chunk, "test chunk");
    freeChunk(&chunk);

    return 0;
}
