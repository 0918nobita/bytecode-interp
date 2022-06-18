#include<stdio.h>

#include "common.h"
#include "chunk.h"
#include "debug.h"

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    Chunk chunk;
    initChunk(&chunk);

    int constantIndex = addConstant(&chunk, 1.2);
    writeChunk(&chunk, OP_CONSTANT);
    writeChunk(&chunk, constantIndex);
    writeChunk(&chunk, OP_RETURN);

    disassembleChunk(&chunk, "test chunk");
    freeChunk(&chunk);

    return 0;
}
