#include <stdio.h>

#include "common.h"
#include "chunk.h"
#include "debug.h"
#include "vm.h"

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    initVM();

    Chunk chunk;
    initChunk(&chunk);

    int constantIndex = addConstant(&chunk, 1.2);
    writeChunk(&chunk, OP_CONSTANT, 123);
    writeChunk(&chunk, constantIndex, 123);
    writeChunk(&chunk, OP_RETURN, 123);

    disassembleChunk(&chunk, "test chunk");

    interpret(&chunk);

    freeVM();
    freeChunk(&chunk);

    return 0;
}
