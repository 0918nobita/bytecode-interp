#include <stdio.h>

#include "../Core/common.h"
#include "../Core/chunk.h"
#include "../Core/debug.h"
#include "../Core/vm.h"

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    initVM();

    Chunk chunk;
    initChunk(&chunk);

    int constantIndex = addConstant(&chunk, 1.2);
    writeChunk(&chunk, OP_CONSTANT, 123);
    writeChunk(&chunk, constantIndex, 123);

    constantIndex = addConstant(&chunk, 3.4);
    writeChunk(&chunk, OP_CONSTANT, 123);
    writeChunk(&chunk, constantIndex, 123);

    writeChunk(&chunk, OP_ADD, 123);

    constantIndex = addConstant(&chunk, 5.6);
    writeChunk(&chunk, OP_CONSTANT, 123);
    writeChunk(&chunk, constantIndex, 123);

    writeChunk(&chunk, OP_DIVIDE, 123);

    writeChunk(&chunk, OP_NEGATE, 123);

    writeChunk(&chunk, OP_RETURN, 123);

    dumpChunk(&chunk, "test chunk", "chunkInfo.html");

    interpret(&chunk);

    freeVM();
    freeChunk(&chunk);

    return 0;
}
