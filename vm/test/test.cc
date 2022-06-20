#include <CppUTest/CommandLineTestRunner.h>

extern "C" {
#include "../Core/chunk.h"
}

TEST_GROUP(Chunk) {};

TEST(Chunk, GrowAndShrink) {
    Chunk chunk;
    initChunk(&chunk);
    CHECK_EQUAL(0, chunk.count);
    CHECK_EQUAL(0, chunk.capacity);
    CHECK_EQUAL(NULL, chunk.code);

    writeChunk(&chunk, 12, 1);
    CHECK_EQUAL(1, chunk.count);
    CHECK_EQUAL(8, chunk.capacity);
    CHECK_EQUAL(12, chunk.code[0]);

    for (int i = 1; i <= 7; i++) writeChunk(&chunk, 24, i + 1);
    CHECK_EQUAL(8, chunk.count);
    CHECK_EQUAL(8, chunk.capacity);

    writeChunk(&chunk, 48, 9);
    CHECK_EQUAL(9, chunk.count);
    CHECK_EQUAL(16, chunk.capacity);

    freeChunk(&chunk);
    CHECK_EQUAL(0, chunk.count);
    CHECK_EQUAL(0, chunk.capacity);
    CHECK_EQUAL(NULL, chunk.code);
}

int main(int argc, char* argv[]) {
    return CommandLineTestRunner::RunAllTests(argc, argv);
}
