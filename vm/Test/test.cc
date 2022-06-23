#include <cstring>
#include <CppUTest/CommandLineTestRunner.h>

extern "C" {
#include "../Core/chunk.h"
#include "../Core/dumpChunk.h"
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

TEST_GROUP(Debug) {};

TEST(Debug, LineList) {
    Line line;
    line.lineNumber = 123;
    line.numInsts = 2;

    line.insts = (InstInfo*)malloc(2 * sizeof(InstInfo));

    line.insts[0].offset = 0;
    char inst1[11] = "CONSTANT 0";
    line.insts[0].content = inst1;

    line.insts[1].offset = 4;
    char inst2[11] = "CONSTANT 1";
    line.insts[1].content = inst2;

    LineList list;
    list.first = list.last = NULL;
    pushBackLineList(&list, &line);
    CHECK(list.first != NULL);
    CHECK(list.last != NULL);
    CHECK_EQUAL(*list.first, *list.last);
    CHECK_EQUAL((*list.first)->line.lineNumber, 123);

    appendInstruction(&list, 8, 123, "ADD");
    CHECK_EQUAL(*list.first, *list.last);
    CHECK_EQUAL((*list.first)->line.numInsts, 3);
    CHECK(strcmp((*list.first)->line.insts[2].content, "ADD") == 0);

    appendInstruction(&list, 10, 124, "RETURN");
    CHECK_EQUAL((*list.first)->next, *list.last);
    CHECK_EQUAL((*list.last)->line.lineNumber, 124);
    CHECK_EQUAL((*list.last)->line.numInsts, 1);
    CHECK(strcmp((*list.last)->line.insts[0].content, "RETURN") == 0);
}

int main(int argc, char* argv[]) {
    return CommandLineTestRunner::RunAllTests(argc, argv);
}
