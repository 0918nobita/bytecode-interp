#include "pch.h"

extern "C" {
#include "../VM/chunk.h"
#include "../VM/dumpChunk.h"
}

TEST(Chunk, GrowAndShrink) {
    Chunk chunk;
    initChunk(&chunk);
    ASSERT_EQ(0, chunk.count);
    ASSERT_EQ(0, chunk.capacity);
    ASSERT_EQ(NULL, chunk.code);

    writeChunk(&chunk, 12, 1);
    ASSERT_EQ(1, chunk.count);
    ASSERT_EQ(8, chunk.capacity);
    ASSERT_TRUE(chunk.code && chunk.code[0] == 12);

    for (int i = 1; i <= 7; i++) writeChunk(&chunk, 24, i + 1);
    ASSERT_EQ(8, chunk.count);
    ASSERT_EQ(8, chunk.capacity);

    writeChunk(&chunk, 48, 9);
    ASSERT_EQ(9, chunk.count);
    ASSERT_EQ(16, chunk.capacity);

    freeChunk(&chunk);
    ASSERT_EQ(0, chunk.count);
    ASSERT_EQ(0, chunk.capacity);
    ASSERT_EQ(NULL, chunk.code);
}

TEST(Debug, LineList) {
    Line line;
    line.lineNumber = 123;
    line.numInsts = 2;

    line.insts = (InstInfo*)malloc(2 * sizeof(InstInfo));

    line.insts[0].offset = 0;
    line.insts[0].content = strdup("CONSTANT 0");

    line.insts[1].offset = 4;
    line.insts[1].content = strdup("CONSTANT 1");

    LineList list;
    list.first = list.last = NULL;
    pushBackLineList(&list, &line);
    clearLine(&line);
    ASSERT_TRUE(list.first != NULL);
    ASSERT_TRUE(list.last != NULL);
    ASSERT_EQ(*list.first, *list.last);
    ASSERT_EQ(123, (*list.first)->line.lineNumber);

    appendInstruction(&list, 8, 123, "ADD");
    ASSERT_EQ(*list.first, *list.last);
    ASSERT_EQ(3, (*list.first)->line.numInsts);
    ASSERT_EQ(0, strcmp((*list.first)->line.insts[2].content, "ADD"));

    appendInstruction(&list, 10, 124, "RETURN");
    ASSERT_EQ(*list.last, (*list.first)->next);
    ASSERT_EQ(124, (*list.last)->line.lineNumber);
    ASSERT_EQ(1, (*list.last)->line.numInsts);
    ASSERT_EQ(0, strcmp((*list.last)->line.insts[0].content, "RETURN"));
    clearLineList(&list);
}
