#include <cstring>
#include <CppUTest/CommandLineTestRunner.h>

extern "C" {
#include "../Core/dumpChunk.h"
}

TEST_GROUP(Debug) {};

TEST(Debug, LineList) {
    Line line;
    line.lineNumber = 123;
    line.numInsts = 2;

    line.insts = (InstInfo*)malloc(2 * sizeof(InstInfo));

    line.insts[0].offset = 0;
    char* inst0 = (char*)malloc(sizeof(char) * 11);
    strncpy(inst0, "CONSTANT 0", 11);
    line.insts[0].content = inst0;

    line.insts[1].offset = 4;
    char* inst1 = (char*)malloc(sizeof(char) * 11);
    strncpy(inst1, "CONSTANT 1", 11);
    line.insts[1].content = inst1;

    LineList list;
    list.first = list.last = NULL;
    pushBackLineList(&list, &line);
    clearLine(&line);
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
    clearLineList(&list);
}
