#pragma once

#include "chunk.h"

int disassembleInstruction(Chunk* chunk, int offset, bool alwaysDisplayLineNum);

// チャンクに格納された命令列の内容を、人間に読めるかたちで出力する
void disassembleChunk(Chunk* chunk, const char* name);

typedef struct {
    int lineNumber;
    int numInstructions;
    char** instructions;
} Line;

struct lineListCell {
    Line line;
    struct listListCell* next;
};

typedef struct {
    struct lineListCell** first;
    struct lineListCell** last;
} LineList;

void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath);
