#pragma once

#include "chunk.h"

int disassembleInstruction(Chunk* chunk, int offset, bool alwaysDisplayLineNum);

// チャンクに格納された命令列の内容を、人間に読めるかたちで出力する
void disassembleChunk(Chunk* chunk, const char* name);

typedef struct {
    int offset;
    char* content;
} InstructionInfo;

typedef struct {
    int lineNumber;
    int numInstructions;
    InstructionInfo* instructions;
} Line;

struct lineListCell {
    Line line;
    struct listListCell* next;
};

typedef struct {
    struct lineListCell** first;
    struct lineListCell** last;
} LineList;

void pushBackLineList(LineList* list, Line line);

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content);

char* readInstruction(Chunk* chunk, int* offset);

void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath);
