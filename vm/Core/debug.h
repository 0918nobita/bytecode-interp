#pragma once

#include "chunk.h"

int disassembleInstruction(Chunk* chunk, int offset, bool alwaysDisplayLineNum);

// チャンクに格納された命令列の内容を、人間に読めるかたちで出力する
void disassembleChunk(Chunk* chunk, const char* name);

typedef struct {
    int offset;
    char* content;
} InstructionInfo;

void clearInstructionInfo(InstructionInfo* instructionInfo);

typedef struct {
    int lineNumber;
    int numInstructions;
    InstructionInfo* instructions;
} Line;

void clearLine(Line* line);

struct lineListCell {
    Line line;
    struct lineListCell* next;
};

typedef struct {
    struct lineListCell** first;
    struct lineListCell** last;
} LineList;

void clearLineList(LineList* lineList);

void pushBackLineList(LineList* list, Line line);

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content);

void readInstruction(Chunk* chunk, int* offset, char** inst);

void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath);
