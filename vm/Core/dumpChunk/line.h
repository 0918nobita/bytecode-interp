#pragma once

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
