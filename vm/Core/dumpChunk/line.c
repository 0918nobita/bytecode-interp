#include <stdlib.h>

#include "line.h"

void clearInstructionInfo(InstructionInfo* instructionInfo) {
    if (!instructionInfo || !instructionInfo->content) return;
    free(instructionInfo->content);
}

void clearLine(Line* line) {
    if (!line || !line->instructions) return;
    for (int i = 0; i < line->numInstructions; i++)
        clearInstructionInfo(&line->instructions[i]);
    free(line->instructions);
}
