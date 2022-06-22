#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lineList.h"

void clearLineList(LineList* lineList) {
    for (struct lineListCell* cell = *lineList->first; cell != NULL;) {
        clearLine(&cell->line);
        struct lineListCell* tmpCell = cell->next;
        free(cell);
        cell = tmpCell;
    }
}

void pushBackLineList(LineList* list, Line line) {
    if (list->first == NULL) {
        if (list->last != NULL) {
            fprintf(stderr, "pushBackLineList: Fatal error\n");
            exit(1);
        }
        struct lineListCell* cell = (struct lineListCell*)malloc(sizeof(struct lineListCell));
        if (!cell) {
            fprintf(stderr, "Failed to allocate memory for list cell (pushBackLineList)");
            exit(1);
        }
        cell->line = line;
        cell->next = NULL;
        struct lineListCell** cellPtr = (struct lineListCell**)malloc(sizeof(struct lineListCell*));
        if (!cellPtr) {
            fprintf(stderr, "Failed to allocate memory for list cell pointer (pushBackLineList)");
            exit(1);
        }
        *cellPtr = cell;
        (*list).first = (void*)cellPtr;
        (*list).last = (void*)cellPtr;
        return;
    }
    if (list->last == NULL) {
        fprintf(stderr, "pushBackLineList: Fatal error\n");
        exit(1);
    }
    struct lineListCell* cell = (struct lineListCell*)malloc(sizeof(struct lineListCell));
    if (!cell) exit(1);
    cell->line = line;
    cell->next = NULL;
    (*list->last)->next = (void*)cell;
    *list->last = cell;
}

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content) {
    if (list->last != NULL) {
        Line* lastLine = &(*list->last)->line;
        int prevLineNum = lastLine->lineNumber;
        if (prevLineNum == lineNumber) {
            InstructionInfo* instructions = (InstructionInfo*)realloc(lastLine->instructions, sizeof(InstructionInfo) * (lastLine->numInstructions + 1));
            if (!instructions) {
                fprintf(stderr, "Failed to reallocate memory for InstructionInfo (appendInstruction)");
                exit(1);
            }
            lastLine->instructions = instructions;
            lastLine->instructions[lastLine->numInstructions].offset = offset;
            size_t len = strlen(content) + 1;
            char* destContent = (char*)malloc(sizeof(char) * len);
            if (!destContent) {
                fprintf(stderr, "Failed to allocate memory for copying instruction content (appendInstruction)");
                exit(1);
            }
            lastLine->instructions[lastLine->numInstructions].content = destContent;
            strncpy(destContent, content, len);
            lastLine->numInstructions++;
            return;
        }
    }

    Line line;
    line.lineNumber = lineNumber;
    line.numInstructions = 1;
    line.instructions = malloc(sizeof(InstructionInfo));
    line.instructions[0].offset = offset;
    size_t len = strlen(content) + 1;
    char* destContent = (char*)malloc(sizeof(char) * len);
    if (!destContent) {
        fprintf(stderr, "Failed to allocate memory for copying instruction content (appendInstruction)");
        exit(1);
    }
    line.instructions[0].content = destContent;
    strncpy(destContent, content, len);
    pushBackLineList(list, line);
}
