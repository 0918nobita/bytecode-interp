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

void pushBackLineList(LineList* list, const Line* line) {
    if (list->first == NULL) {
        if (list->last != NULL) {
            fprintf(stderr, "pushBackLineList: Fatal error\n");
            exit(1);
        }
        struct lineListCell* cell = malloc(sizeof(struct lineListCell));
        if (!cell) {
            fprintf(stderr, "Failed to allocate memory for list cell (pushBackLineList)");
            exit(1);
        }
        deepCopyLine(&cell->line, line);
        cell->next = NULL;
        struct lineListCell** firstCellPtr = malloc(sizeof(struct lineListCell*));
        if (!firstCellPtr) {
            fprintf(stderr, "Failed to allocate memory for list cell pointer (pushBackLineList)");
            exit(1);
        }
        *firstCellPtr = cell;
        struct lineListCell** lastCellPtr = malloc(sizeof(struct lineListCell*));
        if (!lastCellPtr) {
            fprintf(stderr, "Failed to allocate memory for list cell pointer (pushBackLineList)");
            exit(1);
        }
        *lastCellPtr = cell;
        (*list).first = firstCellPtr;
        (*list).last = lastCellPtr;
        return;
    }
    if (list->last == NULL) {
        fprintf(stderr, "pushBackLineList: Fatal error\n");
        exit(1);
    }
    struct lineListCell* cell = malloc(sizeof(struct lineListCell));
    if (!cell) exit(1);
    deepCopyLine(&cell->line, line);
    cell->next = NULL;
    // if (list->first == list->last) (*list->first)->next = cell;
    (*list->last)->next = cell;
    *list->last = cell;
}

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content) {
    if (list->last != NULL) {
        Line* lastLine = &(*list->last)->line;
        int prevLineNum = lastLine->lineNumber;
        if (prevLineNum == lineNumber) {
            InstInfo* insts = realloc(lastLine->insts, sizeof(InstInfo) * (lastLine->numInsts + 1));
            if (!insts) {
                fprintf(stderr, "Failed to reallocate memory for InstructionInfo (appendInstruction)");
                exit(1);
            }
            lastLine->insts = insts;
            lastLine->insts[lastLine->numInsts].offset = offset;
            size_t len = strlen(content) + 1;
            char* destContent = malloc(sizeof(char) * len);
            if (!destContent) {
                fprintf(stderr, "Failed to allocate memory for copying instruction content (appendInstruction)");
                exit(1);
            }
            lastLine->insts[lastLine->numInsts].content = destContent;
            strncpy(destContent, content, len);
            lastLine->numInsts++;
            return;
        }
    }

    Line line;
    line.lineNumber = lineNumber;
    line.numInsts = 1;
    line.insts = malloc(sizeof(InstInfo));
    line.insts[0].offset = offset;
    size_t len = strlen(content) + 1;
    char* destContent = malloc(sizeof(char) * len);
    if (!destContent) {
        fprintf(stderr, "Failed to allocate memory for copying instruction content (appendInstruction)");
        exit(1);
    }
    line.insts[0].content = destContent;
    strncpy(destContent, content, len);
    pushBackLineList(list, &line);
}
