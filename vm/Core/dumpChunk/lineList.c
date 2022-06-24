#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../error.h"
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
        if (list->last != NULL) EXIT1_MSG("pushBackLineList: Invalid value of type LineList\n");

        struct lineListCell* cell = malloc(sizeof(struct lineListCell));
        ASSERT_OR_EXIT1(cell, "pushBackLineList: Failed to allocate memory for list cell\n");

        deepCopyLine(&cell->line, line);
        cell->next = NULL;

        struct lineListCell** firstCellPtr = malloc(sizeof(struct lineListCell*));
        ASSERT_OR_EXIT1(firstCellPtr, "pushBackLineList: Failed to allocate memory for list cell pointer\n");
        *firstCellPtr = cell;

        struct lineListCell** lastCellPtr = malloc(sizeof(struct lineListCell*));
        ASSERT_OR_EXIT1(lastCellPtr, "pushBackLineList: Failed to allocate memory for list cell pointer\n");
        *lastCellPtr = cell;

        (*list).first = firstCellPtr;
        (*list).last = lastCellPtr;
        return;
    }

    if (list->last == NULL) EXIT1_MSG("pushBackLineList: Invalid value of type LineList\n");

    struct lineListCell* cell = malloc(sizeof(struct lineListCell));
    ASSERT_OR_EXIT1(cell, "pushBackLineList: Failed to allocate memory for list cell\n");

    deepCopyLine(&cell->line, line);

    cell->next = NULL;
    (*list->last)->next = cell;
    *list->last = cell;
}

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content) {
    if (list->last != NULL) {
        Line* lastLine = &(*list->last)->line;
        int prevLineNum = lastLine->lineNumber;
        if (prevLineNum == lineNumber) {
            InstInfo* insts = realloc(lastLine->insts, sizeof(InstInfo) * (lastLine->numInsts + 1));
            ASSERT_OR_EXIT1(insts, "appendInstruction: Failed to reallocate memory for InstInfo array\n");

            lastLine->insts = insts;
            lastLine->insts[lastLine->numInsts].offset = offset;
            lastLine->insts[lastLine->numInsts].content = strdup(content);
            lastLine->numInsts++;
            return;
        }
    }

    Line line;
    line.lineNumber = lineNumber;
    line.numInsts = 1;

    InstInfo* insts = malloc(sizeof(InstInfo));
    ASSERT_OR_EXIT1(insts, "appendInstruction: Failed to allocate memory for InstInfo array\n")
    line.insts = insts;

    line.insts[0].offset = offset;
    line.insts[0].content = strdup(content);
    pushBackLineList(list, &line);
}
