#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "line.h"

void deepCopyInstInfo(InstInfo* dest, const InstInfo* src) {
    assert(src != NULL);
    assert(dest != NULL);
    dest->offset = src->offset;
    dest->content = strdup(src->content);
}

void deepCopyLine(Line* dest, const Line* src) {
    assert(src != NULL);
    assert(dest != NULL);
    dest->lineNumber = src->lineNumber;
    dest->numInsts = src->numInsts;
    if (src->numInsts == 0) {
        dest->insts = NULL;
        return;
    }
    dest->insts = malloc(sizeof(InstInfo) * src->numInsts);
    for (int i = 0; i < src->numInsts; i++) {
        deepCopyInstInfo(dest->insts + i, src->insts + i);
    }
}

void clearLine(Line* line) {
    if (!line || !line->insts) return;
    for (int i = 0; i < line->numInsts; i++)
        free(line->insts[i].content);
    free(line->insts);
}
