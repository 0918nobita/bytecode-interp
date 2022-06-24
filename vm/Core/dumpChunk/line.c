#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../error.h"
#include "line.h"

void deepCopyLine(Line* dest, const Line* src) {
    ASSERT_OR_EXIT1(src != NULL,  "deepCopyLine: Source should not be NULL.\n");
    ASSERT_OR_EXIT1(dest != NULL, "deepCopyLine: Destination should not be NULL.\n");
    dest->lineNumber = src->lineNumber;
    dest->numInsts = src->numInsts;
    if (src->numInsts == 0) {
        dest->insts = NULL;
        return;
    }
    dest->insts = malloc(sizeof(InstInfo) * src->numInsts);
    for (int i = 0; i < src->numInsts; i++)
        deepCopyInstInfo(dest->insts + i, src->insts + i);
}

void clearLine(Line* line) {
    if (!line) return;
    ASSERT_OR_EXIT1(
        line->numInsts == 0 || line->insts != NULL,
        "clearLine: Invalid value of type Line.\n"
    );
    for (int i = 0; i < line->numInsts; i++) {
        char* content = line->insts[i].content;
        free(content);
    }
    free(line->insts);
}
