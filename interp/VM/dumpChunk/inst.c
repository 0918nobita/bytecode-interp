#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../error.h"
#include "inst.h"

void deepCopyInstInfo(InstInfo* dest, const InstInfo* src) {
    ASSERT_OR_EXIT1(src != NULL,  "deepCopyInstInfo: Source should not be NULL.\n");
    ASSERT_OR_EXIT1(dest != NULL, "deepCopyInstInfo: Destination should not be NULL.\n");
    dest->offset = src->offset;
    dest->content = strdup(src->content);
}
