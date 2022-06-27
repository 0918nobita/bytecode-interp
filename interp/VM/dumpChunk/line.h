#pragma once

#include "inst.h"

typedef struct {
    int lineNumber;
    int numInsts;
    InstInfo* insts;
} Line;

void deepCopyLine(Line* dest, const Line* src);

void clearLine(Line* line);
