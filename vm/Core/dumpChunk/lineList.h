#pragma once

#include "line.h"

struct lineListCell {
    Line line;
    struct lineListCell* next;
};

typedef struct {
    struct lineListCell** first;
    struct lineListCell** last;
} LineList;

void clearLineList(LineList* lineList);

void pushBackLineList(LineList* list, const Line* line);

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content);
