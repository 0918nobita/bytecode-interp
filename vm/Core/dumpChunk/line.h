#pragma once

typedef struct {
    int offset;
    char* content;
} InstInfo;

void deepCopyInstInfo(InstInfo* dest, const InstInfo* src);

typedef struct {
    int lineNumber;
    int numInsts;
    InstInfo* insts;
} Line;

void deepCopyLine(Line* dest, const Line* src);

void clearLine(Line* line);
