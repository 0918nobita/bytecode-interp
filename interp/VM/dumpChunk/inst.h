#pragma once

typedef struct {
    int offset;
    char* content;
} InstInfo;

void deepCopyInstInfo(InstInfo* dest, const InstInfo* src);
