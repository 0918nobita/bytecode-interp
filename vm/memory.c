#include <stdlib.h>
#include <stdio.h>

#include "error.h"
#include "memory.h"

int growCapacity(int capacity) {
    return capacity < 8 ? 8 : capacity * 2;
}

void* reallocate(void* pointer, size_t oldSize, size_t newSize) {
    (void)oldSize;

    if (newSize == 0) {
        free(pointer);
        return NULL;
    }

    // C 標準ライブラリの realloc を用いる
    // pointer が NULL の場合、malloc と同じく新規にメモリ領域を確保する
    void* result = realloc(pointer, newSize);
    ASSERT_OR_EXIT1(result, "Failed to reallocate memory");
    return result;
}
