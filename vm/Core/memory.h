#pragma once

int growCapacity(int capacity);

// oldSize が 0 なら新しいメモリ領域を確保する
// oldSize が 0 でなく newSize が 0 ならメモリ領域を解放する
// oldSize が 0 でなく newSize が oldSize より小さい場合はメモリ領域を縮小する
// oldSize が 0 でなく newSize が oldSize より大きい場合はメモリ領域を拡大する
void* reallocate(void* pointer, size_t oldSize, size_t newSize);

#define GROW_ARRAY(type, pointer, oldCount, newCount) \
    (type*)reallocate(pointer, sizeof(type) * (oldCount), sizeof(type) * (newCount))

#define FREE_ARRAY(type, pointer, oldCount) \
    reallocate(pointer, sizeof(type) * (oldCount), 0)
