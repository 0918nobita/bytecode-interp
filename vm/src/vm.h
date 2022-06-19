#pragma once

#include "chunk.h"

typedef struct {
    // 実行対象のチャンク
    Chunk* chunk;
    // 命令ポインタ (instruction pointer, ip)
    uint8_t* instPtr;
} VM;

typedef enum {
    INTERPRET_OK,
    INTERPRET_COMPILE_ERROR,
    INTERPRET_RUNTIME_ERROR,
} InterpretResult;

void initVM();

void freeVM();

InterpretResult interpret(Chunk* chunk);
