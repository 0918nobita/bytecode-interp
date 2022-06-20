#pragma once

#include "chunk.h"

#define STACK_MAX 256

typedef struct {
    // 実行対象のチャンク
    Chunk* chunk;
    // 命令ポインタ (instruction pointer, ip)
    uint8_t* instPtr;

    Value stack[STACK_MAX];
    Value* stackTop;
} VM;

typedef enum {
    INTERPRET_OK,
    INTERPRET_COMPILE_ERROR,
    INTERPRET_RUNTIME_ERROR,
} InterpretResult;

void initVM();
void freeVM();

void push(Value value);
Value pop();

InterpretResult interpret(Chunk* chunk);
