#pragma once

// VM で扱う値
typedef double Value;

void printValue(Value value);

// コンスタントプールとして用いる、値の動的配列
typedef struct {
    int count;
    int capacity;
    Value* values;
} ValueArray;

void initValueArray(ValueArray* array);

void writeValueArray(ValueArray* array, Value value);

void freeValueArray(ValueArray* array);
