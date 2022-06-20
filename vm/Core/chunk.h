#pragma once

// コード表現

#include "common.h"
#include "value.h"

// 各命令は 1 byte のオペコードを持ち、命令の種類を表す
typedef enum {
    OP_CONSTANT, // 定数をロードする
    OP_RETURN,   // 現在の関数から返る
} OpCode;

// 命令と一緒に格納する、データの動的配列
// 現在の要素数とキャパシティも保持することで、アクセス・操作を効率化する
typedef struct {
    int count;
    int capacity;
    uint8_t* code;
    int* lines;
    ValueArray constants;
} Chunk;

void initChunk(Chunk* chunk);

// 要素を追加する際にキャパシティが足りない場合には、キャパシティを増やした新しい配列用の領域を確保し、全要素をコピーして参照を更新したうえで要素を追加し、カウントを増やす
void writeChunk(Chunk* chunk, uint8_t byte, int line);

// チャンクに定数を追加し、コンスタントプールにおけるインデックスを返す
int addConstant(Chunk* chunk, Value value);

void freeChunk(Chunk* chunk);
