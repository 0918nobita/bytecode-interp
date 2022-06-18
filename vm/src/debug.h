#pragma once

#include "chunk.h"

int disassembleInstruction(Chunk* chunk, int offset);

// チャンクに格納された命令列の内容を、人間に読めるかたちで出力する
void disassembleChunk(Chunk* chunk, const char* name);
