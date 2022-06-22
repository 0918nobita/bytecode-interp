#pragma once

#include "chunk.h"
#include "dumpChunk/lineList.h"

void readInstruction(Chunk* chunk, int* offset, char** inst);

void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath);
