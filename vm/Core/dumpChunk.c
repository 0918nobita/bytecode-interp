#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "dumpChunk.h"
#include "error.h"

static void readConstantInstruction(Chunk* chunk, int* offset, char** inst) {
    uint8_t constantIndex = chunk->code[*offset + 1];
    const size_t len = 26;
    *inst = malloc(sizeof(char) * len);
    if (!*inst)
        EXIT1_MSG("readConstantInstruction: Failed to allocate memory for copying instruction content");
    snprintf(*inst, len, "CONSTANT %3d (%6.3lf)", constantIndex, chunk->constants.values[constantIndex]);
    *offset += 2;
}

static void readSimpleInstruction(char** inst, int* offset, const char* content) {
    *inst = strdup(content);
    *offset += 1;
}

void readInstruction(Chunk* chunk, int* offset, char** inst) {
    uint8_t instruction = chunk->code[*offset];
    switch (instruction) {
        case OP_CONSTANT:
            readConstantInstruction(chunk, offset, inst);
            break;
        case OP_ADD:
            readSimpleInstruction(inst, offset, "ADD");
            break;
        case OP_SUBTRACT:
            readSimpleInstruction(inst, offset, "SUBTRACT");
            break;
        case OP_MULTIPLY:
            readSimpleInstruction(inst, offset, "MULTIPLY");
            break;
        case OP_DIVIDE:
            readSimpleInstruction(inst, offset, "DIVIDE");
            break;
        case OP_NEGATE:
            readSimpleInstruction(inst, offset, "NEGATE");
            break;
        case OP_RETURN:
            readSimpleInstruction(inst, offset, "RETURN");
            break;
        default:
            EXIT1_MSG("Invalid instruction at %04d\n", *offset);
    }
}

// チャンクの内容を HTML 形式でファイルに出力する
void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath) {
    FILE* file = fopen(outFilePath, "w");
    if (!file) EXIT1_MSG("Could not open %s\n", outFilePath);

    fprintf(file,   "<!DOCTYPE html>\n"
                    "<html>\n"
                    "<head>\n"
                    "<meta charset=\"utf-8\">\n");
    fprintf(file,   "<title>%s</title>\n", title);
    fprintf(file,   "<style>th, td { padding: 2px 5px; }</style>\n"
                    "</head>\n"
                    "<body>\n"
                    "<table border=\"1\">\n"
                    "<tr><th>offset</th><th>line</th><th>instruction</th></tr>\n");

    LineList lines;
    lines.first = lines.last = NULL;

    for (int offset = 0; offset < chunk->count;) {
        int prevOffset = offset;
        char* instruction = NULL;
        readInstruction(chunk, &offset, &instruction);
        appendInstruction(&lines, prevOffset, chunk->lines[prevOffset], instruction);
        free(instruction);
    }

    for (struct lineListCell* cell = *lines.first; cell != NULL; cell = (void*)cell->next) {
        Line* line = &cell->line;
        fprintf(
            file,
            "<tr><td align=\"right\">%04d</td><td rowspan=\"%d\" valign=\"top\" align=\"right\">%d</td><td>%s</td></tr>\n",
            line->insts[0].offset,
            line->numInsts,
            line->lineNumber,
            line->insts[0].content
        );
        for (int i = 1; i < line->numInsts; i++)
            fprintf(file, "<tr><td align=\"right\">%04d</td><td>%s</td></tr>\n", line->insts[i].offset, line->insts[i].content);
    }

    clearLineList(&lines);

    fprintf(file,   "</table>\n"
                    "</body>\n"
                    "</html>\n");
    fclose(file);
}
