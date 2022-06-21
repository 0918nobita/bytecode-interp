#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "debug.h"

static int constantInstruction(const char* name, Chunk* chunk, int offset) {
    uint8_t constantIndex = chunk->code[offset + 1];
    printf("%-16s %4d '", name, constantIndex);
    printValue(chunk->constants.values[constantIndex]);
    printf("'\n");
    return offset + 2;
}

static int simpleInstruction(const char* name, int offset) {
    printf("%s\n", name);
    return offset + 1;
}

int disassembleInstruction(Chunk* chunk, int offset, bool alwaysDisplayLineNum) {
    printf("%04d ", offset);
    if (!alwaysDisplayLineNum && offset > 0 && chunk->lines[offset] == chunk->lines[offset - 1]) {
        printf("   | ");
    } else {
        printf("%4d ", chunk->lines[offset]);
    }

    uint8_t instruction = chunk->code[offset];
    switch (instruction) {
        case OP_CONSTANT:
            return constantInstruction("OP_CONSTANT", chunk, offset);

        case OP_ADD:
            return simpleInstruction("OP_ADD", offset);

        case OP_SUBTRACT:
            return simpleInstruction("OP_SUBTRACT", offset);

        case OP_MULTIPLY:
            return simpleInstruction("OP_MULTIPLY", offset);

        case OP_DIVIDE:
            return simpleInstruction("OP_DIVIDE", offset);

        case OP_NEGATE:
            return simpleInstruction("OP_NEGATE", offset);

        case OP_RETURN:
            return simpleInstruction("OP_RETURN", offset);

        default:
            fprintf(stderr, "Invalid instruction at %04d\n", offset);
            exit(1);
    }
}

void disassembleChunk(Chunk* chunk, const char* name) {
    printf("== %s ==\n", name);
    for (int offset = 0; offset < chunk->count;) {
        offset = disassembleInstruction(chunk, offset, false);
    }
}

void pushBackLineList(LineList* list, Line line) {
    if (list->first == NULL) {
        if (list->last != NULL) {
            fprintf(stderr, "pushBackLineList: Fatal error\n");
            exit(1);
        }
        struct lineListCell* cell = malloc(sizeof(struct lineListCell));
        cell->line = line;
        cell->next = NULL;
        struct listListCell** cellPtr = malloc(sizeof(struct listListCell*));
        *cellPtr = (void*)cell;
        (*list).first = (void*)cellPtr;
        (*list).last = (void*)cellPtr;
        return;
    }
    if (list->last == NULL) {
        fprintf(stderr, "pushBackLineList: Fatal error\n");
        exit(1);
    }
    struct lineListCell* cell = malloc(sizeof(struct lineListCell));
    cell->line = line;
    cell->next = NULL;
    (*list->last)->next = (void*)cell;
    *list->last = cell;
}

void appendInstruction(LineList* list, int offset, int lineNumber, const char* content) {
    if (list->last != NULL) {
        Line* lastLine = &(*list->last)->line;
        int prevLineNum = lastLine->lineNumber;
        if (prevLineNum == lineNumber) {
            lastLine->instructions = (InstructionInfo*)realloc(lastLine->instructions, sizeof(InstructionInfo) * (lastLine->numInstructions + 1));
            lastLine->instructions[lastLine->numInstructions].offset = offset;
            lastLine->instructions[lastLine->numInstructions].content = (char*)malloc(sizeof(char) * strlen(content));
            strcpy(lastLine->instructions[lastLine->numInstructions].content, content);
            lastLine->numInstructions++;
            return;
        }
    }

    Line line;
    line.lineNumber = lineNumber;
    line.numInstructions = 1;
    line.instructions = malloc(sizeof(InstructionInfo));
    line.instructions[0].offset = offset;
    line.instructions[0].content = (char*)malloc(sizeof(char) * strlen(content));
    strcpy(line.instructions[0].content, content);
    pushBackLineList(list, line);
}

static char* readConstantInstruction(Chunk* chunk, int* offset) {
    uint8_t constantIndex = chunk->code[*offset + 1];
    char* msg = "CONSTANT ";
    int len = strlen(msg);
    char* inst = malloc(sizeof(char) * (len + 17));
    strcpy(inst, msg);
    sprintf(inst + len, "%3d (%6.3lf)", constantIndex, chunk->constants.values[constantIndex]);
    *offset += 2;
    return inst;
}

static void readSimpleInstruction(int* offset) {
    *offset += 1;
}

char* readInstruction(Chunk* chunk, int* offset) {
    uint8_t instruction = chunk->code[*offset];
    switch (instruction) {
        case OP_CONSTANT:
            return readConstantInstruction(chunk, offset);
        case OP_ADD:
            readSimpleInstruction(offset);
            return "ADD";
        case OP_SUBTRACT:
            readSimpleInstruction(offset);
            return "SUBTRACT";
        case OP_MULTIPLY:
            readSimpleInstruction(offset);
            return "MULTIPLY";
        case OP_DIVIDE:
            readSimpleInstruction(offset);
            return "DIVIDE";
        case OP_NEGATE:
            readSimpleInstruction(offset);
            return "NEGATE";
        case OP_RETURN:
            readSimpleInstruction(offset);
            return "RETURN";
        default:
            fprintf(stderr, "Invalid instruction at %04d\n", *offset);
            exit(1);
    }
}

// チャンクの内容を HTML 形式でファイルに出力する
void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath) {
    FILE* file = fopen(outFilePath, "w");
    if (file == NULL) {
        fprintf(stderr, "Could not open %s\n", outFilePath);
        exit(1);
    }
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
        char* instruction = readInstruction(chunk, &offset);
        appendInstruction(&lines, prevOffset, chunk->lines[prevOffset], instruction);
    }

    for (struct lineListCell* cell = *lines.first; cell != NULL; cell = (void*)cell->next) {
        Line* line = &cell->line;
        fprintf(
            file,
            "<tr><td align=\"right\">%04d</td><td rowspan=\"%d\" valign=\"top\" align=\"right\">%d</td><td>%s</td></tr>\n",
            line->instructions[0].offset,
            line->numInstructions,
            line->lineNumber,
            line->instructions[0].content
        );
        for (int i = 1; i < line->numInstructions; i++)
            fprintf(file, "<tr><td align=\"right\">%04d</td><td>%s</td></tr>\n", line->instructions[i].offset, line->instructions[i].content);
    }

    fprintf(file,   "</table>\n"
                    "</body>\n"
                    "</html>\n");
    fclose(file);
}
