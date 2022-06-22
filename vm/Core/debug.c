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

void clearInstructionInfo(InstructionInfo* instructionInfo) {
    if (!instructionInfo || !instructionInfo->content) return;
    free(instructionInfo->content);
}

void clearLine(Line* line) {
    if (!line || !line->instructions) return;
    for (int i = 0; i < line->numInstructions; i++)
        clearInstructionInfo(&line->instructions[i]);
    free(line->instructions);
}

void clearLineList(LineList* lineList) {
    for (struct lineListCell* cell = *lineList->first; cell != NULL;) {
        clearLine(&cell->line);
        struct lineListCell* tmpCell = cell->next;
        free(cell);
        cell = tmpCell;
    }
}

void pushBackLineList(LineList* list, Line line) {
    if (list->first == NULL) {
        if (list->last != NULL) {
            fprintf(stderr, "pushBackLineList: Fatal error\n");
            exit(1);
        }
        struct lineListCell* cell = (struct lineListCell*)malloc(sizeof(struct lineListCell));
        if (!cell) {
            fprintf(stderr, "Failed to allocate memory for list cell (pushBackLineList)");
            exit(1);
        }
        cell->line = line;
        cell->next = NULL;
        struct lineListCell** cellPtr = (struct lineListCell**)malloc(sizeof(struct lineListCell*));
        if (!cellPtr) {
            fprintf(stderr, "Failed to allocate memory for list cell pointer (pushBackLineList)");
            exit(1);
        }
        *cellPtr = cell;
        (*list).first = (void*)cellPtr;
        (*list).last = (void*)cellPtr;
        return;
    }
    if (list->last == NULL) {
        fprintf(stderr, "pushBackLineList: Fatal error\n");
        exit(1);
    }
    struct lineListCell* cell = (struct lineListCell*)malloc(sizeof(struct lineListCell));
    if (!cell) exit(1);
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
            InstructionInfo* instructions = (InstructionInfo*)realloc(lastLine->instructions, sizeof(InstructionInfo) * (lastLine->numInstructions + 1));
            if (!instructions) {
                fprintf(stderr, "Failed to reallocate memory for InstructionInfo (appendInstruction)");
                exit(1);
            }
            lastLine->instructions = instructions;
            lastLine->instructions[lastLine->numInstructions].offset = offset;
            size_t len = strlen(content) + 1;
            char* destContent = (char*)malloc(sizeof(char) * len);
            if (!destContent) {
                fprintf(stderr, "Failed to allocate memory for copying instruction content (appendInstruction)");
                exit(1);
            }
            lastLine->instructions[lastLine->numInstructions].content = destContent;
            strncpy(destContent, content, len);
            lastLine->numInstructions++;
            return;
        }
    }

    Line line;
    line.lineNumber = lineNumber;
    line.numInstructions = 1;
    line.instructions = malloc(sizeof(InstructionInfo));
    line.instructions[0].offset = offset;
    size_t len = strlen(content) + 1;
    char* destContent = (char*)malloc(sizeof(char) * len);
    if (!destContent) {
        fprintf(stderr, "Failed to allocate memory for copying instruction content (appendInstruction)");
        exit(1);
    }
    line.instructions[0].content = destContent;
    strncpy(destContent, content, len);
    pushBackLineList(list, line);
}

static void readConstantInstruction(Chunk* chunk, int* offset, char** inst) {
    uint8_t constantIndex = chunk->code[*offset + 1];
    const size_t len = 26;
    *inst = (char*)malloc(sizeof(char) * len);
    if (!*inst) {
        fprintf(stderr, "Failed to allocate memory for copying instruction content (readConstantInstruction)");
        exit(1);
    }
    snprintf(*inst, len, "CONSTANT %3d (%6.3lf)", constantIndex, chunk->constants.values[constantIndex]);
    *offset += 2;
}

static void readSimpleInstruction(char** inst, int* offset, const char* content) {
    size_t len = strlen(content) + 1;
    *inst = (char*)malloc(sizeof(char) * len);
    strncpy(*inst, content, len);
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
            fprintf(stderr, "Invalid instruction at %04d\n", *offset);
            exit(1);
    }
}

// チャンクの内容を HTML 形式でファイルに出力する
void dumpChunk(Chunk* chunk, const char* title, const char* outFilePath) {
    FILE* file = fopen(outFilePath, "w");
    if (!file) {
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
            line->instructions[0].offset,
            line->numInstructions,
            line->lineNumber,
            line->instructions[0].content
        );
        for (int i = 1; i < line->numInstructions; i++)
            fprintf(file, "<tr><td align=\"right\">%04d</td><td>%s</td></tr>\n", line->instructions[i].offset, line->instructions[i].content);
    }

    clearLineList(&lines);

    fprintf(file,   "</table>\n"
                    "</body>\n"
                    "</html>\n");
    fclose(file);
}
