#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../VM/common.h"
#include "../VM/chunk.h"
#include "../VM/dumpChunk.h"
#include "../VM/error.h"
#include "../VM/vm.h"

static void repl() {
    char line[1024];
    for (;;) {
        printf("> ");
        if (!fgets(line, sizeof(line), stdin) || strcmp(line, ":exit\n") == 0) {
            printf("\n");
            break;
        }
        interpret(line);
    }
}

static char* readFile(const char* path) {
    FILE* file = fopen(path, "rb");
    ASSERT_OR_EXIT1(file, "readFile: Failed to open file \"%s\".\n", path);
    // ファイル末尾までシークして ftell でファイルサイズを得る
    fseek(file, 0L, SEEK_END);
    size_t fileSize = ftell(file);
    // ファイルポインタの位置を先頭に戻す
    rewind(file);
    char* buffer = malloc(fileSize + 1);
    ASSERT_OR_EXIT1(buffer, "readFile: Not enough memory to read \"%s\".\n", path);
    size_t bytesRead = fread(buffer, sizeof(char), fileSize, file);
    ASSERT_OR_EXIT1(bytesRead == fileSize, "readFile: Could not read file \"%s\".\n", path);
    buffer[bytesRead] = '\0';
    fclose(file);
    return buffer;
}

static void runFile(const char* path) {
    char* source = readFile(path);
    InterpretResult result = interpret(source);
    free(source);
    if (result == INTERPRET_COMPILE_ERROR) exit(65);
    if (result == INTERPRET_RUNTIME_ERROR) exit(70);
}

int main(int argc, char* argv[]) {
    initVM();
    if (argc == 1) {
        repl();
    } else if (argc == 2) {
        runFile(argv[1]);
    } else {
        EXIT1_MSG("Usage: clox [path]\n");
    }
    freeVM();
}
