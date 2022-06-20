#include <stdio.h>

#include "common.h"
#include "debug.h"
#include "vm.h"

VM vm;

void initVM() {}

void freeVM() {}

static InterpretResult run() {
#define READ_BYTE() (*vm.instPtr++)
#define READ_CONSTANT() (vm.chunk->constants.values[READ_BYTE()])
    for (;;) {
#ifdef _DEBUG
        disassembleInstruction(vm.chunk, (int)(vm.instPtr - vm.chunk->code), false);
#endif

        uint8_t instruction = READ_BYTE();

        switch (instruction) {
            case OP_CONSTANT: {
#ifdef _DEBUG
                Value constant = READ_CONSTANT();
                printValue(constant);
                printf("\n");
#else
                READ_CONSTANT();
#endif
                break;
            }

            case OP_RETURN:
                return INTERPRET_OK;
        }
    }
#undef READ_CONSTANT
#undef READ_BYTE
}

InterpretResult interpret(Chunk* chunk) {
    vm.chunk = chunk;
    vm.instPtr = vm.chunk->code;
    return run();
}
