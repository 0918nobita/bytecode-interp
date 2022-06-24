#include <stdio.h>
#include <stdlib.h>

#include "common.h"
#include "error.h"
#include "debug.h"
#include "vm.h"

VM vm;

static void resetStack() {
    vm.stackTop = vm.stack;
}

void initVM() {
    resetStack();
}

void freeVM() {}

void push(Value value) {
    *vm.stackTop = value;
    vm.stackTop++;
}

Value pop() {
    vm.stackTop--;
    return *vm.stackTop;
}

static void dumpStack() {
    bool isFirst = true;
    printf("[");
    for (Value* slot = vm.stack; slot < vm.stackTop; slot++) {
        if (!isFirst) printf(", ");
        printValue(*slot);
        isFirst = false;
    }
    printf("]\n");
}

static InterpretResult run() {
#define READ_BYTE() (*vm.instPtr++)
#define READ_CONSTANT() (vm.chunk->constants.values[READ_BYTE()])
    for (;;) {
#ifdef _DEBUG
        dumpStack();
        disassembleInstruction(vm.chunk, (int)(vm.instPtr - vm.chunk->code), true);
#endif

        uint8_t instruction = READ_BYTE();

        switch (instruction) {
            case OP_CONSTANT: {
                Value constant = READ_CONSTANT();
                push(constant);
                break;
            }

            case OP_ADD: {
                double rhs = pop();
                double lhs = pop();
                push(lhs + rhs);
                break;
            }

            case OP_SUBTRACT: {
                double rhs = pop();
                double lhs = pop();
                push(lhs - rhs);
                break;
            }

            case OP_MULTIPLY: {
                double rhs = pop();
                double lhs = pop();
                push(lhs * rhs);
                break;
            }

            case OP_DIVIDE: {
                double rhs = pop();
                double lhs = pop();
                push(lhs / rhs);
                break;
            }

            case OP_RETURN:
                printValue(pop());
                printf("\n");
                return INTERPRET_OK;

            case OP_NEGATE:
                push(-pop());
                break;

            default:
                EXIT1_MSG("run: Unknown instruction (opcode = %d)", instruction);
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
