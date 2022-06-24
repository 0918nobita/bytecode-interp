#include <stdio.h>

#include "error.h"

void exitFailure(const char* msg) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
}
