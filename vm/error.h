#pragma once

#define EXIT1_MSG(...) { fprintf(stderr, __VA_ARGS__); exit(1); }

#define ASSERT_OR_EXIT1(cond, ...) \
    if (!(cond)) { fprintf(stderr, __VA_ARGS__); exit(1); }
