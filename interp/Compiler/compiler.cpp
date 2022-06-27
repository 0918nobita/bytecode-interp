#include "compiler.hpp"
#include "scanner.hpp"

extern "C" void compile(const char* source) {
    std::string source_str(source);
    initScanner(std::make_shared<std::string>(source_str));
}
