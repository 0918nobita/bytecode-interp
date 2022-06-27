#include <iostream>
#include <memory>

#include "scanner.hpp"

struct Scanner {
    std::shared_ptr<std::string> source;
    int start;
    int current;
    int line;
};

Scanner scanner;

void initScanner(const std::shared_ptr<std::string> source) {
    scanner.source = source;
    scanner.start = 0;
    scanner.current = 0;
    scanner.line = 1;
}
