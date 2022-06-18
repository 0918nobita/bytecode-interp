#include <CppUTest/CommandLineTestRunner.h>

TEST_GROUP(Add) {};

TEST(Add, FirstTest) {
    int actual = 3 + 4;
    int expected = 7;
    CHECK_EQUAL(expected, actual);
}

int main(int argc, char* argv[]) {
    return CommandLineTestRunner::RunAllTests(argc, argv);
}
