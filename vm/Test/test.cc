#include <cstring>

#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable:28251)
#include <CppUTest/CommandLineTestRunner.h>
#pragma warning(pop)
#else
#include <CppUTest/CommandLineTestRunner.h>
#endif

int main(int argc, char* argv[]) {
    return CommandLineTestRunner::RunAllTests(argc, argv);
}
