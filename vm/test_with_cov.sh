#!/bin/sh -ev

rm -rf coverage
ninja -t clean build/libcorevm.a build/test
PSY_COVERAGE=true ninja build/test
./build/test
lcov -c -d . --no-external -o lcov.info
genhtml lcov.info -o coverage
