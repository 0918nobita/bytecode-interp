#!/bin/sh -ev

ninja -t clean build/libcorevm.a build/test
ninja build/test
./build/test
