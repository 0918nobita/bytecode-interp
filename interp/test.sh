#!/bin/sh -ev

cargo build
ninja -t clean build/libvm.a build/test
ninja build/test
./build/test
