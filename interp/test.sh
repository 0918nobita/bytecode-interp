#!/bin/sh -ev

ninja -t clean build/libvm.a build/test
ninja build/test
./build/test
