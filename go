#!/bin/bash


set -e
./target/${1-release}/eck
gcc -o test test.o
set +e

./test
echo $?
