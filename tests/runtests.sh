#!/bin/sh
cc -o testlisp -DDEBUG -O2 ../src/lisp-cheney.c 
./testlisp runtests.lisp
rm -f testlisp
