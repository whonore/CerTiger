#!/bin/sh
INCLUDES=$(make print-includes)
coqide $INCLUDES "$@"
