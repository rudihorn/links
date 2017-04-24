#!/bin/bash

make -f MakefileLinksTests

if [ $? -eq 0 ]; then
	clear
	echo "Compilation was successful, running tests."
	./linksTests -runner sequential
else
	echo "Build failed, not running tests."
fi

