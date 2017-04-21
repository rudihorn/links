#!/bin/bash

make -f MakefileLinksTests

if [ $? -eq 0 ]; then
	clear
	./linksTests -runner sequential
else
	echo "Build failed, not running tests."
fi

