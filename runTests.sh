#!/bin/bash

make -f MakefileLinksTests
./linksTests -runner sequential
