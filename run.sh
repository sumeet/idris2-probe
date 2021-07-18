#!/bin/bash
set -ex
idris2 --build probe.ipkg
./build/exec/probe
