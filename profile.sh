#!/bin/bash
set -ex
idris2 --build probe.ipkg --profile
./build/exec/probe
