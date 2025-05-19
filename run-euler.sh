#!/bin/bash

# Run lake build
lake build > /dev/null 2>&1

# Run the compiled binary
.lake/build/bin/euler-comp