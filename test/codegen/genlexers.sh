#!/usr/bin/env bash

pack --log-level silence --no-prompt exec src/Gen.idr > src/Lexer.idr
