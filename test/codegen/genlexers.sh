#!/usr/bin/env bash

pack --log-level silence exec src/Gen.idr >src/Lexer.idr
pack --log-level silence exec src/Package.idr >src/PackageLexer.idr
pack --log-level silence exec src/Smiles.idr >src/SmilesLexer.idr
