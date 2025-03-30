@echo off
setlocal EnableDelayedExpansion
set agdahyperfinepath=./artifact/src/Test/
set agdahyperfinecmd=hyperfine --runs 100 --show-output
for %%f in (%agdahyperfinepath%*) do (
    echo %%f
    set agdahyperfinecmd=!agdahyperfinecmd! 'agda -- --no-caching "%agdahyperfinepath%%%f"'
)
%agdahyperfinecmd%