Source for dynamic symmetry breaking specifically for Norines Conjecture and related problems.

Use `git submodule update --init --recursive` to init cadical

Use `build-and-install.sh` for building it. The program should then be in `./build/src/norine`.
The first argument is the number of dimensions, the second the frequency, the third whether all models should be generated and the fourth (if present) the encoding in DIMACS format.