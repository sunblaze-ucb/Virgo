# Acknowledgement

We use [Hyrax](https://github.com/hyraxZK)'s SHA256 circuit generator and LANCZOS circuit generator as a subroutine.

We list all files from Hyrax that in the following:
- [SHA256 Gen](https://github.com/sunblaze-ucb/Virgo/blob/master/tests/SHA256/sha256gen.py)
- [SHA256 Gen batch file](https://github.com/sunblaze-ucb/Virgo/blob/master/tests/SHA256/build.sh)
- [LANCZOS Gen](https://github.com/sunblaze-ucb/Virgo/blob/master/tests/lanczos/lanczos2.py)
- [LANCZOS GEN batch file](https://github.com/sunblaze-ucb/Virgo/blob/master/tests/lanczos/build.sh)

Thanks for their effort in generating these circuits, this saves us a ton of time.

# Virgo ZK reference implementation

[Virgo](https://eprint.iacr.org/2019/1482) is a doubly-efficient (meaning,
for both the prover and the verifier) zkSNARK.

This repo will help you to run all tests that performed in the paper.


## Prerequisites ##

On Debian based systems, you can run the following command:

    ./setup.sh
    
This script will change your default clang compiler to clang-7.

Or:

    apt update
    apt -y install cmake make git clang++-7 libgmp-dev g++ parallel

In other words, you'll need a C++11-compatible compiler (we use clang-7) (g++ 5, 6, or 7 will work).

## Building ##

The top-level Makefile in this directory will build everything below. Just run

    cmake .
    make -j4        # for example

## Testing ##
### Lanczos
    cd tests/lanczos
    python build.py
    python run.py

### Matmul
    cd tests/matmul
    python build.py
    python run.py

### SHA256
    cd tests/SHA256
    python build.py
    python run.py

use `sudo` if necessary.

## Known issue

Due to optimizations to the system, we cannot process small witness(input). We will pad the input to appropriate size. This will slow down on small instances and produce different result compared to the paper. Large instance remains the same.
