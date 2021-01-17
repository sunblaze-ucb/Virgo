# Virgo ZK reference implementation

[Virgo](https://eprint.iacr.org/2019/1482) is a doubly-efficient (meaning,
for both the prover and the verifier) zkSNARK.

This repo will help you to run all tests that performed in the paper.

# Acknowledgement

Our benchmarks use the SHA256 circuit generator and LANCZOS circuit generator from Hyrax (https://github.com/hyraxZK). The files are in [/test/](https://github.com/sunblaze-ucb/Virgo/blob/master/tests/). The files are Copyright 2017 Riad S. Wahby rsw@cs.stanford.edu and the Hyrax authors. We thank the Hyrax authors Riad S. Wahby, Ioanna Tzialla,abhi shelat, Justin Thaler and Michael Walfish for making the code open-source.

# Vector Commitment
We wrote a vector commitment library [here](https://github.com/sunblaze-ucb/Virgo/tree/master/include/poly_commitment).

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
