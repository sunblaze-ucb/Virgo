#!/bin/bash
# Script to setup environment
sudo apt update
sudo apt -y cmake install make git clang++-7 libgmp-dev g++ parallel
sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-7 1000
