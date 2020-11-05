# Acknowledgement
Our benchmarks use the SHA256 circuit generator and LANCZOS circuit generator from Hyrax, here are all files that uses Hyrax code:
- SHA256/sha256gen.py
- SHA256/build.sh
- lanczos/lanczos2.py
- lanczos/build.sh

# Changes to the file
We made some changes to the SHA256/sha256gen.py, here is a brief discussion on it:

- We removed the addition tree, and replaced by a summation gate.
- We removed constant input. Especially for constants that equals to power of 2.
