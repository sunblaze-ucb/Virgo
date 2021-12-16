import os
os.system('mkdir -p LOG')
os.system('./zk_proof lanczos2_112_N=16_circuit.txt lanczos2_112_N=16_meta.txt LOG/lanczos2_112_N=16.txt')
os.system('./zk_proof lanczos2_176_N=64_circuit.txt lanczos2_176_N=64_meta.txt LOG/lanczos2_176_N=64.txt')
os.system('./zk_proof lanczos2_304_N=256_circuit.txt lanczos2_304_N=256_meta.txt LOG/lanczos2_304_N=256.txt')
os.system('./zk_proof lanczos2_560_N=1024_circuit.txt lanczos2_560_N=1024_meta.txt LOG/lanczos2_560_N=1024.txt')
os.system('./zk_proof lanczos2_1072_N=4096_circuit.txt lanczos2_1072_N=4096_meta.txt LOG/lanczos2_1072_N=4096.txt')
