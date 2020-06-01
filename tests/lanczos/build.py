import os
os.system('./build.sh')
os.system('g++ parser_sha_data_parallel.cpp -o psdp -O3')

os.system('./psdp lanczos2_16.pws lanczos2_16_112_N=16_rdl.pws lanczos2_112_N=16_circuit.txt lanczos2_112_N=16_meta.txt')
os.system('./psdp lanczos2_16.pws lanczos2_16_176_N=64_rdl.pws lanczos2_176_N=64_circuit.txt lanczos2_176_N=64_meta.txt')
os.system('./psdp lanczos2_16.pws lanczos2_16_304_N=256_rdl.pws lanczos2_304_N=256_circuit.txt lanczos2_304_N=256_meta.txt')
os.system('./psdp lanczos2_16.pws lanczos2_16_560_N=1024_rdl.pws lanczos2_560_N=1024_circuit.txt lanczos2_560_N=1024_meta.txt')
os.system('./psdp lanczos2_16.pws lanczos2_16_1072_N=4096_rdl.pws lanczos2_1072_N=4096_circuit.txt lanczos2_1072_N=4096_meta.txt')

os.system('make -C ../.. zk_proof')
os.system('make -C ../.. fft_gkr')
os.system('mv ../../zk_proof .')
os.system('mv ../../fft_gkr .')
