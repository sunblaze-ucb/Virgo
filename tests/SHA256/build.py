import os
#os.system('./build.sh')
#os.system('g++ parser_sha_data_parallel.cpp -std=c++11 -o psdp -O3')
#for i in range(8):
#	os.system('./psdp SHA256_64.pws SHA256_64_merkle_' + str(i + 1) + '_rdl.pws SHA256_64_merkle_' + str(i + 1) + '_circuit.txt SHA256_64_merkle_' + str(i + 1) + '_meta.txt')

os.system('cmake ../..')
os.system('make -C ../.. zk_proof')
#os.system('make -C ../.. fft_gkr')
os.system('mv ../../zk_proof .')
#os.system('mv ../../fft_gkr .')
