import os

n = [16, 32, 64, 128, 256]

os.system('g++ gen.cpp -o gen -O3')

for xn in n:
	os.system('./gen ' + str(xn) + ' mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt')

os.system('make -C ../.. zk_proof')
os.system('make -C ../.. fft_gkr')
os.system('mv ../../zk_proof .')
os.system('mv ../../fft_gkr .')
