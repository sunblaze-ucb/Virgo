import os

n = [16, 32, 64, 128, 256]

os.system('g++ gen.cpp -o gen -O3')

for xn in n:
	os.system('./gen ' + str(xn) + ' mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt' + ' wit_' + str(xn) + ' ' + str(4))

os.system('make -C ../.. distributed_proof')
os.system('mv ../../distributed_proof .')
