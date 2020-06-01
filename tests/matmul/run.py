import os
os.system('mkdir -p LOG')
n = [16, 32, 64, 128]

for xn in n:
	os.system('./zk_proof mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt LOG/mat_' + str(xn) + '.txt')
