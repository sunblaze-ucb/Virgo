import os
os.system('mkdir -p LOG')
for i in range(8):
	os.system('./zk_proof SHA256_64_merkle_' + str(i + 1) + '_circuit.txt SHA256_64_merkle_' + str(i + 1) + '_meta.txt LOG/SHA256_' + str(i + 1) + '.txt')
