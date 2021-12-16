import os
os.system('mkdir -p LOG')
#n = [16, 32, 64, 128]
n = [16]
for xn in n:
    print('mpirun -np 4 distributed_proof mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt LOG/mat_' + str(xn) + '.txt' + ' wit_' + str(xn))
    os.system('mpirun -np 4 distributed_proof mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt LOG/mat_' + str(xn) + '.txt' + ' wit_' + str(xn))
