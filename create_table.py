import os


p_time = []
v_time = []
proof_size = []


for i in range(10, 11):
    os.system('./bfc ' + str(i + 1) + ' ' + str(i))
    os.system('./zk_proof fft.txt fft_meta.txt log' + str(i) + '.txt ' + str(i + 1) + ' ' + str(i) + '>> log' + str(i) + '.txt')
    f = open('log' + str(i) + '.txt')

    lines = f.readlines()
    print(lines)
