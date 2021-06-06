import os


p_time = []
v_time = []
proof_size = []
N = 21

for i in range(10, N):
    os.system('./bfc ' + str(i + 1) + ' ' + str(i))
    os.system('./zk_proof fft.txt fft_meta.txt log' + str(i) + '.txt ' + str(i + 1) + ' ' + str(i))
    f = open('log' + str(i) + '.txt')

    lines = f.readlines()
    p, v, ps = lines[0].split(' ')
    p_time.append(p)
    v_time.append(v)
    proof_size.append(int(str(ps)))


lines = ['', '', '']


for i in range(10, N):
    lines[0] = lines[0] + ' ' + str(p_time[i - 10])
    lines[1] = lines[1] + ' ' + str(v_time[i - 10])
    lines[2] = lines[2] + ' ' + str(proof_size[i - 10])

print(lines[0])
print(lines[1])
print(lines[2])

