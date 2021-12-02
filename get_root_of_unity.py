mod = 21888242871839275222246405745257275088548364400416034343698204186575808495617

def fastpow(x, exp):
    ret = 1
    tmp = x
    while(exp):
        if(exp % 2 == 1):
            ret = ret * tmp % mod
        tmp = tmp * tmp % mod
        exp >>= 1
    return ret

n = 2 ** 28
p = (mod - 1) // n
assert((mod - 1) % n == 0)
import random
answer = -1
while(True):
    x = random.randint(0, mod)
    if(fastpow(fastpow(x, p), n) == 1):
        print(fastpow(x, p))
        answer = fastpow(x, p)
        break

x = answer
for i in range(29):
    print(i, x)
    x = x * x % mod

    

