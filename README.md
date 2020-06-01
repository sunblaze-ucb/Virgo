# Interface of the zero-knowledge system, Virgo:

## Input file and the file format
Our system is based on layered arithmatic circuit. When you want to generate the zero knowledge proof for the statement, you should tranfer it into a text file "input.txt" to represent the corresponding circuit.  

For the file format, in the first line, there is only one integer `d` represnet the depth of the circuit. Input layer has layer number `0` output layer has layer number `d-1`.

For next `d` lines, each line represents a layer.

In this first line, it specifies the input layer, the first number is `n`, which is the number of gates in this layer. Next `4n` numbers represents `n` gates. For each gate, we use 4 integers to describe: `ty gate_id value0 value1`, indicates the type of the gate, the id of the gate and the input value of the gate.

For `i`-th line, it specifies the layer `i - 1`, the first number is `n`, specifies the number of gates in this layer. `n` must be a power of `2`.
The rest of this line contains `4n` integers, represent `n` gates. For each gate, we use 4 integers to describe: `ty g u v`, indicates the type of the gate, and the connection of the gate, `g` is the gate number, `u` is the id of the left input of g in last layer, `v` is the id of the right input of g.

We have `11` different types of gates for now.

`ty=0` is addition gate[V(g) = V(u) + V(v)], `ty=1` is multiplication gate[V(g) = V(u) * V(v)], `ty=2` is dummy gate[V(g) = 0], `ty=3` is input gate[V(g) = u], `ty=4` is direct relay gate[V(g) = V(u) and g = u], `ty=5` is summation gate[V(g) = \sum_{i = u}^{v - 1}V(i)], `ty=6` is not gate[V(g) = 1 - V(u)], `ty=7` is minus gate[V(g) = V(u) - V(v)], `ty=8` is XOR gate[V(g) = V(u) & V(v)], `ty=9` is NAAB gate [V(g) = (1-V(u)) * V(v)], `ty=10` is relay gate[V(g) = V(u)], `ty=11` is not used, `ty=12` is `exp sum gate`[V(g) = \sum_{i = u}^{v}2^i * V(i)], `ty=13` is bit-test gate[V(g) = V(u)[(1-V(u)].

### Special gate explaination
#### Direct relay gate
Do not use it in the circuit description, it's a gate that we use it to simplify computation. The gate just directly copy the value from the node in previous layer which has the same label as the direct relay gate.

#### Summation gate
It's a gate that output the summation of previous layer. A simple use case is matrix multiplication.

## Examples of the input file
```
3 \\three layers
4 3 0 1 1 3 1 1 1 3 2 1 1 3 3 1 1 \\input layer("layer 0"): 4 inputs 
2 0 0 0 1 1 1 2 3 \\layer 1: the first gate is an addition gate with input wires of input 0 and input 1, and the second is a multiplication gate with input wires of input 2 and input 3.
1 1 0 0 1 \\output layer(layer 2): it's a multiplication gate with input wire of 0 and 1 in previous layer.
```

## Some tests on the system 
### Image scaling with Lanczos method
`cd tests/lanczos`

`python build.py`

`python run.py`

### Matrix multiplication: P proves to V that it knows two matrices whose product equals a public matrix.

`cd tests/matmul`

`python build.py`

`python run.py`

### Merkel tree with SHA256 hash function
`cd tests/SHA256`

`python build.py`

`python run.py`

use `sudo` if necessary.
