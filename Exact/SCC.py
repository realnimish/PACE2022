'''
Let u<->v denote they both are reachable from the other.
Let u</>v denote both are not reachable from the other.

Lemma 1) if u</>v then they are indepenent from each other i.e. removing
one won't affect the cyclicity of the other node.

Lemma 2) u<->v && v<->w => u<->w (Strongly Connected Component)

So from Lemma 1&2, We can divide the nodes into MECE SCCs subsets.
And for each subset, We get its induced subgraph and solve them indepenently!

Improvement over brute_force ->

brute_force = O*(2^n)
this = O*(2^s1 + 2^s2 + ... + 2^sx) where s1+s2+..+sx = n
'''

if __name__ == "__main__":
    print("To be implemented")