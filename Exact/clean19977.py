# %%
import networkx as nx

# %%
def contractGraphNode(G, v):

    Gn = nx.DiGraph(G)

    e = G.in_edges(v)
    en = set([i[0] for i in e])

    l = G.out_edges(v)
    ln = set([i[1] for i in l])

    com = set(en) & set(ln)

    # Delete the loop vertex.
    for c in com:
        Gn.remove_node(c)
        en.remove(c)
        ln.remove(c)

    for j in en:
        for k in ln:
            Gn.add_edge(j, k)

    Gn.remove_node(v)

    return Gn


# %%
def contractGraph(G, D):

    if type(D) == type(3):
        return contractGraphNode(G, D)

    elif len(D) == 0:
        return G

    else:
        t = D.pop()
        return contractGraph(contractGraphNode(G, t), D)


# %%
def V_L(G, R):
    t = set()

    for v in G.nodes():
        if R[v] == "LM" or R[v] == "LMD":
            t.add(v)

    return t


def V_R(G, R):
    t = set()

    for v in G.nodes():
        if R[v] == "RM" or R[v] == "RMD":
            t.add(v)

    return t


# %%
def convertArb(R, F, N):
    for j in range(N):
        if F == "VR":
            for key in R:
                if R[key] == "RM" or R[key] == "RMD":
                    R[key] = "WRM"
                    break

        elif F == "VL":
            for key in R:
                if R[key] == "LM" or R[key] == "LMD":
                    R[key] = "WLM"
                    break


# %%
def balance(G, R):

    lenL = len(V_L(G, R))
    lenR = len(V_R(G, R))

    if lenR - lenL > 3:
        convertArb(R, "VR", lenR - lenL - 3)
    elif lenL - lenR > 3:
        convertArb(R, "VL", lenL - lenR - 3)


# %%
def checkcycle2(G):
    # Return any vertex of the first cycle of length 2.
    for v in list(G.nodes):
        l = G.out_edges(v)
        ln = [i[1] for i in l]

        for u in ln:
            l1 = G.out_edges(u)
            l1n = [i[1] for i in l1]

            if v in l1n:
                # Can return v or u here.
                return v

    return -1


# %%
def powerset(s):
    x = len(s)
    masks = [1 << i for i in range(x)]
    for i in range(1 << x):
        yield set([ss for mask, ss in zip(masks, s) if i & mask])


# %%
def getAcyclicSubsets(G, s):
    # Returns a list of sets, containing all the acyclic subsets of the set s.

    allsets = list(powerset(s))

    for sub in allsets:
        if len(sub) == 0 or len(sub) == 1:
            continue

        G1 = G.subgraph(list(sub))

        try:
            nx.find_cycle(G1)
            allsets.remove(sub)
        except:
            pass

    return allsets


# %%
def GetMAS(G, R):
    # Returns set of vertices which form the MAS, ie. complement of FVS.

    # Balancing.
    balance(G, R)

    # C1
    # Return the MAS directly and return it.

    l = list(G.nodes)

    if len(l) == 1 or len(l) == 0:
        return set(G.nodes)

    elif len(l) == 2:
        try:

            nx.find_cycle(G)
            return set([list(G.nodes)[0]])
        except Exception as e:
            return set(G.nodes)

    elif len(l) == 3:
        try:
            nx.find_cycle(G)

            ps = list(powerset(l))
            for s in ps:
                if len(s) == 2:
                    Gm = G.subgraph(list(s))
                    try:
                        nx.find_cycle(Gm)
                    except:
                        return s

            for s in ps:
                if len(s) == 1:
                    return s
        except:
            return set(G.nodes)

    # C2

    t = checkcycle2(G)
    if t != -1:

        if R[t] == "UM":

            R1 = R.copy()
        elif R[t] == "LM" or R[t] == "LMD" or R[t] == "WLM":

            R1 = R.copy()
            e = G.in_edges(t)
            en = [i[0] for i in e]

            for k in en:
                if R[k] == "UM":
                    R1[k] = "WLM"

        elif R[t] == "RM" or R[t] == "RMD" or R[t] == "WRM":

            R1 = R.copy()
            l = G.out_edges(t)
            ln = [i[1] for i in l]

            for k in ln:
                if R[k] == "UM":
                    R1[k] == "WRM"

        G1 = nx.DiGraph(G)
        G1.remove_node(t)
        S1 = GetMAS(G1, R)
        S2 = GetMAS(contractGraph(G, t), R1) | set([t])

        if len(S1) > len(S2):
            return S1
        else:
            return S2

    # C3

    allscc = list(nx.strongly_connected_components(G))

    if len(allscc) >= 2:
        # G1 and G2 are the SCC components.
        G1 = G.subgraph(list(allscc[0]))
        G2 = G.subgraph(list(allscc[1]))

        v1 = list(G1.nodes)[0]
        v2 = list(G2.nodes)[0]

        for i in list(G1.nodes):
            if R[i] == "LMD" or R[i] == "RMD":
                v1 = i
                break

        for i in list(G2.nodes):
            if R[i] == "LMD" or R[i] == "RMD":
                v2 = i
                break

        t1 = set([v1, v2]) | GetMAS(contractGraph(G, set([v1, v2])), R)
        rl = list(G.nodes)
        rl.remove(v1)
        rl.remove(v2)
        t2 = GetMAS(G.subgraph(rl), R)

        x1 = t1 & set(G1.nodes)
        x2 = t2 & set(G1.nodes)
        if len(x1) > len(x2):
            xm = x1
        else:
            xm = x2

        y1 = t1 & set(G2.nodes)
        y2 = t2 & set(G2.nodes)

        if len(y1) > len(y2):
            ym = y1
        else:
            ym = y2

        z1 = set(G1.nodes) | set(G2.nodes)
        z = t1 - z1

        b = xm | ym | z

        return b

    # C4

    if len(V_L(G, R)) == 0 or len(V_R(G, R)) == 0:
        # C41
        for v in list(G.nodes):
            if R[v] == "UM" or R[v] == "WLM" or R[v] == "WRM":
                e = G.in_edges(v)
                en = [i[0] for i in e]
                l = G.out_edges(v)
                ln = [i[1] for i in l]

                if len(en) == 0:
                    return set([v]) | GetMAS(contractGraph(G, v), R)

                elif len(en) == 1:
                    rl = list(G.nodes)
                    rl.remove(v)
                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R),
                        set([en[0]]) | GetMAS(contractGraph(G.subgraph(rl), en[0]), R),
                        key=len,
                    )

                elif len(en) == 2:
                    rl = list(G.nodes)
                    rl.remove(v)
                    r1 = rl.copy()
                    rl.remove(en[0])
                    r2 = rl.copy()
                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R),
                        set([en[0]]) | GetMAS(contractGraph(G.subgraph(r1), en[0]), R),
                        set([en[1]]) | GetMAS(contractGraph(G.subgraph(r2), en[1]), R),
                        key=len,
                    )

                elif len(en) == 3:
                    # print("en = 3")
                    rl = list(G.nodes)
                    rl.remove(v)
                    r1 = rl.copy()
                    rl.remove(en[0])
                    r2 = rl.copy()
                    rl.remove(en[1])
                    r3 = rl.copy()

                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R),
                        set([en[0]]) | GetMAS(contractGraph(G.subgraph(r1), en[0]), R),
                        set([en[1]]) | GetMAS(contractGraph(G.subgraph(r2), en[1]), R),
                        set([en[2]]) | GetMAS(contractGraph(G.subgraph(r3), en[2]), R),
                        key=len,
                    )

                elif len(ln) == 0:
                    return set([v]) | GetMAS(contractGraph(G, v), R)

                elif len(ln) == 1:
                    rl = list(G.nodes)
                    rl.remove(v)
                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R),
                        set([ln[0]]) | GetMAS(contractGraph(G.subgraph(rl), ln[0]), R),
                        key=len,
                    )

                elif len(ln) == 2:
                    rl = list(G.nodes)
                    rl.remove(v)
                    r1 = rl.copy()
                    rl.remove(ln[0])
                    r2 = rl.copy()
                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R),
                        set([ln[0]]) | GetMAS(contractGraph(G.subgraph(r1), ln[0]), R),
                        set([ln[1]]) | GetMAS(contractGraph(G.subgraph(r2), ln[1]), R),
                        key=len,
                    )

                elif len(ln) == 3:
                    rl = list(G.nodes)
                    rl.remove(v)
                    r1 = rl.copy()
                    rl.remove(ln[0])
                    r2 = rl.copy()
                    rl.remove(ln[1])
                    r3 = rl.copy()
                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R),
                        set([ln[0]]) | GetMAS(contractGraph(G.subgraph(r1), ln[0]), R),
                        set([ln[1]]) | GetMAS(contractGraph(G.subgraph(r2), ln[1]), R),
                        set([ln[2]]) | GetMAS(contractGraph(G.subgraph(r3), ln[2]), R),
                        key=len,
                    )

        # C42
        for v in list(G.nodes):
            if R[v] == "UM" or R[v] == "WLM" or R[v] == "WRM":
                R1 = R.copy()

                e = G.in_edges(v)
                en = [i[0] for i in e]
                l = G.out_edges(v)
                ln = [i[1] for i in l]

                tok = 4
                for i in en:
                    if tok != 0:
                        R1[i] = "LM"
                        tok = tok - 1
                    else:
                        R1[i] = "WLM"
                tok = 4
                for i in ln:
                    if tok != 0:
                        R1[i] = "RM"
                        tok = tok - 1
                    else:
                        R1[i] = "WRM"

                rl = list(G.nodes)
                rl.remove(v)

                return max(
                    set([v]) | GetMAS(contractGraph(G, v), R1),
                    GetMAS(G.subgraph(rl)),
                    key=len,
                )

        R1 = R.copy()

        e = G.in_edges(v)
        en = [i[0] for i in e]
        l = G.out_edges(v)
        ln = [i[1] for i in l]

        tok = 4
        for i in en:
            if tok != 0:
                R1[i] = "LM"
                tok = tok - 1
            else:
                R1[i] = "WLM"
        tok = 4
        for i in ln:
            if tok != 0:
                R1[i] = "RM"
                tok = tok - 1
            else:
                R1[i] = "WRM"

        rl = list(G.nodes)
        rl.remove(v)

        return max(
            set([v]) | GetMAS(contractGraph(G, v), R1), GetMAS(G.subgraph(rl)), key=len
        )

    # C5

    lenL = len(V_L(G, R))
    lenR = len(V_R(G, R))

    # For the first part.
    if lenL < lenR:

        # C51 not needed.
        # C52
        for v in list(G.nodes):
            if R[v] == "LM" or R[v] == "LMD":
                e = G.in_edges(v)
                en = [i[0] for i in e]

                uen = [i for i in en if R[i] == "UM"]

                if len(uen) >= 4:
                    R1 = R.copy()
                    tok = 4
                    for j in uen:
                        if tok != 0:
                            R1[j] = "LM"
                            tok = tok - 1
                        else:
                            R1[j] = "WLM"

                    rl = list(G.nodes)
                    rl.remove(v)

                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R1),
                        GetMAS(G.subgraph(rl), R),
                        key=len,
                    )

        # C53
        ue = []
        v = 0
        for vt in list(G.nodes):
            e = G.in_edges(vt)
            en = [i[0] for i in e]

            uet = [i for i in en if R[i] == "UM"]

            if len(uet) > len(ue):
                ue = uet
                v = vt

        # ue is X.
        # Ys is a set of all Y.
        Ys = getAcyclicSubsets(G, ue)
        Ty = []

        for Y in Ys:
            Rt = R.copy()
            if len(Y) == 0:
                Rt[v] = "LMD"

            temp = Y | GetMAS(contractGraph(G.subgraph(list(ue - Y)), Y), Rt)
            Ty.append(temp)

        return max(Ty, key=lambda item: len(item))

    # For the second part.
    else:
        # C51 not needed.
        # C52
        for v in list(G.nodes):
            if R[v] == "RM" or R[v] == "RMD":
                l = G.out_edges(v)
                ln = [i[1] for i in l]

                uln = [i for i in ln if R[i] == "UM"]

                if len(uln) >= 4:
                    R1 = R.copy()
                    tok = 4
                    for j in uln:
                        if tok != 0:
                            R1[j] = "RM"
                            tok = tok - 1
                        else:
                            R1[j] = "WRM"

                    rl = list(G.nodes)
                    rl.remove(v)

                    return max(
                        set([v]) | GetMAS(contractGraph(G, v), R1),
                        GetMAS(G.subgraph(rl), R),
                        key=len,
                    )

        # C53
        ul = []
        v = 0
        for vt in list(G.nodes):
            l = G.out_edges(vt)
            ln = [i[1] for i in l]

            ult = [i for i in ln if R[i] == "UM"]

            if len(ult) > len(ul):
                # ul = ult.copy()
                ul = ult
                v = vt

        Ys = getAcyclicSubsets(G, v)
        Ty = []

        for Y in Ys:
            Rt = R.copy()
            if len(Y) == 0:
                Rt[v] = "RMD"

            temp = Y | GetMAS(contractGraph(G.subgraph(list(ul - Y)), Y), Rt)
            Ty.append(temp)

        return max(Ty, key=lambda item: len(item))


# %%
def GetFVS(G):
    V = set(G.nodes)

    R = {}

    for v in list(G.nodes()):
        R[v] = "UM"

    MAS = GetMAS(G, R)
    FVS = V - MAS

    return FVS


# %%
def read_graph():
    def read_data():    # Helper function to read the graph based on PACE input format
        is_comment = lambda x: len(x) > 0 and x[0] == "%"
        inp = "%"
        while is_comment(inp):
            inp = input()
        return map(int, inp.split())

    n, m, _ = read_data()
    # G = Graph(n, m)
    G = nx.DiGraph()
    edges = []
    for u in range(1, n + 1):
        nei = read_data()
        for v in nei:
            edges.append((u,v))
    G.add_edges_from(edges)
    return G

def print_solution(G, sol, DEBG=False):
    if DEBG:
        # print("Is FVS?", G.is_FVS(sol))
        print("Minimum nodes to remove = ", len(sol))
    else:
        print("\n".join(map(str, sol)))

if __name__ == "__main__":
    G = read_graph()
    fvs = GetFVS(G)
    print_solution(G,fvs)
