class Graph:
    def __init__(self, N, M):
        self.graph = {u: set() for u in range(1, N + 1)}
        self.N = N
        self.M = M

    # Adds edge u -> v
    def add_edge(self, u, v):
        # if u not in self.graph:
        # 	self.graph[u] = set()
        # if v not in self.graph:
        # 	self.graph[v] = set()
        self.graph[u].add(v)

    # @param nodes -> set(nodes)
    def remove_nodes(self, nodes):
        for node in nodes:
            self.graph.pop(node)

        for node in self.graph:
            self.graph[node].difference_update(nodes)

    def copy(self):
        G = Graph(0, self.M)
        G.N = self.N
        for node in self.graph:
            G.graph[node] = set(self.graph[node])
        return G

    def is_DAG(self):
        def dfs(node):
            vis[node] = True
            marked[node] = True
            for ch in self.graph[node]:
                if marked[ch] or (vis[ch] == False and dfs(ch)):
                    return True
            marked[node] = False
            return False

        vis = {node: False for node in self.graph}
        marked = {node: False for node in self.graph}
        for node in self.graph:
            if vis[node] == False and dfs(node):
                return False
        return True

    def is_FVS(self, nodes):
        G = self.copy()
        G.remove_nodes(nodes)
        return G.is_DAG()


def read_graph():  # Main Graph (nodes := 1,2,3,....)
    def read_data():
        is_comment = lambda x: len(x) > 0 and x[0] == "%"
        inp = "%"
        while is_comment(inp):
            inp = input()
        return map(int, inp.split())

    n, m, _ = read_data()
    G = Graph(n, m)

    for u in range(1, n + 1):
        nei = read_data()
        for v in nei:
            G.add_edge(u, v)
    return G


def getSetBits(mask):
    bits = set()
    idx = 1

    while mask > 0:
        if mask & 1:
            bits.add(idx)
        idx += 1
        mask >>= 1
    return bits


def find_solution(G):
    mask, lim = 0, 1 << G.N
    sol = set(range(1, G.N + 1))

    while mask < lim:
        FVS = getSetBits(mask)
        if len(FVS) < len(sol) and G.is_FVS(FVS):
            sol = FVS
        mask += 1
    return sol


def print_solution(sol, DEBG=True):
    if DEBG:
        print("Minimum nodes to remove = ", len(sol))
        print("Removed nodes = ", sol)
    else:
        print("\n".join(map(str, sol)))


if __name__ == "__main__":
    G = read_graph()
    sol = find_solution(G)
    print_solution(sol, False)

"""
	Optimisation 1) If #nodes >= curSol: return
	Optimisation 2) Eval mask in order of #set_bits
"""
