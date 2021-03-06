"""
Let u<->v denote they both are reachable from the other.
Let u</>v denote both are not reachable from the other.

Lemma 1) if u</>v then they are independent from each other i.e. removing
one won't affect the cyclicity of the other node.

Lemma 2) u<->v && v<->w => u<->w (Strongly Connected Component)

So from Lemma 1&2, We can divide the nodes into MECE SCCs subsets.
And for each subset, We get its induced subgraph and solve them independently!

Improvement over brute_force ->

brute_force = O*(2^n)
this = O*(2^s1 + 2^s2 + ... + 2^sx) where s1+s2+..+sx = n
"""

from collections import defaultdict as ddict
from itertools import combinations


class Graph:
    def __init__(self, N, M):
        self.graph = dict()
        self.N = N  # Number of Nodes
        self.M = M  # Number of Edges

    def get_all_nodes(self):
        nodes = set()
        for node in self.graph:
            nodes.add(node)
            nodes |= self.graph[node]
        return nodes
        
    # Adds edge u -> v
    def add_edge(self, u, v):
        if u not in self.graph:
            self.graph[u] = set()
        if v not in self.graph:
            self.graph[v] = set()
        self.graph[u].add(v)

    # @param nodes -> set(nodes)
    def remove_nodes(self, nodes):
        for node in nodes:
            self.graph.pop(node, None)

        for node in self.graph:
            self.graph[node].difference_update(nodes)

    def remove_sink_nodes(self):
        while True:
            sink_nodes = set()
            for node in self.graph:
                if len(self.graph[node]) == 0:
                    sink_nodes.add(node)
            if not sink_nodes:
                break
            self.remove_nodes(sink_nodes)

    # @param nodes: set(nodes)
    # @returns G: Graph
    def get_induced_subgraph(self, nodes):
        G = Graph(len(nodes), None)
        for node in nodes:
            G.graph[node] = self.graph[node] & nodes
        G.M = sum(map(len, G.graph.values()))  # counts number of edges
        return G

    # Deepcopy the graph
    def copy(self):
        G = Graph(self.N, self.M)
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

    def get_transpose(self):
        G = Graph(self.N, self.M)
        G.graph = {node:set() for node in self.get_all_nodes()}

        for node in self.graph:
            for ch in self.graph[node]:
                G.add_edge(ch, node)
        return G

    # @returns list of set where each set correspond to SCC
    def get_SCC(self):
        def fill(node):
            vis[node] = True
            for ch in self.graph[node]:
                if not vis[ch]:
                    fill(ch)
            stack.append(node)

        def dfs(node, grp):
            vis[node] = True
            grp.add(node)

            for ch in Gt.graph[node]:
                if not vis[ch]:
                    dfs(ch, grp)

        stack = []
        vis = ddict(bool)

        for node in self.graph:
            if not vis[node]:
                fill(node)

        Gt = self.get_transpose()
        vis = ddict(bool)

        scc = []
        while stack:
            node = stack.pop()
            if not vis[node]:
                _set = set()
                dfs(node, _set)
                scc.append(_set)
        return scc

    def get_FVS(self):
        def find_fvs(nodes, sz): # Finds FVS of size sz if exists
            for rem_nodes in combinations(nodes, sz):
                rem_nodes = set(rem_nodes)
                if self.is_FVS(rem_nodes):
                    return rem_nodes
            return None

        def decide_side():  
            # Some heuristic to prefer order of eval
            # of ternary search for general optimisation
            return "LEFT"

        def solve_side(lo, hi, mid):
            # Checks if FVS exists for size=mid
            # Updates the constraints based on the outcome
            fvs = find_fvs(nodes, mid)
            if fvs != None:
                hi = mid - 1
            else:
                lo = mid + 1
            return lo, hi, fvs

        # if not self.is_DAG(): return set()
        nodes = self.graph.keys()

        lo, hi = 0, len(nodes) - 1
        sol = None

        while lo < hi:
            mid1 = lo + (hi - lo) // 3
            mid2 = hi - (hi - lo) // 3

            if decide_side() == "LEFT":
                lo, hi, fvs = solve_side(lo, hi, mid1)
                if fvs == None:  # Solution doesn't exist
                    lo, hi, fvs = solve_side(lo, hi, mid2)
            else:
                lo, hi, fvs = solve_side(lo, hi, mid2)
                if fvs != None:  # Solution exists
                    sol = fvs
                    lo, hi, fvs = solve_side(lo, hi, mid1)

            if fvs != None:
                sol = fvs

        if lo == hi:
            fvs = find_fvs(nodes, lo)
            if fvs != None:
                sol = fvs
        return sol


def read_graph():
    def read_data(): # Helper function to read the graph based on PACE input format
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


def find_solution(G):
    scc = G.get_SCC()
    sol = set()
    for _set in scc:
        if len(_set) < 2:
            continue
        sol |= G.get_induced_subgraph(_set).get_FVS()
    return sol


def print_solution(sol, DEBG=False):
    if DEBG:
        print("Minimum nodes to remove = ", len(sol))
    else:
        print("\n".join(map(str, sol)))


if __name__ == "__main__":
    G = read_graph()
    sol = find_solution(G)
    print_solution(sol)
