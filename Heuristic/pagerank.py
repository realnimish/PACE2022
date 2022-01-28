from random import random
from collections import defaultdict as ddict
from itertools import combinations

from sys import setrecursionlimit as srl 
srl(10**5)

class Graph:
    def __init__(self, N, M):
        self.graph = dict()
        self.N = N
        self.M = M

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
    def get_induced_subgraph(self, nodes):
        G = Graph(len(nodes), None)
        for node in nodes:
            G.graph[node] = self.graph[node] & nodes
        G.M = sum(map(len, G.graph.values()))  # counts number of edges
        return G

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
        scc = self.get_SCC()
        fvs = set()

        for _set in scc:
            if len(_set) < 2: 
                continue

            subgraph = self.get_induced_subgraph(_set)
            critical_nodes = subgraph.get_critical_nodes()
            fvs |= critical_nodes
            subgraph.remove_nodes(critical_nodes)
            fvs |= subgraph.get_FVS()
        return fvs

    def get_critical_nodes(self):
        if self.is_DAG(): return set()

        pr = self.pagerank()
        critical = None 

        for node in pr:
            if critical is None:
                critical = node
            elif pr[node] > pr[critical]:
                critical = node 
        return {critical,}

    def pagerank(self, beta=0.85, epsilon=1e-6, itr=100, rand=False):
        """
        beta - damping factor
        itr - no. of iterations
        epsilon - to check for convergence
        rand - randomly initialize the probability of each node
        Time Complexity - O(itr*(V + E)) (if there are no sink nodes in Graph)
        """
        N = len(self.graph)
        curr = {}

        # uniform probability distribution
        if not rand:
            curr = {node: 1 / N for node in self.graph}
        else:
            curr = {node: random() for node in self.graph}
            sm = sum(curr.values())
            curr = {k: v / sm for k, v in curr.items()}  # normalize the vector

        for _ in range(itr):

            # initialize the next distribution with (1-beta)/n to prevent spider trap
            nxt = {node: (1 - beta) / N for node in self.graph}

            for node in self.graph:
                for ch in self.graph[node]:
                    nxt[ch] += beta * (curr[node] / len(self.graph[node]))

                # Distribute value of sink nodes among all other nodes
                if len(self.graph[node]) == 0:
                    for x in self.graph:
                        nxt[x] += beta * (curr[node] / N)
            # if converge then return
            if all(abs(curr[node] - nxt[node]) < epsilon for node in self.graph):
                return nxt
            curr = nxt
        return curr

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

def print_solution(G, sol, DEBG=True):
    if DEBG:
        print("Is FVS?", G.is_FVS(sol))
        print("Minimum nodes to remove = ", len(sol))
        #print("Removed nodes = ", sol)
    else:
        print("\n".join(map(str, sol)))


if __name__ == "__main__":
    G = read_graph()
    sol = G.get_FVS()
    print_solution(G,sol)

