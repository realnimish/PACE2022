from random import random
from collections import defaultdict as ddict
from itertools import combinations

from sys import setrecursionlimit as srl 
srl(10**7)

class Graph:
    def __init__(self, N, M):
        self.graph = dict()
        self.N = N  # Number of Nodes
        self.M = M  # Number of Edges
        self.indegree = dict()  # Number of incoming edges

    def get_all_nodes(self):
        nodes = set()
        for node in self.graph:
            nodes.add(node)
            nodes |= self.graph[node]
        return nodes
        
    # Returns count of incoming,outgoing edges
    def node_degree(self, node):
        _in = self.indegree.get(node,0)
        _out = len(self.graph.get(node,[]))
        return _in, _out

    # Adds edge u -> v
    def add_edge(self, u, v):
        if u not in self.graph:
            self.graph[u] = set()
            self.indegree[u] = 0
        if v not in self.graph:
            self.graph[v] = set()
            self.indegree = 0

        self.graph[u].add(v)
        self.indegree[v] += 1

    # @param nodes -> set(nodes)
    def remove_nodes(self, nodes):
        for node in nodes:
            nei = self.graph.pop(node, None)
            if nei is not None:
                self.N -= 1
                self.M -= len(nei)
                self.indegree.pop(node)

        for node in self.graph:
            sz1 = len(self.graph[node])
            self.graph[node].difference_update(nodes)
            sz2 = len(self.graph[node])
            self.M -= (sz1 - sz2)

    def remove_sink_nodes(self):
        while True:
            sink_nodes = set()
            for node in self.graph:
                if len(self.graph[node]) == 0:
                    sink_nodes.add(node)
            if not sink_nodes:
                break
            self.remove_nodes(sink_nodes)

    def compute_indegree(self):
        self.indegree = dict()

        for node in self.graph:
            if node not in self.indegree:
                self.indegree[node] = 0
            for nei in self.graph[node]:
                self.indegree[nei] = 1 + self.indegree.get(nei,0)

    # @param nodes: set(nodes)
    # @returns G: Graph
    def get_induced_subgraph(self, nodes):
        G = Graph(len(nodes), None)
        for node in nodes:
            G.graph[node] = self.graph[node] & nodes
        G.M = sum(map(len, G.graph.values()))  # counts number of edges
        G.compute_indegree()
        return G

    # Deepcopy the graph
    def copy(self):
        G = Graph(self.N, self.M)
        for node in self.graph:
            G.graph[node] = set(self.graph[node])
            G.indegree[node] = self.indegree[node]
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
 
    # Uses ../Exact/SCC solution
    def get_FVS_Exact(self, method = "linear"):
        def find_fvs(nodes, sz): # Finds FVS of size sz if exists
            for rem_nodes in combinations(nodes, sz):
                rem_nodes = set(rem_nodes)
                if self.is_FVS(rem_nodes):
                    return rem_nodes
            return None

        def ternary_search():
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

        def linear_search():
            nodes = self.graph.keys()
            fvs,sz = None, 0

            while fvs is None:
                fvs = find_fvs(nodes,sz)
                sz += 1
            return fvs
                
        if method == "linear":
            return linear_search()
        else:
            return ternary_search()

    def get_FVS_Heuristic(self):
        critical_nodes = self.get_critical_nodes()
        self.remove_nodes(critical_nodes)
        return critical_nodes | self.get_FVS()

    # Heurisitic to determine the method to find FVS for self
    def decide_approach(self):
        if self.N < 20:
            return "Exact"
        else:
            return "Heuristic"

    # Finds the FVS for the given graph
    def get_FVS(self):
        scc = self.get_SCC()
        fvs = set()

        for _set in scc:
            if len(_set) < 2: 
                continue

            subgraph = self.get_induced_subgraph(_set)
            if subgraph.decide_approach() == "Exact":
                fvs |= subgraph.get_FVS_Exact()
            else:
                fvs |= subgraph.get_FVS_Heuristic()
        return fvs

    # Heuristic to find the set of nodes that should be removed
    def get_critical_nodes(self):
        """
            Approach:
            Select the highest weighted node based on Pagerank algorithm
        """
                    
        if self.is_DAG(): return set()

        pr = self.pagerank(itr=1000)
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

def read_graph():
    def read_data():    # Helper function to read the graph based on PACE input format
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

def print_solution(G, sol, DEBG=False):
    if DEBG:
        print("Is FVS?", G.is_FVS(sol))
        print("Minimum nodes to remove = ", len(sol))
    else:
        print("\n".join(map(str, sol)))


if __name__ == "__main__":
    G = read_graph()
    sol = G.get_FVS()
    print_solution(G,sol)