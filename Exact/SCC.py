'''
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
'''

from collections import defaultdict as ddict
from itertools import combinations

class Graph:
	def __init__(self, N, M):
		self.graph = dict()
		self.N = N
		self.M = M

	# Adds edge u -> v
	def add_edge(self, u, v):
		if u not in self.graph: self.graph[u] = set()
		if v not in self.graph: self.graph[v] = set()
		self.graph[u].add(v)

	# @param nodes -> set(nodes)
	def remove_nodes(self, nodes):
		for node in nodes:
			self.graph.pop(node,None)

		for node in self.graph:
			self.graph[node].difference_update(nodes)

	def remove_sink_nodes(self):
		while True:
			sink_nodes = set()
			for node in self.graph:
				if len(self.graph[node])==0:
					sink_nodes.add(node)
			if not sink_nodes: break
			self.remove_nodes(sink_nodes)

	# @param nodes: set(nodes)
	def get_induced_subgraph(self,nodes):
	    G = Graph(len(nodes),None)
	    for node in nodes:
	        G.graph[node] = self.graph[node]&nodes
	    G.M = sum(map(len,G.graph.values())) # counts number of edges
	    return G

	def copy(self):
		G = Graph(self.N,self.M)
		for node in self.graph:
			G.graph[node] = set(self.graph[node])
		return G

	def is_DAG(self):
		def dfs(node):
			vis[node] = True
			marked.add(node)
			for ch in self.graph[node]:
				if ch in marked or dfs(ch):
					return True
			return False

		vis = {node: False for node in self.graph}
		marked = set()
		for node in self.graph:
			marked = set()
			if vis[node]==False and dfs(node):
				return True
		return False

	def is_FVS(self, nodes):
		G = self.copy()
		G.remove_nodes(nodes)
		return not G.is_DAG()

	def get_transpose(self):
		G = Graph(self.N,self.M)

		for node in self.graph:
			for ch in self.graph[node]:
				G.add_edge(ch,node)
		return G

	def get_SCC(self):
		def fill(node):
			vis[node] = True
			for ch in self.graph[node]:
				if not vis[ch]: fill(ch)
			stack.append(node)

		def dfs(node, grp):
			vis[node] = True
			grp.add(node)

			for ch in Gt.graph[node]:
				if not vis[ch]: dfs(ch,grp)
			
		stack = []
		vis = ddict(bool)

		for node in self.graph:
			if not vis[node]: fill(node)

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
		def find_fvs(nodes,sz):
			for rem_nodes in combinations(nodes,sz):
				rem_nodes = set(rem_nodes)
				if self.is_FVS(rem_nodes):
					return rem_nodes
			return None
		
		# if not self.is_DAG(): return set()
		nodes = self.graph.keys()
		
		lo,hi = 0,len(nodes)-1
		sol = None

		while lo<hi:
			mid1 = lo + (hi-lo)//3
			mid2 = hi - (hi-lo)//3

			# Solve left
			fvs1 = find_fvs(nodes,mid1)

			if fvs1 != None:
				sol = fvs1
				hi = mid1-1  # No need to check mid2 now
				continue
			else:
				lo = mid1+1

			# Solve right
			fvs2 = find_fvs(nodes,mid2)

			if fvs2 != None:
				sol = fvs2
				hi = mid2-1
			else:
				lo = mid2+1  # No need to check mid1 now

		return find_fvs(nodes,lo) if lo==hi else sol
					

def read_graph(): # Main Graph (nodes := 1,2,3,....)
	def read_data():
		is_comment = lambda x: len(x)>0 and x[0]=='%'
		inp = '%'
		while is_comment(inp): inp = input()
		return map(int,inp.split())

	n, m, _ = read_data()
	G = Graph(n,m)

	for u in range(1,n+1):
		nei = read_data()
		for v in nei: G.add_edge(u,v)
	return G

def find_solution(G):
	scc = G.get_SCC()
	sol = set()
	for _set in scc:
		if len(_set)<3: continue
		sol |= G.get_induced_subgraph(_set).get_FVS()
	return sol

def print_solution(sol, DEBG=True):
	if DEBG:
		print('Minimum nodes to remove = ', len(sol))
		print('Removed nodes = ', sol)
	else:
		print('\n'.join(map(str,sol)))
		
if __name__ == "__main__":
	G = read_graph()
	sol = find_solution(G)
	print_solution(sol,False)