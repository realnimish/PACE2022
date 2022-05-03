import math
import random
"""
	Simulated Annealing to solve FVS
	Ref: https://in.booksc.me/book/22293599/92b049
"""

def getPositionMinus(S, neigh_minus):
	for i in range(len(S)-1, -1, -1):
		if S[i] in neigh_minus:
			return i+1
	return 0

def getPositionPlus(S, neigh_plus):
	for i in range(0, len(S)):
		if S[i] in neigh_plus:
			return i
	return len(S)

def simulatedAnnealing(G, T0=0.6, alpha=0.99, mvtFactor=5, maxFail=50, randomSeed=None):
	nNodes = len(G)

	T = T0
	nbFail = 0
	S = []
	S_optimal = []
	maxMvt = mvtFactor * nNodes
	random.seed(randomSeed)

	parent = [set() for i in range(nNodes)]
	for u in range(1, nNodes):
		for v in G[u]:
			parent[v].add(u)

	unnumbered = [i for i in range(1, nNodes)]

	while(nbFail < maxFail):
		nbMvt = 0
		failure = True
		while(nbMvt < maxMvt):
			v_index = random.randint(0, len(unnumbered)-1)
			v = unnumbered[v_index]
			b = random.randint(0, 1)

			neigh_minus = parent[v] # Incoming Edges
			neigh_plus = G[v]       # Outgoing Egdes

			position = getPositionMinus(S, neigh_minus) if b == 0 else getPositionPlus(S, neigh_plus)
			S_copy = S[:]
			S_copy.insert(position, v)

			conflict = []
			if b == 0:
				for i in range(position):
					if S_copy[i] in neigh_plus:
						conflict.append(S_copy[i])
			else:
				for i in range(position+1, len(S_copy)):
					if S_copy[i] in neigh_minus:
						conflict.append(S_copy[i])

			for x in conflict:
				S_copy.remove(x)

			delta = len(conflict) - 1
			if delta <= 0 or math.exp(-delta/T) >= random.random():
				S = S_copy
				unnumbered.remove(v)
				for x in conflict:
					unnumbered.append(x)
				nbMvt += 1
				if len(S) > len(S_optimal):
					S_optimal = S[:]
					failure = False
		if failure == True:
			nbFail += 1
		else:
			nbFail = 0
		T = alpha * T
	return S_optimal


def readGraph():
	def read_data():
		is_comment = lambda x: len(x) > 0 and x[0] == "%"
		inp = "%"
		while is_comment(inp):
			inp = input()
		return map(int, inp.split())

	n, m, _ = read_data()
	G = [set() for i in range(n+1)]

	for u in range(1, n+1):
		nei = read_data()
		for v in nei:
			G[u].add(v)
	return G


if __name__ == "__main__":
	G = readGraph()
	S_optimal = simulatedAnnealing(G)
	allNodes = [i for i in range(1, len(G))]

	FVS = set(allNodes) - set(S_optimal)
	for x in FVS:
		print(x)