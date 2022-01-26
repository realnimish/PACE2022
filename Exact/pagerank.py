import random


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
        curr = {node: random.random() for node in self.graph}
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
