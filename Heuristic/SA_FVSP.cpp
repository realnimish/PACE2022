#include <iostream>
#include <sstream>
#include <vector>
#include <stack>
#include <queue>
#include <cstring>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <cmath>
#include <random>
#include <functional>
#include <assert.h>
#include <signal.h>
#include <unistd.h>

using namespace std;

enum heuristic { Pagerank, Edge_Density };

// to produce random numbers between 0 and 1
random_device rd;
mt19937 gen(rd());
uniform_real_distribution<> dis(0.0, 1.0);

volatile sig_atomic_t tle = 0;
/// SIGTERM handler
void term(int signum) {
    tle = 1;
}

class Graph {
public:
    static int G_NODES, G_EDGES; // helps in determining which heuristic to apply
    int n, m;
    unordered_map<int, unordered_set<int>> graph;
    unordered_map<int, unordered_set<int>> transpose;

    Graph(int n, int m): n(n), m(m) {}

    void add_edge(int u, int v) {
        graph[u].insert(v);
        transpose[v].insert(u);

        if(graph.find(v) == graph.end()) graph[v] = unordered_set<int>();
        if(transpose.find(u) == transpose.end()) transpose[u] = unordered_set<int>();
    }


    /**
     * Apply basic five reduction operations
     * 1) IN0(v) - If indegree(v) = 0, remove v from graph
     * 2) OUT0(v) - symmetric to IN0(v)
     * 3) IN1(v) - If indegree(v) = 1 and u is the predecessor of v, collapse v into u.
     * 4) OUT1(v) - symmetric to IN1(v)
     * 5) LOOP(v) - if v->v is a self loop edge in graph, remove v
     * 
     * Note: 
     * i) operation 3, 4 can introduced self loop, which will be removed by operation 5.
     * ii) nodes removed by operation 5 will belong to MFVS.
     */
    void reduce_basic(vector<int>& fvs) {
        int node;
        int _in, _out;
        bool nodesRemoved = true;
        vector<int> cnodes; // stores nodes to be removed
        unordered_set<int> removed; // stores nodes that has been removed
        
        while(nodesRemoved) {
            nodesRemoved = false;

            for(auto& u: graph) {
                if(removed.find(u.first) != removed.end()) continue; // if the node is already set to be removed then continue
                node = u.first;
                _in = transpose[node].size();
                _out = graph[node].size();

                if(_in == 1) { // operation 3 IN1(v)
                    int par = *(transpose[node].begin()); // only one parent of node
                    for(const int& ch: graph[node]) { // merge node into its parent
                        if(par == ch) { // self-loop is being introduced apply operation 5 LOOP(v)
                            if(removed.find(par) == removed.end()) {
                                removed.insert(par);
                                cnodes.push_back(par);                
                                fvs.push_back(par);
                            } break; // since this node will also be removed so no need to continue merging
                        } else {
                            m += graph[par].insert(ch).second;
                            transpose[ch].insert(par);
                        }
                    }
                } else if(_out == 1) { // operation 4 OUT1(v)
                    int ch = *(graph[node].begin()); // only one child of node
                    for(const int& par: transpose[node]) { // merge node into its child
                        if(par == ch) { // self-loop is being introduced apply operation 5 LOOP(v)
                            if(removed.find(ch) == removed.end()) {
                                removed.insert(ch);
                                cnodes.push_back(ch);
                                fvs.push_back(ch);
                            } break; // since this node will also be removed so no need to continue merging
                        } else {
                            m += graph[par].insert(ch).second; // if new edge is added update m
                            transpose[ch].insert(par);
                        }
                    }
                }

                if(_in == 0 || _in == 1 || _out == 0 || _out == 1) {
                    nodesRemoved = true;
                    cnodes.push_back(node);
                }
            }
            remove_nodes(cnodes);
            cnodes.clear();
            removed.clear();
        }
    }

    /**
     * Evalutes PI graph and G-PI graph
     * 
     * Given an edge (u, v), (u, v) is a PI-edge if (v, u) also exists in G
     * PI graph contains all PI edges
     * G-PI graph will not contain any PI edges
     */
    void get_PI(Graph* PI, Graph* G_minus_PI) { // Expensive Operation
        for(auto& u: graph) {
            for(const int& v: u.second) { // for every (u, v)
                if(graph[v].find(u.first) == graph[v].end()) { // if (v, u) does not exists
                    G_minus_PI->add_edge(u.first, v); // then add it to G-PI 
                } else { // if (v, u) exists
                    PI->add_edge(u.first, v); // add it to PI
                    PI->add_edge(v, u.first);
                }
            }
        }
    }

    /**
     * Remove acyclic edges from a graph
     * 
     * acyclic edges are edges that join one scc with another, since, those edges will never be part 
     * of a cycle we can safely remove them
     */
    void remove_acyclic_edges(Graph* G) {
        vector<unordered_set<int>> scc = G->get_scc(); 
        for(auto& _scc: scc) {
            for(const int& u: _scc) {
                for(const int& v: G->graph[u]) {
                    if(_scc.find(v) == _scc.end()) { // if (u, v) is not in _scc, remove it
                        transpose[v].erase(u);
                        graph[u].erase(v);
                        m--;
                    }
                }
            }
        }
    }

    /**
     * Apply PI reduction
     * remove all the acyclic edges present in G-PI graph
     * 
     * Note: 
     * PI reduction does not remove any node from graph but since it remove edges, indegree and outdegree of nodes will decrease
     * resulting in a graph which could be reduced using basic reduction techniques
     * Complexity: O(E + V)
     */
    void reduce_pi(Graph* G_minus_PI) {
        remove_acyclic_edges(G_minus_PI);
    }

    /**
     * A vertex u is a PI vertex if all its incident edges are in PI graph
     * @return array of all PI vertex, sorted in ascending order w.r.t. its degree
     */
    vector<int> get_PIV(Graph* PI) {
        vector<int> PIV;
        for(auto& u: PI->graph) {
            if(PI->graph[u.first].size() == graph[u.first].size() && PI->transpose[u.first].size() == transpose[u.first].size()) {
                PIV.push_back(u.first);
            }
        }
        sort(PIV.begin(), PIV.end(), [&](const int& a, const int& b) {
            return graph[a].size() < graph[b].size();
        });
        return PIV;
    }

    /**
     * Apply Core reduction
     * 
     * a vertex u is a neighbour of v if edge (u, v) is in PI graph
     * a vertex u COULD be a core vertex if u is in PIV and has minimum degree compare to all its neighbour N(u)
     * a vertex u IS a core vertex if u and its neighbours N(u) forms a d-clique
     * if a PI-vertex u with minimum degree n compared to its neighbours is not a core then each vertex in N(u) is not a core either
     * 
     * if u is a core vertex and then all vertex in N(u) will belong to MFVS and we can safely remove {u, N(u)} from graph
     * Complexity: O( E + V*lg(V) )
     */
    void reduce_core(Graph* PI, vector<int>& fvs) {
        vector<int> PIV = get_PIV(PI); // sorted in ascending order w.r.t. its degree
        unordered_map<int, bool> valid; // represents if a vertex can be a core vertex or not
        unordered_set<int> mfvs;
        
        for(int& x: PIV)
            valid[x] = true;

        for(auto& u: PIV) {
            if(valid[u] == true) {
                unordered_set<int> neighbour;
                for(const int& v: PI->graph[u]) // finds its neighbours
                    neighbour.insert(v);

                bool is_d_clique = true;
                for(const int& v: neighbour) { // check if {u, N(u)} forms a d-clique
                    int vis = 0;
                    for(const int& ch: PI->graph[v]) {
                        if(neighbour.find(ch) != neighbour.end()) vis++;
                    }
                    if(vis != neighbour.size()-1) {
                        is_d_clique = false;
                        break;
                    }
                }
                if(is_d_clique) {
                    mfvs.insert(neighbour.begin(), neighbour.end());
                    neighbour.insert(u);
                    vector<int> cnodes(neighbour.begin(), neighbour.end());
                    remove_nodes(cnodes);
                }
                for(const int& v: neighbour)
                    valid[v] = false;
            }
        }
        fvs.insert(fvs.end(), mfvs.begin(), mfvs.end());
    }

    /// Apply all reduction rules to a graph untill it cannot be reduced any further
    void reduce(vector<int>& fvs) {
        Graph *PI, *G_minus_PI;

        reduce_basic(fvs);
        while(true) {
            PI = new Graph(0, 0);
            G_minus_PI = new Graph(0, 0);

            int old_n = n;

            get_PI(PI, G_minus_PI); // get PI and G-PI graph
            reduce_pi(G_minus_PI); // try to reduce using PI reduction
            reduce_core(PI, fvs); // apply Core reduction

            reduce_basic(fvs);
            
            delete(PI);
            delete(G_minus_PI);

            if(n == old_n) break; // if fail to reduce then break out of loop
        }
    }

    void remove_nodes(vector<int>& nodes) {
        // remove u->v edges from transpose
        // where v is in nodes
        for(int& par: nodes) {
            if(graph.count(par) == 0) continue;
            for(const int& ch: graph[par]) {
                transpose[ch].erase(par);
            }
        }

        // remove u->v edges from graph
        // where v is in nodes
        for(int& ch: nodes) {
            if(transpose.count(ch) == 0) continue;
            for(const int& par: transpose[ch]) {
                m -= graph[par].erase(ch); // erase returns 1 if element is present
            }
        }
        
        // remove u->v egdes from graph and transpose
        // where u is in nodes
        for(int& node: nodes) {
            m -= graph.count(node) ? graph[node].size() : 0;
            n -= graph.erase(node);
            transpose.erase(node);
        }
    }

    /**
     * Takes intersection of two unorderd sets and stores the result in graph[u]
     * Complexity: O( min(|a|, |b|) )
     */
    void compute_edges(int u, unordered_set<int>& a, unordered_set<int>& b, Graph* G) {
        if(a.size() > b.size()) {
            // if b has less no. of elements than a
            for(const int& v: b) {
                if(a.find(v) != a.end())
                    G->add_edge(u, v);
            }
        } else {
            // if a has less no. of elements than b 
            for(const int& v: a) {
                if(b.find(v) != b.end())
                    G->add_edge(u, v);
            }
        }
    }

    // Bottleneck if graph is very dense.
    // Test case: 98, 99
    Graph* get_induced_subgraph(unordered_set<int>& nodes) {
        Graph* G = new Graph(nodes.size(), 0);        
        for(const int& u: nodes) {
            compute_edges(u, graph[u], nodes, G);
            G->m += G->graph[u].size();
        }
        return G;
    }

    /// Helps in calculating SCC of a graph
    void fill(int start, unordered_map<int, bool>& vis, stack<int>& st) {
        stack<int> q;

        q.push(start);
        while(!q.empty()) {
            int u = q.top();
            vis[u] = true;
            bool finished = true;

            for(const int& v: graph[u]) {
                if(!vis[v]) {
                    q.push(v);
                    finished = false;
                    break;
                }
            }
            if(finished) {
                st.push(u);
                q.pop();
            }
        }
    }

    /// Helps in calculating SCC of a graph
    unordered_set<int> dfs(int start, unordered_map<int, bool>& vis) {
        stack<int> q;
        unordered_set<int> comp;

        q.push(start);
        vis[start] = true;
        while(!q.empty()) {
            int u = q.top(); q.pop();
            comp.insert(u);

            for(const int& v: transpose[u]) {
                if(!vis[v]) {
                    vis[v] = true;
                    q.push(v);
                }
            }
        }
        return comp;
    }

    vector<unordered_set<int>> get_scc() {
        stack<int> st;
        unordered_map<int, bool> vis;
        vector<unordered_set<int>> scc;

        for(auto& u: graph) {
            if(!vis[u.first]) {
                fill(u.first, vis, st);
            }
        }
        vis.clear();

        while(!st.empty()) {
            int node = st.top();
            st.pop();

            if(!vis[node]) {
                scc.push_back(std::move(dfs(node, vis)));
            }
        }
        return scc;
    }

	/// @return the position of node in current configutation S after all its parents in S
	int getPositionMinus(vector<int>& S, int v) {
		for(int i=S.size()-1; i>=0; i--) {
			if(transpose[v].find(S[i]) != transpose[v].end())
				return i+1;
		}
		return 0;
	}

	/// @return the position of node in current configutation S before all its children in S
	int getPositionPlus(vector<int>& S, int v) {
		for(int i=0; i<S.size(); i++) {
			if(graph[v].find(S[i]) != graph[v].end())
				return i;
		}
		return S.size();
	}

	/// @return a random number between 0 and 1
	double getRandom() {
		return dis(gen);
	}

	/// @return a random node which is not in current configurtion S
	int select_random(unordered_set<int>& s) {
		int v_index = (int)(getRandom() * s.size());
		auto it = begin(s);
		advance(it, v_index);
		return *it;
	}

	/**
	 * The configuration used in SA is topological ordering of nodes. Since, the nodes in a topological order do not form a cycle
	 * among themselves, the algorithm tries to increase the size of this configuration, after the algorithm converges the nodes that
	 * are not in the configuration will belong to FVS(since they most probably are part of cycle)
	 * @param fvs stores the nodes in fvs
	 * @param T0 initial temperature
	 * @param alpha cooling rate(rate by which temperature is reduced)
	 * @param mvtFactor determine no. of time to update configuration S in an iteration (n * mvtFactor)
	 * @param maxFail algorithm is set to converge if S_optimal does not change for {maxFail} iteration
	 */
	void simulatedAnnealing(vector<int>& fvs, double T0=0.7, double alpha=0.99, double mvtFactor=7, int maxFail=50) {
		double T = T0;
		int maxMvt = min(mvtFactor * n, 3e5); // no. of times to update S in an iteration
        if(n <= 1e4) maxFail = 200;
     
		vector<int> S; // current configuration
		vector<int> S_optimal; // best configuration achieved so far

		unordered_set<int> unnumbered; // stores the node that are not part of current configuration S
		for(auto& u: graph) { // Initially all node will be in unnumbered
			unnumbered.insert(u.first);
		}

		int nbFail = 0;
		while(nbFail < maxFail && !tle) { // tle will be equal to 1 if program has received SIGTERM 
			int nbMvt = 0;
			bool failure = true; // determined if we were able to find a better S_optimal

			while(nbMvt < maxMvt && !tle) {
				int v = select_random(unnumbered); // randomly select a node not in S
				
				// there are |S| possible ways to put the node selected into S
				// but out of those |S| we only need to consider two positions
				// (i) after every parent of v in S
				// (ii) before every child of v in S
				// (these two give an optimal next configuration)

				// randomly select a position out of those two
				// b = 0, after parents	in S		b = 1, before children in S
				int b = (int)(getRandom() * 2);
				int position = (b == 0) ? getPositionMinus(S, v) : getPositionPlus(S, v);

				// after adding v in S at position {position} to maintain topological ordering we may have to remove some nodes
				vector<int> conflict; // stores nodes to be removed
				if(b == 0) {
					for(int i=0; i<position; i++) {
						if(graph[v].find(S[i]) != graph[v].end())
							conflict.push_back(S[i]);
					}
				} else {
					for(int i=position; i<S.size(); i++) {
						if(transpose[v].find(S[i]) != transpose[v].end())
							conflict.push_back(S[i]);
					}
				}

				int delta = conflict.size() - 1; // change in size of S after adding v
				// if size of S increases or remain the same add v in S
				// if size of S does not increse, add v in S with some probability
				if(delta <= 0 || 0.5*exp(-delta/T) >= getRandom()) { 
					// update unnumbered set
					unnumbered.erase(v);
					for(int x: conflict) {
						unnumbered.insert(x);
					}

					S.insert(S.begin()+position, v); // add v in S
					vector<int> S_new; // new S after removing conflicting nodes
					int j=0;
					conflict.push_back(__INT_MAX__); // to prevent index out of bound
					for(int i=0; i<S.size(); i++) {
						if(S[i] == conflict[j]) j++;
						else S_new.push_back(S[i]);
					}
					S.swap(S_new);
					nbMvt++;

					if(S.size() > S_optimal.size()) { // update S_optimal accordingly
						S_optimal = S;
						failure = false;
					}
				}
			}
			if(failure) nbFail++;
			else nbFail = 0;
			T = alpha * T;
		}
		
		// now push the node that are not part of S_optimal into fvs array
		unordered_set<int> optimal_set(S_optimal.begin(), S_optimal.end());
		for(auto& u: graph) {
			if(optimal_set.count(u.first) == 0)
				fvs.push_back(u.first);
		}
	}
};

void read(string& input) {
    do {
        getline(cin, input);
    } while(input.length() > 0 && input[0] == '%');
}

/// @return an object of the input graph
Graph* read_graph() {
	string input;
	istringstream ss;
	int n, m, v;

    read(input); ss.str(input);
	ss >> n >> m;
	ss.clear();

    Graph* G = new Graph(n, m);

	for(int u=1; u<=n; u++) {
		read(input); ss.str(input);
		while(ss >> v) {
			G->add_edge(u, v);
		} ss.clear();
	}
    G->n = G->graph.size();
    return G;
}

/**
 * @param OG original graph
 * @return FVS of the original graph
 */
vector<int> get_fvs(Graph* OG) {
    stack<Graph*> st; // to store objects of induced graphs
    vector<int> fvs; // stores the FVS

    Graph* G = OG;
    // get all the graphs induced by the SCCs of G 
    for(auto& _scc: G->get_scc()) {
        if(_scc.size() > 1) {
            st.push(G->get_induced_subgraph(_scc));
        }
    }
    delete(G); // don't need this graph anymore
	
    while(!st.empty()) {
        G = st.top(); st.pop();
		G->simulatedAnnealing(fvs);
        delete(G); // don't need this graph anymore
    }
    return fvs;
}

int Graph::G_NODES = 0;
int Graph::G_EDGES = 0;

int main() {
    ios::sync_with_stdio(0);
    cin.tie(0);

	struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_handler = term;
    sigaction(SIGTERM, &action, NULL);

    Graph* G = read_graph();
    vector<int> mfvs;
    
    G->reduce(mfvs);
    Graph::G_NODES = G->n; 
    Graph::G_EDGES = G->m;

    vector<int> fvs = get_fvs(G);
    fvs.insert(fvs.end(), mfvs.begin(), mfvs.end());

    for(const int& x: fvs) {
        cout << x << "\n";
    }
    // cerr << fvs.size() << "\n";
}
