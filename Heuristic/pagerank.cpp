#include <iostream>
#include <sstream>
#include <vector>
#include <stack>
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <cmath>
#include <functional>
#include <assert.h>

using namespace std;

enum heuristic { Pagerank, Edge_Density };

class Graph {
public:
    static int G_NODES, G_EDGES;
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

    void remove_nodes(vector<int>& nodes) {
        for(int& par: nodes) {
            for(const int& ch: graph[par]) {
                transpose[ch].erase(par);
            }
        }

        for(int& ch: nodes) {
            for(const int& par: transpose[ch]) {
                m -= graph[par].erase(ch); // erase returns 1 if element is present
            }
        }
        
        for(int& node: nodes) {
            n -= 1;
            m -= graph[node].size();
            graph.erase(node);
            transpose.erase(node);
        }
    }

    void compute_edges(int u, unordered_set<int>& a, unordered_set<int>& b, Graph* G) {
        if(a.size() > b.size()) {
            for(const int& v: b) {
                if(a.find(v) != a.end())
                    G->add_edge(u, v);
            }
        }else {
            for(const int& v: a) {
                if(b.find(v) != b.end())
                    G->add_edge(u, v);
            }
        }
    }

    Graph* get_induced_subgraph(unordered_set<int>& nodes) {
        Graph* G = new Graph(nodes.size(), 0);        
        for(const int& u: nodes) {
            compute_edges(u, graph[u], nodes, G);
            G->m += G->graph[u].size();
        }
        return G;
    }

    // No need to check if the graph is DAG or NOT since every graph we are processing is a SCC.
    // bool isDAG() {
	//     unordered_map<int, bool> vis, marked;

    //     function<bool(int)> dfs;
    //     dfs = [&](int node) {
    //             vis[node] = true;
    //             marked[node] = true;
    //             for(const int& ch: graph[node]) {
    //                 if(marked[ch] || (!vis[ch] && dfs(ch)))
    //                     return true;
    //             }
    //             marked[node] = false;
    //             return false;
    //         };

    //     for(auto& p: graph) {
    //         if(!vis[p.first] && dfs(p.first))
    //             return false;
    //     }
    //     return true;
    // }

    // void get_transpose() {
    //     for(auto& u: graph) {
    //         for(int v: u.second) {
    //             transpose[v].insert(u.first);
    //         }
    //     }
    // }

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

   void get_FVS_Heuristic(vector<int>& fvs) {
        heuristic method;
        int freq;
        if(Graph::G_NODES < 10000 && Graph::G_EDGES < 100000) {
            method = Pagerank;
            freq = 500;
        } else {
            method = Edge_Density;
            freq = 50;
        }
        int count = max(1, n/freq);
        vector<int> cnodes = get_critical_nodes(method, count);
        remove_nodes(cnodes);

        fvs.insert(fvs.end(), cnodes.begin(), cnodes.end());
    }

    vector<int> get_critical_nodes(heuristic method=Edge_Density, int count=1) {
        if(method == Edge_Density) {
            return edge_density(count);
        } else {
            return pagerank(count);
        }
    }

    vector<int> pagerank(int count=1, double beta=0.85, double epsilon=1e-6, int itr=100, bool rand=false) {
        unordered_map<int, double> curr, next;
        for(auto& u: graph) {
            curr[u.first] = (double)1/n;
        }

        for(int i=0; i<itr; i++) {
            for(auto& u: graph) {
                next[u.first] = (1-beta)/n;
            }

            for(auto& u: graph) {
                for(const int& ch: u.second) {
                    next[ch] += beta * (curr[u.first] / u.second.size());
                }
                // will never run in case graph is SCC
                if(u.second.size() == 0) {
                    for(auto& x: graph) {
                        next[x.first] += beta * (curr[u.first] / n);
                    }
                }
            }

            bool converge = true;
            for(auto& u: curr) {
                if(std::abs(u.second - next[u.first]) >= epsilon) {
                    converge = false;
                    break;
                }
            } 
            curr.swap(next);
            if(converge) break;
        }
        vector<int> cnodes;
        priority_queue<pair<double, int>, vector<pair<double, int>>, greater<pair<double, int>>> pq;
        for(auto& p: curr) {
            pq.push({p.second, p.first});
            if(pq.size() > count) pq.pop();
        }
        while(!pq.empty()) {
            cnodes.push_back(pq.top().second);
            pq.pop();
        }
        return cnodes;
    }

    vector<int> edge_density(int count=1) {
        priority_queue<pair<long long, int>, vector<pair<long long, int>>, greater<pair<long long, int>>> pq;
        for(auto& u: graph) {
            pq.push({(long long)transpose[u.first].size() + u.second.size(), u.first});
            if(pq.size() > count) pq.pop();
        }
        vector<int> cnodes;
        while(!pq.empty()) {
            cnodes.push_back(pq.top().second);
            pq.pop();
        }
        return cnodes;
    }
};

void read(string& input) {
    do {
        getline(cin, input);
    } while(input.length() > 0 && input[0] == '%');
}

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
    return G;
}

vector<int> get_fvs(Graph* OG) {
    stack<Graph*> st;
    vector<int> fvs;

    Graph* G = OG;

    for(auto& _scc: G->get_scc()) {
        if(_scc.size() > 1) {
            st.push(G->get_induced_subgraph(_scc));
        }
    }
    delete(G);

    // int x = 0;
    while(!st.empty()) {
        // cerr << "fvs " << fvs.size() << " " << x++ << endl;
        G = st.top(); st.pop();
        G->get_FVS_Heuristic(fvs);

        for(auto& _scc: G->get_scc()) {
            if(_scc.size() > 1) {
                st.push(G->get_induced_subgraph(_scc));
            }
        }
        delete(G);
    }
    return fvs;
}

int Graph::G_NODES = 0;
int Graph::G_EDGES = 0;

int main() {
    ios::sync_with_stdio(0);
    cin.tie(0);

    Graph* G = read_graph();
    Graph::G_NODES = G->n; 
    Graph::G_EDGES = G->m;
    // cerr << "read input" << endl; 
    vector<int> fvs = get_fvs(G);

    for(int& x: fvs) {
        cout << x << "\n";
    }
    // cerr << fvs.size() << "\n";
}
