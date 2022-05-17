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

using namespace std;

enum heuristic { Pagerank, Edge_Density };

class Graph {
public:
    static int G_NODES, G_EDGES; // helps in determining which heuristic to apply
    int n, m;
    unordered_map<int, unordered_set<int>> graph;
    unordered_map<int, unordered_set<int>> transpose;

    Graph(int n, int m): n(n), m(m) {}
    Graph(const Graph& G): n(G.n), m(G.m), graph(G.graph), transpose(G.transpose) {} // Copy Constructor

    void add_edge(int u, int v) { // add edge (u, v) to graph
        graph[u].insert(v);
        transpose[v].insert(u);

        if(graph.find(v) == graph.end()) graph[v] = unordered_set<int>();
        if(transpose.find(u) == transpose.end()) transpose[u] = unordered_set<int>();
    }

    void delete_edge(int u, int v) { // delete edge (u, v) from graph
        graph[u].erase(v);
        transpose[v].erase(u);
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
     * Given an edge (u, v), (u, v) is a PI-edge if (v, u) also exists in G
     * @return the no. of PI edges in graph
     */
    int get_pi_edges_count() {
        int pi_edges = 0;
        for(auto& u: graph) {
            for(const int& v: u.second) { // for every (u, v)
                if(graph[v].find(u.first) != graph[v].end()) { // if (v, u) exists
                   pi_edges++;
                }
            }
        }
        return pi_edges;
    }

    /**
     * Evalutes PI graph and G-PI graph
     * 
     * Given an edge (u, v), (u, v) is a PI-edge if (v, u) also exists in G
     * PI graph contains all PI edges
     * G-PI graph will not contain any PI edges
     */
    void get_PI(Graph*& PI, Graph*& G_minus_PI) {
        int pi_edges = get_pi_edges_count();

        if(pi_edges && m / pi_edges <= 1) { // if condition holds then PI graph is almost similar to original graph
            PI = new Graph(*this);
            G_minus_PI = new Graph(0, 0);

            for(auto& u: graph) {
                for(const int& v: u.second) { // for every (u, v)
                    if(graph[v].find(u.first) == graph[v].end()) { // if (v, u) does not exists
                        G_minus_PI->add_edge(u.first, v); // add edge to G-PI
                        PI->delete_edge(u.first, v); // delete edge from PI
                    }
                }
            }
        } else { // else G-PI graph is almost similar to original graph
            PI = new Graph(0, 0);
            G_minus_PI = new Graph(*this);

            for(auto& u: graph) {
                for(const int& v: u.second) { // for every (u, v)
                    if(graph[v].find(u.first) != graph[v].end()) { // if (v, u) exists
                        PI->add_edge(u.first, v); // add edge to PI
                        PI->add_edge(v, u.first);
                        G_minus_PI->delete_edge(u.first, v); // delete edge from G-PI
                    }
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

    /// checks if a set A is a subset of another set B 
    bool is_subset(unordered_set<int>& a, unordered_set<int>& b) {
        if(a.size() > b.size()) return false;

        for(const int& x: a) {
            if(b.find(x) == b.end()) 
                return false;
        }
        return true;
    }

    /**
     * Apply Dome Reduction
     * 
     * Dominant Edge are edges that are not part of minimal cycle and therefore, can be safely removed from graph
     * 
     * An edge (u, v) is a dominant edge if one of the following condition holds:-
     * 1) Set of non-PI predecessor of u is a subset of all predecessor of v.
     * 2) Set of non-PI successor of v is a subset of all successors of u.
     * 
     * Complexity: O(V * E)  !Very Expensive Reduction
     */
    void reduce_dome() {
        Graph *PI, *G_minus_PI;

        get_PI(PI, G_minus_PI);
        
        vector<pair<int, int>> dominant_edges;
        for(auto& u: G_minus_PI->graph) {
            for(const int& v: u.second) {
                if(is_subset(G_minus_PI->transpose[u.first], transpose[v])) {
                    dominant_edges.emplace_back(u.first, v);
                } else if(is_subset(G_minus_PI->graph[v], graph[u.first])) {
                    dominant_edges.emplace_back(u.first, v);
                }
            }
        }

        m -= dominant_edges.size();
        for(auto& edge: dominant_edges) {
            graph[edge.first].erase(edge.second);
            transpose[edge.second].erase(edge.first);
        }

        delete(PI);
        delete(G_minus_PI);
    }

    /// Apply all reduction rules to a graph except Dome until it cannot be reduced any further
    void reduce(vector<int>& fvs) {
        Graph *PI, *G_minus_PI;

        reduce_basic(fvs);
        while(true) {
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

    /// Apply all reduction rules to a graph including Dome until it cannot be reduced any further
    void reduce_special(vector<int>& fvs) {
        while(true) {
            int old_n = n;
            reduce_dome(); // Apply Dome reduction 
            reduce(fvs); // Apply all other reductions
            if(n == old_n) break;
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
        
        // re-hash graph and transpose if nescessary
        if(graph.size() && graph.bucket_count() / graph.size() >= 2) {
            graph.rehash(graph.size());
            transpose.rehash(transpose.size());
            for(auto& u: graph) {
                if(graph[u.first].size() && graph[u.first].bucket_count() / graph[u.first].size() >= 2)
                    graph[u.first].rehash(graph[u.first].size());
                if(transpose[u.first].size() && transpose[u.first].bucket_count() / transpose[u.first].size() >= 2)
                    transpose[u.first].rehash(transpose[u.first].size());
            }
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

    /// @return induced sub-graph containing vertices in {nodes} 
    Graph* get_induced_subgraph(unordered_set<int>& nodes) {
        Graph* G; // induced sub-graph
        
        if(graph.size()/nodes.size() <= 2) { // induced sub-graph is almost similar to original graph
            G = new Graph(*this);

            vector<int> remove;
            for(auto& u: G->graph) {
                if(nodes.find(u.first) == nodes.end()) {
                    remove.push_back(u.first);
                }
            }
            G->remove_nodes(remove);
        } else {
            G = new Graph(nodes.size(), 0);        
            for(const int& u: nodes) {
                compute_edges(u, graph[u], nodes, G);
                G->m += G->graph[u].size();
            }
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

    // helps in finding topological ordering of a graph
    void topo_helper(int start, unordered_map<int, bool>& vis, vector<int>& topo_order) {
        stack<int> q;

        q.push(start);
        while(!q.empty()) {
            int u = q.top();
            vis[u] = true;
            bool finished = true;

            for(const int& v: transpose[u]) {
                if(!vis[v]) {
                    q.push(v);
                    finished = false;
                    break;
                }
            }
            if(finished) {
                topo_order.push_back(u);
                q.pop();
            }
        }
    }

    vector<int> get_topological_ordering() {
        vector<int> topo_order;
        unordered_map<int, bool> vis;

        for(auto& u: graph) {
            if(!vis[u.first]) {
                topo_helper(u.first, vis, topo_order);
            }
        }

        return topo_order;
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
        int count = max(1, n/freq); // no. of critical nodes to remove from graph
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

    /**
     * Time Complexity - O(itr*(V + E)) (for SCC)
     * @param count no. of critical nodes to return
     * @param beta damping factor
     * @param itr no. of iterations
     * @param epsilon to check for convergence
     * @param rand flag to randomly initialize the probability of each node
     * @return a list of critical nodes
     */
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

        // using min heap to get {count} no. of elements having largest density
        // Complexity: O( n*log(k) ), n: no. of nodes in graph, k: count
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

    /**
     * @param count no. of critical nodes to return
     * @return a list of critical nodes
     */
    vector<int> edge_density(int count=1) {
        // using min heap to get {count} no. of elements having largest density
        // Complexity: O( n*log(k) ), n: no. of nodes in graph, k: count
        // using <long long, int>, if in case density is changed to _incomingEdges * _outgoingEdges
        priority_queue<pair<long long, int>, vector<pair<long long, int>>, greater<pair<long long, int>>> pq;

        for(auto& u: graph) {
            pq.push({(long long)transpose[u.first].size() * u.second.size(), u.first});
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

    while(!st.empty()) {
        G = st.top(); st.pop();
        
        G->get_FVS_Heuristic(fvs);

        if(G->m <= 1e6) G->reduce(fvs);
        else G->reduce_basic(fvs);

        // get all the graphs induced by the SCCs of G 
        for(auto& _scc: G->get_scc()) {
            if(_scc.size() > 1) {
                st.push(G->get_induced_subgraph(_scc));
            }
        }

        // cerr << "fvs size: " << fvs.size() << endl;

        delete(G); // don't need this graph anymore
    }
    return fvs;
}

/**
 * Time Complexity: O( V + E )
 * Space Complexity: O( batch_size * V )
 *  @return set of redundant nodes in fvs set
 */
unordered_set<int> get_redunant(Graph* OG, vector<int>& fvs) {
    unordered_set<int> redundant;
    Graph* G = new Graph(*OG); // acyclic sub-graph of original
    G->remove_nodes(fvs);
    vector<int> ordering = G->get_topological_ordering(); // topological ordering of acyclic graph

    int batch_size = 1000; // process {batch_size} no. of nodes at one go
    int iterations = (fvs.size() + batch_size - 1) / batch_size;

    for(int i=0; i<iterations; i++) {
        unordered_map<int, unordered_set<int>> vis; // vis[u] stores the set of nodes in fvs that can reach u

        int cnt = batch_size;
        for(int j=i*batch_size; j<fvs.size() && cnt; j++, cnt--) {
            int u = fvs[j];
            for(const int& v: OG->graph[u]) {
                if(G->graph.find(v) != G->graph.end())
                    vis[v].insert(u);
            }
        }

        // if a node u is reachable from a node x in fvs
        // then successor of u are also reachable from x
        for(int& u: ordering) {
            for(const int& v: G->transpose[u]) {
                vis[u].insert(vis[v].begin(), vis[v].end());
            }
        }

        cnt = batch_size;
        for(int j=i*batch_size; j<fvs.size() && cnt; j++, cnt--) {
            int u = fvs[j];
            bool is_redundant = true;
            // if a node in fvs is reachable from itself then its not redundant
            for(const int& v: OG->transpose[u]) {
                if(G->graph.find(v) != G->graph.end() && vis[v].find(u) != vis[v].end()) {
                    is_redundant = false;
                    break;
                }
            }
            if(is_redundant) redundant.insert(u);
        }
    }

    // if all nodes in fvs are redundant randomly remove one node from redundant set
    if(!redundant.empty() && redundant.size() == fvs.size()) redundant.erase(redundant.begin());
    return redundant;
}

/// removes redundant nodes from fvs
vector<int> remove_redundant(Graph* OG, vector<int>& fvs) {
    bool flag = 1;
    vector<int> final_fvs; // fvs after removal of redundant nodes

    while(flag) {
        unordered_set<int> redundant = get_redunant(OG, fvs);

        for(int x: fvs) { // if x is not redundant push it to final_fvs
            if(redundant.find(x) == redundant.end())
                final_fvs.push_back(x);
        }

        if(!redundant.empty()) {
            OG->remove_nodes(final_fvs); // remove nodes from original that are not redundant
            fvs = get_fvs(OG); // re-calculate fvs
            if(fvs.empty()) flag = 0;
        } else {
            flag = 0;
        }
    }
    return final_fvs;
}

int Graph::G_NODES = 0;
int Graph::G_EDGES = 0;

int main() {
    ios::sync_with_stdio(0);
    cin.tie(0);

    Graph* G = read_graph();
    // cerr << "read graph" << endl;
    vector<int> mfvs;
    
    G->reduce(mfvs);
    Graph::G_NODES = G->n; 
    Graph::G_EDGES = G->m;

    if(G->m < 1e6) G->reduce_special(mfvs); // if graph is small apply expensive reduction

    // cerr << G->n << " " << G->m << " " << mfvs.size() << endl;

    vector<int> fvs = get_fvs(G);
    fvs = remove_redundant(G, fvs);

    for(const int& x: fvs)
        cout << x << "\n";
    for(const int& x: mfvs)
        cout << x << "\n";
    
    // cerr << "Ans: " << fvs.size() + mfvs.size() << endl;
}
