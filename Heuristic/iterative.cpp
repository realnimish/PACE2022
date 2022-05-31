#include <iostream>
#include <sstream>
#include <vector>
#include <stack>
#include <unordered_set>
#include <map> 
#include <unordered_map>
#include <algorithm>
#include <signal.h>
#include <unistd.h>
#include <assert.h>
#include <chrono>

using namespace std;

volatile sig_atomic_t tle = 0;
/// SIGTERM handler
void term(int signum) {
    tle = 1;
}

class Graph {
public:
    int n, m;
    unordered_map<int, unordered_set<int>> graph;
    unordered_map<int, unordered_set<int>> transpose;

    unordered_map<int, long long> ele_wt;
    map<long long, unordered_set<int>> wt_ele;

    Graph(int n, int m): n(n), m(m) {}
    Graph(const Graph& G): n(G.n), m(G.m), graph(G.graph), transpose(G.transpose), ele_wt(G.ele_wt), wt_ele(G.wt_ele) {} // Copy Constructor

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

    void pre_compute_density() {
        ele_wt.clear();
        wt_ele.clear();
        for(auto& u: graph) {
            long long density = (long long)u.second.size() * transpose[u.first].size();
            ele_wt[u.first] = density;
            wt_ele[density].insert(u.first);
        }
    }

    void update_in(int u, bool dec=true) {
        wt_ele[ele_wt[u]].erase(u);
        if(wt_ele[ele_wt[u]].empty()) wt_ele.erase(ele_wt[u]);

        if(dec) ele_wt[u] -= graph[u].size();
        else ele_wt[u] += graph[u].size();

        wt_ele[ele_wt[u]].insert(u);
    }

    void update_out(int u, bool dec=true) {
        wt_ele[ele_wt[u]].erase(u);
        if(wt_ele[ele_wt[u]].empty()) wt_ele.erase(ele_wt[u]);

        if(dec) ele_wt[u] -= transpose[u].size();
        else ele_wt[u] += transpose[u].size();

        wt_ele[ele_wt[u]].insert(u);
    }

    void delete_entry(int u) {
        wt_ele[ele_wt[u]].erase(u);
        if(wt_ele[ele_wt[u]].empty()) wt_ele.erase(ele_wt[u]);

        ele_wt.erase(u);
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
                node = u.first;
                if(removed.find(node) != removed.end()) continue; // if the node is already set to be removed then continue
                _in = transpose[node].size();
                _out = graph[node].size();

                if(_in == 1) { // operation 3 IN1(v)
                    int par = *(transpose[node].begin()); // only one parent of node
                    if(graph[node].find(par) != graph[node].end()) { // self-loop will be introduced apply operation 5 LOOP(v)
                        if(removed.find(par) == removed.end()) {
                            removed.insert(par);
                            cnodes.push_back(par);                
                            fvs.push_back(par);
                        }
                    } else {
                        for(const int& ch: graph[node]) { // merge node into its parent
                            if(graph[par].insert(ch).second) {
                                m++;
                                transpose[ch].insert(par);
                                update_out(par, false);
                                update_in(ch, false);
                            }
                        }
                    }
                } else if(_out == 1) { // operation 4 OUT1(v)
                    int ch = *(graph[node].begin()); // only one child of node
                    if(transpose[node].find(ch) != transpose[node].end()) { // self-loop will be introduced apply operation 5 LOOP(v)
                        if(removed.find(ch) == removed.end()) {
                            removed.insert(ch);
                            cnodes.push_back(ch);
                            fvs.push_back(ch);
                        }
                    } else {
                        for(const int& par: transpose[node]) { // merge node into its child
                            if(graph[par].insert(ch).second) {
                                m++;
                                transpose[ch].insert(par);
                                update_out(par, false);
                                update_in(ch, false);
                            }
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
        stack<int> st;
        unordered_map<int, bool> vis;

        for(auto& u: G->graph) {
            if(!vis[u.first]) {
                G->fill(u.first, vis, st);
            }
        }
        vis.clear();

        while(!st.empty()) {
            int node = st.top();
            st.pop();

            if(!vis[node]) {
                unordered_set<int> _scc = G->dfs(node, vis);
                for(const int& u: _scc) {
                    for(const int& v: G->graph[u]) {
                        if(_scc.find(v) == _scc.end()) { // if (u, v) is not in _scc, remove it
                            transpose[v].erase(u);
                            graph[u].erase(v);
                            m--;
                            update_out(u);
                            update_in(v);
                        }
                    }
                }
            }
        }
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

        for(int& u: PIV) {
            if(valid[u]) {
                unordered_set<int>& neighbour = PI->graph[u];
                
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
                    vector<int> cnodes(neighbour.begin(), neighbour.end());
                    cnodes.push_back(u);
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
        delete(PI);
        
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
            update_out(edge.first);
            update_in(edge.second);
        }

        delete(G_minus_PI);
    }

    /// Apply all reduction rules to a graph except Dome until it cannot be reduced any further
    void reduce(vector<int>& fvs) {
        Graph *PI, *G_minus_PI;

        reduce_basic(fvs);
        while(true) {
            int old_n = n;

            get_PI(PI, G_minus_PI); // get PI and G-PI graph
            remove_acyclic_edges(G_minus_PI); // try to reduce using PI reduction
            reduce_core(PI, fvs); // apply Core reduction

            delete(PI);
            delete(G_minus_PI);
            
            reduce_basic(fvs);

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
                update_in(ch);
            }
        }

        // remove u->v edges from graph
        // where v is in nodes
        for(int& ch: nodes) {
            if(transpose.count(ch) == 0) continue;
            for(const int& par: transpose[ch]) {
                m -= graph[par].erase(ch); // erase returns 1 if element is present
                update_out(par);
            }
        }
        
        // remove u->v egdes from graph and transpose
        // where u is in nodes
        for(int& node: nodes) {
            m -= graph.count(node) ? graph[node].size() : 0;
            n -= graph.erase(node);
            transpose.erase(node);
            delete_entry(node);
        }
        
        // re-hash graph and transpose if nescessary
        if(graph.size() && graph.bucket_count() / graph.size() >= 2) {
            graph.rehash(graph.size());
            transpose.rehash(transpose.size());
            ele_wt.rehash(ele_wt.size());
            for(auto& u: graph) {
                if(graph[u.first].size() && graph[u.first].bucket_count() / graph[u.first].size() >= 2)
                    graph[u.first].rehash(graph[u.first].size());
                if(transpose[u.first].size() && transpose[u.first].bucket_count() / transpose[u.first].size() >= 2)
                    transpose[u.first].rehash(transpose[u.first].size());
            }
        }
    }

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

   void get_FVS_Heuristic(vector<int>& fvs, int freq=50) {
        int count = max(1, n/freq); // no. of critical nodes to remove from graph
        edge_density(fvs, count);
    }

    void edge_density(vector<int>& fvs, int count=1) {
        // for(auto& u: graph) 
        //     assert(ele_wt[u.first] == (long long)graph[u.first].size() * transpose[u.first].size());
        vector<int> cnodes;
        while(count > 0) {
            unordered_set<int>& temp = wt_ele.rbegin()->second;
            for(auto itr=temp.begin(); itr!=temp.end() && count; itr++) {
                cnodes.push_back(*itr);
                fvs.push_back(*itr);
                count--;
            }
            if(count) wt_ele.erase(prev(wt_ele.end()));
        }
        remove_nodes(cnodes);
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
vector<int> get_fvs(Graph* OG, int freq=50) {
    vector<int> fvs; // stores the FVS

    Graph* G = new Graph(*OG);

    if(G->m <= 1e6) {
        G->reduce(fvs);
    } else {
        G->remove_acyclic_edges(G);
        G->reduce_basic(fvs);
    }
    while(G->n) {
        G->get_FVS_Heuristic(fvs, freq);

        if(G->m <= 1e6) {
            G->reduce(fvs);
        } else {
            G->remove_acyclic_edges(G);
            G->reduce_basic(fvs);
        }
    }
    delete(G);
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
        vis.reserve(G->graph.size());

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
    delete(G);
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

int main() {
    ios::sync_with_stdio(0);
    cin.tie(0);

    // struct sigaction action;
    // memset(&action, 0, sizeof(struct sigaction));
    // action.sa_handler = term;
    // sigaction(SIGTERM, &action, NULL);

    auto start = chrono::high_resolution_clock::now();

    Graph* G = read_graph();
    vector<int> mfvs;
    
    G->reduce(mfvs);
    if(G->m < 1e6) G->reduce_special(mfvs); // if graph is small apply expensive reduction

    // cerr << G->n << " " << G->m << " " << mfvs.size() << endl;

    G->pre_compute_density();
    vector<int> fvs = get_fvs(G);
    fvs = remove_redundant(G, fvs);

    auto stop = chrono::high_resolution_clock::now();
    auto duration = chrono::duration_cast<chrono::duration<double>>(stop - start);

    // for(const int& x: fvs)
    //     cout << x << "\n";
    // for(const int& x: mfvs)
    //     cout << x << "\n";
    
    // cerr << "Ans: " << fvs.size() + mfvs.size() << endl;
    cout << "Ans: " << fvs.size() + mfvs.size() << "\t\t" << "Time: " << duration.count() << "\n";
}
