#include <string.h>
#include <vector>
#include <cstdlib>
#include <cstdio>
#include <tuple>
#include <cassert>
#include <iostream>
#include <algorithm>
#include <vector>
#include <tuple>
#include <stdint.h>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <cilk/cilk_api.h>
#include <cilk/cilk.h>
//#include "tbb/concurrent_vector.h" 
#include "CycleTimer.h"

#define OUTGOING 0
#define INCOMING 1

using namespace std;

template <typename T> class VQueue {	
	size_t V;
	size_t curr_;
	size_t next_;
	size_t end_;

public:
	vector<T> data;vector<T> value;
	explicit VQueue(size_t V) : data(V), value(V), V(V), curr_(0), next_(0), end_(0){
	}
  // virtual ~VQueue(){ delete [] data; }
	inline bool empty() const { return curr_ == next_; }
	inline bool full() const { return end_ == V; }
	inline T &front() { return data[curr_];}
	inline size_t size() const { return end_; }
	inline void pop() { ++curr_; assert(curr_ <= end_);}
	inline void push(const T &val){ data[end_++] = val; assert(end_ <= V);}
	inline void push(const T &dat, const T &val){ data[end_] = dat;value[end_++] = val; assert(end_ <= V);}
	inline void next() {  assert(curr_ == next_);next_ = end_; }//
	inline void clear() { curr_ = next_ = end_ = 0; }
	inline void resize(size_t V_){
		if (V_ > V){ V = V_; data.resize(V); value.resize(V);}
	}
	inline size_t sum(){
		size_t s=0;
		for (uint32_t i = 0; i < end_; i++){
			s += value[i];
		}
		return s;
	}

	inline typename vector<T>::iterator begin() { return data.begin();}
	inline typename vector<T>::iterator end() { return data.begin() + end_;}
};

const uint32_t ALIVE   = 0;
const uint32_t DEAD    = 1;
const uint32_t UNKNOWN = 2;
const uint32_t MASK    = 3;

//tbb::concurrent_
vector<tuple<uint32_t, uint32_t, uint32_t, char> > 	updates; // <source, target, timestamp, type>
vector<tuple<uint32_t, uint32_t, uint32_t> > 		queries; // <source, target, timestamp>
vector<vector<uint32_t>>			Edges;
vector<vector<uint32_t>>			Maps;//for all threads
vector<VQueue<uint32_t> > 			Queues;//for all threads
vector<int>							Distances;//for all nodes
uint32_t  							Node_Num = 0, Edge_Num=0;
bool 								is_directed = false;

uint32_t num_threads = __cilkrts_get_nworkers();

static inline uint32_t GetID(uint32_t v) { return v >> 2; }
static inline uint32_t GetState(uint32_t v)  { return v & MASK; }
static inline uint32_t ToEdge(uint32_t v) { return (v << 2) ;} //| ALIVE
static inline void ResetMap(uint32_t threadID)
{
	for (uint32_t v : Queues[threadID].data) {
		Maps[threadID][v>>5] = 0;
	}
	//Queues[threadID].clear();
}
//set bit at v in Maps
static inline void SetBit(uint32_t threadID, uint32_t v)
{
	Maps[threadID][v >> 5] |= (1 << ( v & 31 ));
}

//test bit at v in Maps
static inline int TestBit(uint32_t threadID, uint32_t v)
{
	return (Maps[threadID][v >> 5] >> (v & 31) ) & 1;
}

inline bool readeof() {
	for (;;) {
		int c = getc_unlocked(stdin);
		if (c == EOF || c == '#') {
			return true;
		} else if (isspace(c)) {
			continue;
		} else {
			ungetc(c, stdin);
			return false;
		}
	}
	assert(false);
}

inline uint32_t readuint() {
	uint32_t c;
	uint32_t x;
	while (!isdigit(c = getc_unlocked(stdin)));
	x = c - '0';
	while (isdigit(c = getc_unlocked(stdin))) {
		x = (x * 10 + (c - '0'));
	}
	return x;
}

void Build(char * filename)
{
	cerr << "Building the big graph..." ;
    //1.fetch edge set from stdin  
	FILE *fp = stdin; size_t bufsize=0;char *line = NULL;
	fp = fopen(filename,"r");
    int res; uint32_t u, v;
	Edges.clear(); 
	Edges.resize(1e7);
    // vertex identified from 0 -> n
	while (!feof(fp)){
		res = getline(&line,&bufsize,fp);
		if (res == -1) break;
		if (line[0] == 'S') break;

		res = sscanf(line, "%u %u", &u, &v);
		if ( !res || res == EOF ) {
			continue;
		} 
		Node_Num = max({Node_Num, u + 1, v + 1});  
		if (Node_Num>Edges.size()){
			Edges.resize(Node_Num + 1e6); 
		}
		if (std::find (Edges[u].begin(), Edges[u].end(), v) == Edges[u].end()){
			Edges[u].push_back(v);   
			++Edge_Num;
		}
		if (!is_directed && std::find (Edges[v].begin(), Edges[v].end(), u) == Edges[v].end() ){
			Edges[v].push_back(u);      		
			++Edge_Num;
		}
	}
	cerr << " Done.";
	fclose(fp);

    //sort adjacent lists
	cilk_for (uint32_t v = 0; v < Node_Num; v++){
		sort(Edges[v].begin(), Edges[v].end());    
	}

    //Node_Num += 1e5;//add more nodes 
    //cerr << "End of init" << endl;
    Edges.resize(Node_Num);


    //2. Init the graph
    Queues.clear();
    Maps.clear();
    for (uint32_t t = 0; t < num_threads; t++){
    	Queues.emplace_back(VQueue<uint32_t>(Node_Num));
    	Maps.emplace_back(vector<uint32_t>(Node_Num /32 + 1) );    	
      //cerr << (Maps[t][0]) << " " << Node_Num / (sizeof(Maps[t][0]) * 4) << endl;
    }
    Distances.resize(Node_Num);

   cerr << " Num of nodes " << Node_Num << ", num of edges " << Edge_Num << endl;
   // cerr << ". Done!" << endl;
}

uint32_t SSSP(uint32_t v)
{
	uint32_t threadID = __cilkrts_get_worker_number();    

	auto &Q = Queues[threadID];	
	int distance = 0;
	
	Q.clear();
	Q.push(v,0);
	Q.next();
	//cout << "Computing thread = " << threadID << endl;
	SetBit(threadID, v);
	
	
	//cout << "Computing v = " << v << " M = "<<Maps[threadID][v >> 5] <<endl;
	while (!Q.empty()) {
		distance++;
		while (!Q.empty()) {
			uint32_t s = Q.front();
			Q.pop();		
			for (uint32_t w : Edges[s]) {
				if (TestBit(threadID,w)) {
					//cout << "	found " << s << "-"<<w << endl;
					continue;
				}
				Q.push(w, distance);//Q.next();
				//cout << "	putting " << w << "-"<< TestBit(threadID,w) << ":"<<distance << "M="<<Maps[threadID][w >> 5] << endl;
				SetBit(threadID,w);
				//cout << "	puttinG " << s << "-"<< w << ":"<<distance << " M="<<Maps[threadID][w >> 5] << endl;
				
			}			
		}
		Q.next();
	}
	
	ResetMap(threadID);
	return Q.sum();
}

int main(int argc, char *argv[])
{
	if (argc < 2) {
        cout << "need more args..." << endl;
		cout << "	filename directed init_node node_num" << endl;
        return 0;
    }
    is_directed = atoi(argv[2]);
    //num_threads = atoi(argv[2]);
	

	Build(argv[1]);
	uint32_t n = Node_Num, init=0;
	if (argc == 4)	
		n = atoi(argv[3]);
	else if (argc == 5)	{
		init = atoi(argv[3]);
		n = atoi(argv[4]);
	}

	vector<tuple<uint32_t, int>> Distances;
	Distances.resize(Node_Num);
	if (argc == 5)	
		cout << "Computing Closeness Centrality from "<< init << " for " << n << " nodes ..." << endl;	
	else 
		cout << "Computing Closeness Centrality for "<< n << " nodes ..." << endl;	
	n += init;
	for (int i=1; i< 19; i++){
		//num_threads = i*2;
		__cilkrts_set_param("nworkers",to_string(i*2).data());
		cout << "NumThread = " << __cilkrts_get_nworkers() << endl;
		__cilkrts_init();
		double start = CycleTimer::currentSeconds();
		cilk_for (uint32_t v = init; v < n; v++){
			Distances[v] = make_tuple(SSSP(v),v);
		}
		cout << CycleTimer::currentSeconds() - start << "s" << endl;
	}	
		
	return 0;
}
