#ifndef CDCL_SOLVER_H
#define CDCL_SOLVER_H

#include <iostream>
#include <fstream> 
#include <vector>
#include <set> 
#include <string>
#include <cassert>
#include <map>
#include <cmath> 
#include <limits>
#include <cstdlib>
#include <unordered_set>
#include <unordered_map>
#include <_types/_uint64_t.h>

using namespace std;

struct Variable;

struct Clause {
    vector<int> lits;
    Variable* watched1;
    Variable* watched2;
    bool to_be_deleted = false;
};

// A variable is either unset, false or true.
enum class Value {
    unset, f, t
};

struct Variable {
    int bd = -1;
    Value value = Value::unset;
    Value old_value = Value::unset;
    vector<Clause*> pos_watched_occ;
    vector<Clause*> neg_watched_occ;
    Clause* reason = nullptr;
    int heap_position = 0;  // A variable's position in the heap, which is used to update the heap.
    double vs_pos_score = 0;
    double vs_neg_score = 0;
    double vm_pos_score = 0;
    double vm_neg_score = 0;
    double pos_count = 0;
    double neg_count = 0;
    
    int id();
    int var_to_lit();
    void set(Value, int);
    void unset();
};

enum class Heuristic {
    vsids1, vsids2, vmtf
};

bool greater_than(Variable*, Variable*);

struct Heap {  // a max-heap
    vector<Variable*> heap{nullptr}; // Add a dummy element to simplify index computation.

    static int parent_ind(int ind) { return ind/2; }  // Return the index of the parent node of a node.
    static int l_child_ind(int ind) { return ind*2; }  // Return the index of the left child of a node.
    static int r_child_ind(int ind) { return ind*2+1; }  // Return the index of the right child of a node.
    // Return the index of the child with the maximum priority. When there is no child, return the index of the node.
    int max_child_ind(int i) const { 
        if (i*2+1 < heap.size()) { return greater_than(heap[i*2], heap[i*2+1]) ? i*2 : i*2+1; } 
        else if (i*2 < heap.size()) { return i*2; }
        else { return i; }
    }

    void insert(Variable*);
    void remove(Variable*);
    void move_up(Variable*);
    void move_down(Variable*);
    Variable* max();
};

enum class Preprocess {
    equisub, subs, niver, selfsubs
};

struct Preprocessor {
    set<set<int>>& clauses;
    unordered_map<int, unordered_set<const set<int>*>> lit_to_cl;
    unordered_map <const set<int>*, uint64_t> cl_sig;

    Preprocessor(set<set<int>>& clauses): clauses(clauses) {
        for (const set<int>& cl: clauses) {
            for (int l: cl) {
                lit_to_cl[l].insert(&cl);
            }
            cl_sig[&cl] = signature(cl);
        }
    }

    uint64_t signature(const set<int>& cl);
    set<int> get_all_vars();
    void add_clause(const set<int>& cl);
    void remove_clause(const set<int>* cl);
    void equivalence_substitution();
    void niver();
    bool subsumes(const set<int>& cl1, const set<int>& cl2);
    vector<const set<int>*> find_subsumed(const set<int>& cl);
    void eliminate_subsumed_clauses();
    void self_subsume();
};

#endif