#ifndef CDCL_SOLVER_H
#define CDCL_SOLVER_H

#include <iostream>
#include <fstream> 
#include <vector>
#include <set> 
#include <deque> 
#include <string>
#include <cassert>
#include <map>
#include <cmath> 
#include <limits>
#include <cstdlib>

using namespace std;

struct Variable;

struct Clause {
    vector<int> lits;
    Variable* watched1;
    Variable* watched2;
};

// A variable is either unset, false or true.
enum class Value {
    unset, f, t
};

struct Variable {
    int bd = -1;
    Value value = Value::unset;
    vector<Clause*> pos_watched_occ;
    vector<Clause*> neg_watched_occ;
    Clause* reason = nullptr;
    int heap_position = 0;  // A variable's position in the heap, which is used to update the heap.
    double heu_pos_score = 0;
    double heu_neg_score = 0;
    int vs_pos_count = 0;
    int vs_neg_count = 0;
    double vm_pos_priority = 0;
    double vm_neg_priority = 0;
    
    int id();
    int var_to_lit();
    void set(Value, int);
    void unset();
};

enum class Heuristic {
    none, vsids, vmtf
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

void learn_clause(Clause*);

void backtrack(int, Clause*);

void unit_prop();

#endif