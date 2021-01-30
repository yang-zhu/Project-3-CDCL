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
    int bd = 0;
    Value value = Value::unset;
    vector<Clause*> pos_watched_occ;
    vector<Clause*> neg_watched_occ;
    Clause* reason;
    
    int id();
    int var_to_lit();
    void set(Value, int);
    void unset();
};

void backtrack(int, Clause*);

#endif