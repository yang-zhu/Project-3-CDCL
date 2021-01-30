#include "cdcl_solver.h"

vector<Variable> variables;
deque<Clause> clauses;  // uses deque instead of vector to avoid dangling pointers
vector<Variable*> assignments;
vector<Clause*> unit_clauses;

Variable* lit_to_var(int lit) {
    return &variables[abs(lit)];
}

Value make_lit_true(int lit) {
    return lit > 0 ? Value::t : Value::f;
}

int Variable::id() {
    return this - &variables[0];
}

int Variable::var_to_lit() {
    return this->value==Value::t ? this->id() : -(this->id());
}

void Variable::set(Value value, int bd) {
    this->value = value;
    this->bd = bd;
    assignments.push_back(this);

    vector<Clause*>& watched_occ = value == Value::t ? neg_watched_occ : pos_watched_occ;  
    for (int i = 0; i < watched_occ.size();) {
        Clause* cl = watched_occ[i];
        bool found_true = false;
        for (int lit: cl->lits) {
            if (lit_to_var(lit)->value == make_lit_true(lit)) {
                found_true = true;
                break;
            }
        }
        if (found_true) {
            ++i;
            continue;
        }
        
        if (cl->watched1->value != Value::unset && cl->watched2->value != Value::unset) {
            learn_clause(cl);
            return;
        } else {
            Variable* old_watched1 = cl->watched1;
            Variable* old_watched2 = cl->watched2;
            for (int j = 0; j < cl->lits.size(); ++j) {
                Variable* var = lit_to_var(cl->lits[j]);
                if (var == cl->watched1 || var == cl->watched2) { continue; }
                else if (var->value == Value::unset) {
                    (cl->watched1 == this ? cl->watched1 : cl->watched2) = var;
                    swap(watched_occ[i], watched_occ.back());
                    watched_occ.pop_back();
                    (cl->lits[j] > 0 ? var->pos_watched_occ : var->neg_watched_occ).push_back(cl);
                    break;
                }
            }
            if (cl->watched1 == old_watched1 && cl->watched2 == old_watched2) { 
                unit_clauses.push_back(cl);
                ++i;
            }
        }
    }
}

void Variable::unset() {
    value = Value::unset;
}

void add_unit_clause(vector<int> lits) {
    clauses.push_back(Clause{lits, nullptr, nullptr});
    Clause* cl = &clauses.back();
    unit_clauses.push_back(cl); 
}

void add_clause(const vector<int>& lits, int first, int second) {
    clauses.push_back(Clause{lits, lit_to_var(first), lit_to_var(second)});
    Clause* cl = &clauses.back();
    (first > 0 ? variables[first].pos_watched_occ : variables[-first].neg_watched_occ).push_back(cl);
    (second > 0 ? variables[second].pos_watched_occ : variables[-second].neg_watched_occ).push_back(cl);    
}

void fromFile(string path) {
    ifstream file = ifstream(path);
    string s;
    file >> s;

    // Read lines that start with "c" and ignore them.
    while (s == "c") {
        string line;
        getline(file, line);
        file >> s;
    }

    // Read the line that starts with "p" and get the number of variables as well as the number of clauses.
    if (s != "p") {
        cout << "The format of the file is wrong.\n";
        exit(1);
    } else {
        string cnf;
        int num_vars;
        int num_clauses;
        file >> cnf >> num_vars >> num_clauses;

        // Fill the vector of variables.
        variables.push_back(Variable());  // to allow indexing of variables to start from 1
        for (int i = 1; i < num_vars+1; ++i) {
            variables.push_back(Variable());
        }

        // Fill the deque of clauses.
        for (int i = 0; i < num_clauses; ++i) {
            set<int> lits_set;  // removes duplicate literals; for detecting tautological clause
            int lit;
            file >> lit;
            while (lit != 0) {
                lits_set.insert(lit);
                file >> lit;
            }
            
            // Only process non-tautological clauses.
            bool tautology = false;
            for (int lit: lits_set) {
                if (lits_set.count(-lit) > 0) {
                    tautology = true;
                    break;
                }
            }
            if (tautology) { continue; }
            
            vector<int> lits = vector<int>(lits_set.begin(), lits_set.end());
            if (lits.size() == 1) { add_unit_clause(lits); }
            else { add_clause(lits, lits[0], lits.back()); }
        }

        assert(variables.size() == num_vars+1);
    }
}

void resolution(Clause* cl, set<int>& lits, Variable* var) {
    for (int lit: cl->lits) {
        if (lit_to_var(lit) == var) {
            lits.erase(-lit);
            continue;
        }
        lits.insert(lit);
    }
}

void learn_clause(Clause* cl) {
    int counter = assignments.size()-1;
    set<int> conflict_cl = set<int>(cl->lits.begin(), cl->lits.end());
    while (true) {
        Variable* var = assignments[counter];
        if (conflict_cl.count(-var->var_to_lit()) == 1) {
            int max_bd = var->bd;
            resolution(var->reason, conflict_cl, var);
            int with_max_bd = 0;
            int assertion_level = 0;
            for (int lit: conflict_cl) {
                int lit_bd = lit_to_var(lit)->bd;
                if (lit_bd == max_bd) {
                    ++with_max_bd;
                } else {
                    assertion_level = max(assertion_level, lit_bd);
                }
                if (with_max_bd > 1) { break; }
            }
            
            if (with_max_bd == 1) {
                vector<int> learned_cl = vector<int>(conflict_cl.begin(), conflict_cl.end());
                if (learned_cl.size() == 1) {
                    add_unit_clause(learned_cl); 
                } else {
                    vector<Variable*> watched;
                    for(int i = 0; i < 2;) {
                        if (conflict_cl.count(-assignments[counter]->var_to_lit()) == 1) {
                            watched.push_back(assignments[counter]);
                            ++i;
                        }
                        --counter;
                    }
                    add_clause(learned_cl, -watched[0]->var_to_lit(), -watched[1]->var_to_lit());                   
                }                
                backtrack(assertion_level);
                return;
            }
        }
        --counter;
    }
}

void backtrack(int depth) {
    unit_clauses.clear();
    while(assignments.back()->bd > depth) {
        assignments.back()->unset();
        assignments.pop_back();
    }
}