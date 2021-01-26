#include "cdcl_solver.h"


Variable* lit_to_var(int lit) {
    return &variables[abs(lit)];
}

Value make_lit_true(int lit) {
    return lit > 0 ? Value::t : Value::f;
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
            backtrack();
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

vector<Variable> variables;
deque<Clause> clauses;  // uses deque instead of vector to avoid dangling pointers
vector<Variable*> assignments;
vector<Clause*> unit_clauses;

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
            vector<int> lits;
            for (int lit: lits_set) { lits.push_back(lit); }
            clauses.push_back(Clause{lits, lit_to_var(lits[0]), lit_to_var(lits.back())});
            Clause* cl = &clauses.back();
            if (lits.size() == 1) { unit_clauses.push_back(cl); }
            else {
                int first = lits[0];
                int second = lits.back();
                (first > 0 ? variables[first].pos_watched_occ : variables[-first].neg_watched_occ).push_back(cl);
                (second > 0 ? variables[second].pos_watched_occ : variables[-second].neg_watched_occ).push_back(cl);
            }
            
        }

        assert(variables.size() == num_vars+1);
    }
}