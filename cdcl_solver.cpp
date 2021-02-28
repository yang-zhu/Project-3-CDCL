#include "cdcl_solver.h"

vector<Variable> variables;
vector<Clause*> clauses;
int orig_clause_num = 0;  // number of clauses contained in the orginal formula
vector<Variable*> assignments;
vector<Clause*> unit_clauses;
Heap unassigned_vars;
Heuristic heu = Heuristic::vmtf;
int branchings = 0;
double max_vm_score = 0;
int deletion_count_down = 100;

bool greater_than(Variable* v1, Variable* v2) {
    switch(heu) {
        case Heuristic::vsids1:
            return max(v1->vs_pos_score, v1->vs_neg_score) > max(v2->vs_pos_score, v2->vs_neg_score);
        case Heuristic::vsids2:
            return max(v1->pos_count, v1->neg_count) > max(v2->pos_count, v2->neg_count);
        case Heuristic::vmtf:
            return max(v1->vm_pos_score, v2->vm_neg_score) > max(v2->vm_pos_score, v2->vm_neg_score);
    }
}

// Pick a polarity for a variable.
Value pick_polarity(Variable* v) {
    switch(heu) {
        case Heuristic::vsids1:
            return (v->vs_pos_score > v->vs_neg_score) ? Value::t : Value::f;
        case Heuristic::vsids2:
            return (v->pos_count > v->neg_count) ? Value::t : Value::f;
        case Heuristic::vmtf:
            return (v->vm_pos_score > v->vm_neg_score) ? Value::t : Value::f;
    }
}

// Append a variable to the heap and re-sort the heap.
void Heap::insert(Variable* var) {
    heap.push_back(var);
    var->heap_position = heap.size()-1;
    move_up(var);
}

// Remove a variable from the heap and re-sort the heap.
void Heap::remove(Variable* var) {
    assert(var->heap_position < heap.size() && heap[var->heap_position] == var);
    if (var->heap_position == heap.size()-1) {
        heap.pop_back();
        return;
    }
    Variable* end_var = heap[heap.size()-1];
    swap(heap[var->heap_position], heap[heap.size()-1]);  // First swap the to-be-removed variable with the last variable.
    heap.pop_back();
    end_var->heap_position = var->heap_position;
    move_down(end_var);
}

// When a variable's priority is bigger than its parent's, it percolates up in the heap.
void Heap::move_up(Variable* var) {
    assert(var->heap_position < heap.size() && heap[var->heap_position] == var);
    int var_ind = var->heap_position;
    while (var_ind > 1) {
        Variable* parent = heap[parent_ind(var_ind)];
        if (greater_than(var, parent)) {
            swap(heap[var_ind], heap[parent_ind(var_ind)]);
            parent->heap_position = var_ind;
            var_ind = parent_ind(var_ind);
        } else { break; }
    }
    var->heap_position = var_ind;
}

// When a variable's priority is smaller than its children's, it percolates down in the heap.
void Heap::move_down(Variable* var) {
    assert(var->heap_position < heap.size() && heap[var->heap_position] == var);
    int var_ind = var->heap_position;
    while (true) {
        int max_child_ind = this->max_child_ind(var_ind);
        if (var_ind == max_child_ind || !greater_than(heap[max_child_ind], heap[var_ind])) { 
            break;
        } else {
            swap(heap[var_ind], heap[max_child_ind]);
            heap[var_ind]->heap_position = var_ind;
            var_ind = max_child_ind;
        }
    }
    heap[var_ind]->heap_position = var_ind;
}

Variable* Heap::max() {
    return this->heap[1];
}

Variable* lit_to_var(int lit) {
    return &variables[abs(lit)];
}

int Variable::id() {
    // a variable's position in the variables vector (starting from 1), which corresponds to the absolute value of its literal
    return this - &variables[0];
}

int Variable::var_to_lit() {
    return this->value==Value::t ? this->id() : -(this->id());
}

void Variable::set(Value value, int bd) {
    this->value = value;
    this->bd = bd;
    assignments.push_back(this);
    unassigned_vars.remove(this);

    vector<Clause*>& watched_occ = value == Value::t ? neg_watched_occ : pos_watched_occ;  
    for (int i = 0; i < watched_occ.size();) {
        Clause* cl = watched_occ[i];

        // when the clause is satisfied
        bool found_true = false;
        for (int lit: cl->lits) {
            Value lit_true = lit > 0 ? Value::t : Value::f;
            if (lit_to_var(lit)->value == lit_true) {
                found_true = true;
                break;
            }
        }
        if (found_true) {
            ++i;
            continue;
        }
        
        if (cl->watched1->value != Value::unset && cl->watched2->value != Value::unset) {
            // when all literals in the clause are set to false -> conflict arises
            learn_clause(cl);
            return;
        } else {
            Variable* old_watched1 = cl->watched1;
            Variable* old_watched2 = cl->watched2;
            for (int j = 0; j < cl->lits.size(); ++j) {
                Variable* var = lit_to_var(cl->lits[j]);
                if (var == cl->watched1 || var == cl->watched2) { continue; }
                else if (var->value == Value::unset) {
                    assert(this == cl->watched1 || this == cl->watched2);
                    // the two watched literals are not distinguished
                    (cl->watched1 == this ? cl->watched1 : cl->watched2) = var;
                    // deletes the clause for the set literal
                    swap(watched_occ[i], watched_occ.back());
                    watched_occ.pop_back();
                    // adds the clause to the watched occurrence vector of the new watched literal
                    (cl->lits[j] > 0 ? var->pos_watched_occ : var->neg_watched_occ).push_back(cl);
                    break;
                }
            }
            // If the watched literals are not changed, the clause is a unit clause.
            if (cl->watched1 == old_watched1 && cl->watched2 == old_watched2) { 
                unit_clauses.push_back(cl);
                ++i;
            }
        }
    }
}

void Variable::unset() {
    value = Value::unset;
    bd = -1;
    reason = nullptr;
    unassigned_vars.insert(this);
}


Clause* add_unit_clause(vector<int> lits) {
    int first = lits[0];
    clauses.push_back(new Clause{lits, lit_to_var(first), lit_to_var(first)});  // every clause is created on the heap
    Clause* cl = clauses.back();
    (first > 0 ? variables[first].pos_watched_occ : variables[-first].neg_watched_occ).push_back(cl);
    unit_clauses.push_back(cl);
    return cl;
}

Clause* add_clause(const vector<int>& lits, int first, int second) {
    clauses.push_back(new Clause{lits, lit_to_var(first), lit_to_var(second)});
    Clause* cl = clauses.back();
    (first > 0 ? variables[first].pos_watched_occ : variables[-first].neg_watched_occ).push_back(cl);
    (second > 0 ? variables[second].pos_watched_occ : variables[-second].neg_watched_occ).push_back(cl);
    return cl;   
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
            // choose two arbitrary literals as the watched literals of the clause
            else { add_clause(lits, lits[0], lits.back()); }
            
            for (int lit: lits) {
                (lit > 0 ? lit_to_var(lit)->vs_pos_score : lit_to_var(lit)->vs_neg_score) += 1;
            }
        }
        
        orig_clause_num = clauses.size();

        if (heu == Heuristic::vmtf) {
            max_vm_score = num_clauses;  // no literal's number of occurrences could exceed the number of clauses
            for (Variable& var: variables) {
                // VMTF initially sorts the literals according to the number of occurrences. To simulate this, we assign the number of occurences as initial score.
                var.vm_pos_score = var.vs_pos_score;
                var.vm_neg_score = var.vs_neg_score;
                var.pos_count = var.vs_pos_score;
                var.neg_count = var.vs_pos_score;
            }
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
        lits.insert(lit);  // lits as a set will eliminate all the duplicate literals (the two clauses could have several shared literals)
    }
}

void count_incr(const vector<int>& lits) {
    for (int lit: lits) {
        (lit > 0 ? lit_to_var(lit)->pos_count : lit_to_var(lit)->neg_count) += 1;
    }
}

double get_vm_count(int lit) {
    return lit > 0 ? lit_to_var(lit)->pos_count : lit_to_var(lit)->neg_count;
}

// Derives an asserting conflict clause
void learn_clause(Clause* cl) {
    int counter = assignments.size()-1;
    set<int> conflict_cl = set<int>(cl->lits.begin(), cl->lits.end());
    while (counter >= 0) {
        Variable* var = assignments[counter];
        if (var->bd == 0) {
            break;
        }
        // Only clauses that contribute to the conflict will be taken into account.
        if (conflict_cl.count(-var->var_to_lit()) == 1) {  // the literal has to be false under the current assignment
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
                vector<int> learned_cl_lits = vector<int>(conflict_cl.begin(), conflict_cl.end());
                Clause* learned_cl;
                if (learned_cl_lits.size() == 1) {
                    learned_cl = add_unit_clause(learned_cl_lits);
                } else {
                    vector<Variable*> watched;
                    // The two watched literals in the new asserting conflict clause are the shallowest in the assignment stack. This way we make sure that they are the first to be unset in backtracking.
                    for(int i = 0; i < 2;) {
                        if (conflict_cl.count(-assignments[counter]->var_to_lit()) == 1) {
                            watched.push_back(assignments[counter]);
                            ++i;
                        }
                        --counter;
                    }
                    learned_cl = add_clause(learned_cl_lits, -watched[0]->var_to_lit(), -watched[1]->var_to_lit());              
                }

                // Increments the counters for the literals in the newly learned clause.
                count_incr(learned_cl_lits); 
                if (heu == Heuristic::vmtf) {
                    // Sorts the literals descendingly according to their counters.
                    sort(learned_cl_lits.begin(), learned_cl_lits.end(), [](int l1, int l2) { return get_vm_count(l1) > get_vm_count(l2); });

                    // Picks at most 8 literals to move to the front (increase their vmtf heuristic scores).
                    int num_moved_vars = min<int>(learned_cl_lits.size(), 8);
                    for (int i = 0; i < num_moved_vars; ++i) {
                        // Adding max_vm_score makes sure that the new scores surpass all the other literals' scores -> move to the front of the list
                        int lit = learned_cl_lits[i];
                        (lit > 0 ? lit_to_var(lit)->vm_pos_score : lit_to_var(lit)->vm_neg_score) = max_vm_score + num_moved_vars - i;
                    }
                    max_vm_score = max_vm_score + num_moved_vars;
                }
                backtrack(assertion_level, learned_cl);
                return;
            }
        }
        --counter;
    }
    cout << "s UNSATISFIABLE\n";
    exit(0);
}

// Backtracking
void backtrack(int depth, Clause* learned_cl) {
    unit_clauses.clear();
    while(!assignments.empty() && assignments.back()->bd > depth) {
        assignments.back()->unset();
        assignments.pop_back();
    }
    unit_clauses.push_back(learned_cl);
    --deletion_count_down;
}

// Unit propagation
void unit_prop() {
    while (!unit_clauses.empty()) {
        Clause* cl = unit_clauses.back();
        unit_clauses.pop_back();
        for (int lit: cl->lits) {
            Variable* var = lit_to_var(lit);
            if (var->value == Value::unset) {  // A clause does not keep track of which literals are unassigned.
                var->reason = cl;
                // cur_bd is the current global branching depth. Initially the branching depth is set to 0 for all literals in unit clauses.
                int cur_bd = assignments.empty() ? 0 : assignments.back()->bd;
                if (lit > 0) {
                    var->set(Value::t, cur_bd);
                } else {
                    var->set(Value::f, cur_bd);
                }
                break;
            }
        }
    }
}


void delete_watched_occ(vector<Clause*>& watched_occ) {
    watched_occ.erase(remove_if(watched_occ.begin(), watched_occ.end(), [](Clause* cl) { return cl->to_be_deleted; }), watched_occ.end());
}

void deletion() {
    // Deletes learned clauses that are more than 5 literals wide and contain more than two literals unassigned.
    int clauses_before = clauses.size();
    for (int i = orig_clause_num; i < clauses.size(); ++i) {
        if (clauses[i]->lits.size() > 3) {
            int count = 0;
            for (int lit: clauses[i]->lits) {
                if (lit_to_var(lit)->value == Value::unset) { ++count; }
                if (count == 2) {
                    clauses[i]->to_be_deleted = true;
                    break;
                }
            }
        }
    }
    for (Variable& var: variables) {
        // Removes the to-be-deleted learned clauses from the watched occurrences vector of every variable.
        delete_watched_occ(var.pos_watched_occ);
        delete_watched_occ(var.neg_watched_occ);
    }
    for (int i = orig_clause_num; i < clauses.size();) {
        if (clauses[i]->to_be_deleted) {
            // first frees the memory on the heap
            delete clauses[i];
            // then deletes the pointer from the clauses vector
            swap(clauses[i], clauses.back());
            clauses.pop_back();
        } else {
            ++i;
        }
    }
}


int main(int argc, const char* argv[]) {
    string filename;
     
    for (int i = 1; i < argc; ++i) {
        string option = string(argv[i]);
        
        if (option[0] == '-') {
            if (option == "-vsids1") { heu = Heuristic::vsids1; }
            else if (option == "-vsids2") { heu = Heuristic::vsids2; }
            else if (option == "-vmtf") { heu = Heuristic::vmtf; }
            else {
                cout << "Unknown argument: " << option << "\nPossible options:\n";
                cout << "-vsids1\tuse the VSIDS heuristic\n";
                cout << "-vsids2\tuse the VSIDS heuristic\n";
                cout << "-vmtf\tuse the VMTF heuristic\n";
                exit(1);
            }
        } else { filename = option; }
    }
    // When no file name is given.
    if (filename == "") {
        cout << "No filename specified\n";
        cout << "usage: cdcl_solver <path to a cnf file> [heuristics]\n";
        exit(1);
    }

    fromFile(filename);
    // Fill the unassigned_vars heap. Originally all variables are unassigned.
    for (int i = 1; i < variables.size(); ++i) {
        unassigned_vars.insert(&variables[i]);
    }
    // There could be unit clauses in the original formula. If unit-propagation solves the whole formula, the following while-loop will not be executed.
    unit_prop();
    
    while (variables.size()-1 != assignments.size()) {   
        if (heu == Heuristic::vsids1 || heu == Heuristic::vsids2) {
            // only resort the heap when certain number of branchings is reached
            if (branchings <= 255) {
                ++branchings;        
            } else {
                for(Variable& var: variables) {
                    if (heu == Heuristic::vsids1) {
                        var.vs_pos_score = var.vs_pos_score/2 + var.pos_count;
                        var.vs_neg_score = var.vs_neg_score/2 + var.neg_count;
                        var.pos_count = 0;
                        var.neg_count = 0;
                        branchings = 0;
                    } else {
                        var.pos_count /= 2;
                        var.neg_count /= 2;
                        branchings = 0;
                    }
                }
                if (heu == Heuristic::vsids1) {
                    for (int i = unassigned_vars.heap.size()-1; i > 0; --i) {
                        unassigned_vars.move_down(unassigned_vars.heap[i]);
                    }
                }
            }
        }

        // Every time another 100 clauses are learned, we try to delete clauses. 
        if (deletion_count_down <= 0) {
            deletion_count_down = 100;
            deletion(); 
        }

        // Always pick the variable of highest priority to branch on.
        Variable* picked_var = unassigned_vars.max();
        picked_var->set(pick_polarity(picked_var), assignments.empty() ? 1 : assignments.back()->bd+1);
        unit_prop();
    }
    cout << "s SATISFIABLE\n";
    cout << "v ";
    for (int i = 1; i < variables.size(); ++i) {
        cout << ((variables[i].value == Value::t) ? i : -i) << " ";
    }
    cout << "0\n";
    return 0;
}