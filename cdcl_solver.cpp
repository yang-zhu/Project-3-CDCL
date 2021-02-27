#include "cdcl_solver.h"

vector<Variable> variables;
vector<Clause*> clauses;  // uses deque instead of vector to avoid dangling pointers
int orig_clause_num = 0;
vector<Variable*> assignments;
vector<Clause*> unit_clauses;
Heap unassigned_vars;
Heuristic heu = Heuristic::none;
int branchings = 0;
double top_priority = 0;

bool greater_than(Variable* v1, Variable* v2) {
    switch(heu) {
        case Heuristic::none:
            // Pick a variable randomly
            return rand() % 2 == 0;
        case Heuristic::vsids:
            return max(v1->heu_pos_score, v1->heu_neg_score) > max(v2->heu_pos_score, v2->heu_neg_score);
        case Heuristic::vmtf:
            return max(v1->vm_pos_priority, v2->vm_neg_priority) > max(v2->vm_pos_priority, v2->vm_neg_priority);
    }
}

// Pick a polarity for a variable.
Value pick_polarity(Variable* v) {
    switch(heu) {
        case Heuristic::none:
            return rand()%2 == 0 ? Value::t : Value::f;
        case Heuristic::vsids:
            return (v->heu_pos_score > v->heu_neg_score) ? Value::t : Value::f;
        case Heuristic::vmtf:
            return (v->vm_pos_priority > v->vm_neg_priority) ? Value::t : Value::f;
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
    unassigned_vars.remove(this);

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
                    assert(this == cl->watched1 || this == cl->watched2);
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
    bd = -1;
    reason = nullptr;
    unassigned_vars.insert(this);
}

Clause* add_unit_clause(vector<int> lits) {
    int first = lits[0];
    clauses.push_back(new Clause{lits, lit_to_var(first), lit_to_var(first)});
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
            for (int lit: lits) {
                (lit > 0 ? lit_to_var(lit)->heu_pos_score : lit_to_var(lit)->heu_neg_score) += 1;
            }
        }
        
        orig_clause_num = clauses.size();

        top_priority = num_clauses;
        for (Variable var: variables) {
            var.vm_pos_priority = var.heu_pos_score;
            var.vm_neg_priority = var.heu_neg_score;
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

void branching_count_incr(const vector<int>& lits) {
    for (int lit: lits) {
        (lit > 0 ? lit_to_var(lit)->vs_pos_count : lit_to_var(lit)->vs_neg_count) += 1;
    }
}

void learn_clause(Clause* cl) {
    int counter = assignments.size()-1;
    set<int> conflict_cl = set<int>(cl->lits.begin(), cl->lits.end());
    while (counter >= 0) {
        Variable* var = assignments[counter];
        if (var->bd == 0) {
            break;
        }
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
                vector<int> learned_cl_lits = vector<int>(conflict_cl.begin(), conflict_cl.end());
                Clause* learned_cl;
                if (learned_cl_lits.size() == 1) {
                    learned_cl = add_unit_clause(learned_cl_lits);
                } else {
                    vector<Variable*> watched;
                    for(int i = 0; i < 2;) {
                        if (conflict_cl.count(-assignments[counter]->var_to_lit()) == 1) {
                            watched.push_back(assignments[counter]);
                            ++i;
                        }
                        --counter;
                    }
                    learned_cl = add_clause(learned_cl_lits, -watched[0]->var_to_lit(), -watched[1]->var_to_lit());              
                }

                if (heu == Heuristic::vsids) {
                    branching_count_incr(learned_cl_lits);
                }

                if (heu == Heuristic::vmtf) {
                    sort(learned_cl_lits.begin(), learned_cl_lits.end(), [](int l1, int l2) { return (l1 > 0 ? lit_to_var(l1)->vm_pos_priority : lit_to_var(l1)->vm_neg_priority) < (l2 > 0 ? lit_to_var(l2)->vm_pos_priority : lit_to_var(l2)->vm_neg_priority); });

                    for (int i = 0; i < min<int>(learned_cl_lits.size(), 8); ++i) {
                        (learned_cl_lits[i] > 0 ? lit_to_var(learned_cl_lits[i])->vm_pos_priority : lit_to_var(learned_cl_lits[i])->vm_neg_priority) = top_priority + i;
                    }
                    top_priority = top_priority + min<int>(learned_cl_lits.size(), 8);
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

void backtrack(int depth, Clause* learned_cl) {
    unit_clauses.clear();
    while(!assignments.empty() && assignments.back()->bd > depth) {
        assignments.back()->unset();
        assignments.pop_back();
    }
    unit_clauses.push_back(learned_cl);
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
    int clauses_before = clauses.size();
    for (int i = orig_clause_num; i < clauses.size(); ++i) {
        if (clauses[i]->lits.size() > 5) {
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
        delete_watched_occ(var.pos_watched_occ);
        delete_watched_occ(var.neg_watched_occ);
    }
    for (int i = orig_clause_num; i < clauses.size();) {
        if (clauses[i]->to_be_deleted) {
            delete clauses[i];
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
            if (option == "-vsids") { heu = Heuristic::vsids; }
            else if (option == "-vmtf") { heu = Heuristic::vmtf; }
            else {
                cout << "Unknown argument: " << option << "\nPossible options:\n";
                cout << "-vsids\tuse the VSIDS heuristic\n";
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
    // There could be unit clauses in the original formula. If unit-propagation and pure literal elimination solve the whole formula, the following while-loop will not be executed.
    unit_prop();
    
    while (variables.size()-1 != assignments.size()) {   
        if (heu == Heuristic::vsids) {     
            if (branchings <= 225) {
                ++branchings;        
            } else {
                for(Variable var: variables) {
                    var.heu_pos_score = var.heu_pos_score/2 + var.vs_pos_count;
                    var.heu_neg_score = var.heu_neg_score/2 + var.vs_neg_count;
                    var.vs_pos_count = 0;
                    var.vs_neg_count = 0;
                    branchings = 0;
                }
                sort(unassigned_vars.heap.begin()+1, unassigned_vars.heap.end(), greater_than);
            }
        }

        if ((clauses.size()-orig_clause_num) % 100 == 0) { deletion(); }

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