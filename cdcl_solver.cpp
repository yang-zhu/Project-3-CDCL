#include "cdcl_solver.h"

vector<Variable> variables;

vector<Clause*> orig_clauses; // original clauses cannot be deleted
vector<Clause*> learned_clauses;  // learned clauses can be deleted

vector<Variable*> assignments; // the assignment stack
vector<Clause*> unit_clauses;
Heap unassigned_vars;

Heuristic heuristic = Heuristic::vsids2;
int branchings = 0;
double max_vm_score = 0; // maximal VMTF score assigned so far

int deletion_count_down = 100;
int kept_clauses = 100;
int kept_clauses_growth = 400;
int kept_clause_width = 5;
int kept_clause_unset_lits = 4;
int unset_lits_weight = 5;

int restart_interval = 200;
int restart_count_down;
double interval_growth = 1.2;
bool phase_saving = true;

vector<Preprocess> preprocessings;
vector<pair<set<int>, int>> eliminated_clause_var_pair;  // stores eliminated variables together with the removed clauses

set<set<int>> original_formula; // stores the original formula to verify satisfying assignments

ofstream* proof_file = nullptr;

bool greater_than(Variable* v1, Variable* v2) {
    switch(heuristic) {
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
    if (phase_saving && v->old_value != Value::unset) {
        return v->old_value;
    } else {
        switch(heuristic) {
            case Heuristic::vsids1:
                return (v->vs_pos_score > v->vs_neg_score) ? Value::t : Value::f;
            case Heuristic::vsids2:
                return (v->pos_count > v->neg_count) ? Value::t : Value::f;
            case Heuristic::vmtf:
                return (v->vm_pos_score > v->vm_neg_score) ? Value::t : Value::f;
        }
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

bool Heap::empty() {
    return this->heap.size() == 1;
}


void log_new_clause(const set<int>& lits) {
    if (proof_file) {
        for (int lit: lits) {
            *proof_file << lit << " ";
        }
            *proof_file << "0\n";
    }
}

template<class T>
void log_deleted_clause(const T& lits) {  // lits could be a set (in preprocessing stage) or a vector
    if (proof_file) {
        *proof_file << "d ";
        for (int lit: lits) {
            *proof_file << lit << " ";
        }
        *proof_file << "0\n";
    }
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

Value make_lit_true(int lit) {
    return lit > 0 ? Value::t : Value::f;
}

template<class T>
bool clause_satisfied_check(const T& lits) {
    for (int l: lits) {
        if (lit_to_var(l)->value == make_lit_true(l)) {
            return true;
        }
    }
    return false;
}

void learn_clause(Clause*);

void Variable::set(Value value, int bd) {
    this->value = value;
    this->bd = bd;
    assignments.push_back(this);
    unassigned_vars.remove(this);

    vector<Clause*>& watched_occ = value == Value::t ? neg_watched_occ : pos_watched_occ;  
    for (int i = 0; i < watched_occ.size();) {
        Clause* cl = watched_occ[i];

        // when the clause is satisfied
        if (clause_satisfied_check(cl->lits)) {
            ++i;
            continue;
        }
        
        if (cl->watched1->value != Value::unset && cl->watched2->value != Value::unset) {
            // when all literals in the clause are set to false -> conflict arises
            --restart_count_down;
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
    old_value = value;
    value = Value::unset;
    bd = -1;
    reason = nullptr;
    unassigned_vars.insert(this);
}

bool tautology_check(set<int> lits) {
    for (int lit: lits) {
        if (lits.count(-lit) > 0) {
            return true;
        }
    }
    return false;
}

template <class T>
set<int> resolution(const T& cl1, set<int> cl2, int var) {
    for (int lit: cl1) {
        if (abs(lit) == var) {
            cl2.erase(-lit);
            continue;
        }
        cl2.insert(lit);
    }
    return cl2;
}

void exit_unsatisfiable() {
    cout << "s UNSATISFIABLE\n";
    delete proof_file;
    exit(0);
}


set<int> Preprocessor::get_all_vars() {
    set<int> vars = {};
    for (const pair<int, unordered_set<const set<int>*>>& p: lit_to_cl) {
        vars.insert(abs(p.first));
    }
    return vars;
}

void Preprocessor::add_clause(const set<int>& cl) {
    auto it = clauses.insert(cl).first;  // returns an iterator to the inserted element if the element does not exist, otherwise returns an iterator to the existing element
    for (int l: cl) {
        lit_to_cl[l].insert(&*it);
    }
    cl_sig[&*it] = signature(cl);
    log_new_clause(cl);
}

void Preprocessor::remove_clause(const set<int>* cl) {
    for (int l: *cl) {
        lit_to_cl[l].erase(cl);
    }
    cl_sig.erase(cl);
    log_deleted_clause(*cl);
    clauses.erase(*cl);
}

// Equivalence Substitution
void Preprocessor::equivalence_substitution() {
    bool changed;
    do {
        changed = false;
        set<set<int>> clauses_copy = clauses;
        for (const set<int>& cl1: clauses_copy) {  // iterates over the copy instead of the original set, because we are modifying it along the way
            if (cl1.size() == 2) {
                int fst = *cl1.begin();
                int snd = *(++cl1.begin());
                if (clauses.count({-fst, -snd}) > 0) {
                    changed = true;
                    unordered_set<const set<int>*> to_be_modified = lit_to_cl[snd];
                    to_be_modified.insert(lit_to_cl[-snd].begin(), lit_to_cl[-snd].end());
                    for (const set<int>* cl2: to_be_modified) {
                        set<int> new_cl = *cl2;
                        int target = new_cl.count(snd) > 0 ? snd : -snd;
                        new_cl.erase(target);
                        new_cl.insert(target == snd ? -fst : fst);
                        if (!tautology_check(new_cl)) {
                            add_clause(new_cl);
                        }
                    }
                    // The original clauses are deleted in the end, because we do not want to delete the two clauses {fst, snd} and {-first, -snd} too early, since they are used in the proof file to justify the newly added clauses.
                    for (const set<int>* cl2: to_be_modified) {
                        eliminated_clause_var_pair.push_back(make_pair(*cl2, abs(snd)));
                        remove_clause(cl2);
                    }
                }
            }
        }
    } while (changed);
}

// Non-increasing Variable Elimination Resolution (NiVER)
void Preprocessor::niver() {
    set<int> vars = get_all_vars();

    bool changed;
    do {
        changed = false;
        for (int v: vars) {
            unordered_set<const set<int>*>& pos_res = lit_to_cl[v];
            unordered_set<const set<int>*>& neg_res = lit_to_cl[-v];
            // The method is only applied to variables x where x or ¬x has at most 10 occurrences.
            if (min(pos_res.size(), neg_res.size()) <= 10) {
                set<set<int>> new_clauses = {};
                int occurrences = pos_res.size() + neg_res.size();
                if (occurrences == 0) { continue; }  // in this case, changed should remain false
                for (const set<int>* cl1: pos_res) {
                    for (const set<int>* cl2: neg_res) {
                        set<int> new_cl = resolution(*cl1, *cl2, v);
                        if (!tautology_check(new_cl) && clauses.count(new_cl) == 0) {  // a new clause derived from resolution that already exists in the clauses set is not counted in
                            new_clauses.insert(move(new_cl)); 
                        }
                        if (new_clauses.size() > occurrences) {
                            goto next_var;
                        }
                    }
                }
                for (const set<int>& cl: new_clauses) {
                    add_clause(cl);
                }
                unordered_set<const set<int>*> to_delete_cls = pos_res;
                to_delete_cls.insert(neg_res.begin(), neg_res.end());
                for (const set<int>* cl: to_delete_cls) {
                    eliminated_clause_var_pair.push_back(make_pair(*cl, v));
                    remove_clause(cl);
                }
                changed = true;
            }
            next_var:;
        }
    } while(changed);
}

uint64_t Preprocessor::signature(const set<int>& cl) {
    uint64_t cl_bits = 0;
    for (int l: cl) {
        l = abs(l) % 64;  // hash function
        uint64_t l_bits = uint64_t{1} << l;
        cl_bits |= l_bits;
    }
    return cl_bits;
}

// Subsumption testing: tests if cl1 subsumes cl2
bool Preprocessor::subsumes(const set<int>& cl1, const set<int>& cl2) {
    if ((cl_sig.at(&cl1) & ~cl_sig.at(&cl2)) != 0) {
        return false;
    } else {
        for (int l: cl1) {
            if (cl2.count(l) == 0) {
                return false;
            }
        }
    }
    return true;
}

// Collects clauses that are subsumed by the clause subset.
vector<const set<int>*> Preprocessor::find_subsumed(const set<int>& subset) {
    vector<const set<int>*> subsumed;
    // for efficiency we only consider the literal that appears least often
    int min_size = numeric_limits<int>::max();
    int min_lit = 0;
    for (int l: subset) {
        if (lit_to_cl[l].size() < min_size) {
            min_size = lit_to_cl[l].size();
            min_lit = l;
        }
    }
    unordered_set<const set<int>*>& supers = lit_to_cl[min_lit];
    for (const set<int>* super: supers) {
        if (subsumes(subset, *super)) {
            subsumed.push_back(super);
        }
    }
    return subsumed;
}

// Eliminates subsumed clauses from the formula
void Preprocessor::eliminate_subsumed_clauses() {
    for (const set<int>& cl1: clauses) {
        for (const set<int>* cl2: find_subsumed(cl1)) {
            if (&cl1 != cl2) {
                remove_clause(cl2);
            }
        }
    }
}

// Self-Subsuming Resolution
void Preprocessor::self_subsume() {
    set<int> vars = get_all_vars();
    for (int v: vars) {
        for (const set<int>* cl1: lit_to_cl[v]) {
            set<int> subset = *cl1;
            subset.erase(v);
            subset.insert(-v);
            // &subset does not exist in cl_sig. Therefore we add it in cl_sig on the fly and delete it afterwards.
            cl_sig[&subset] = signature(subset);
            // If a clause D is subsumed by (C\a) ∪ ¬a, then D can be strengthened to D\¬a.
            for (const set<int>* cl2: find_subsumed(subset)) {
                set<int> new_cl = *cl2;
                new_cl.erase(-v);
                add_clause(new_cl);
                remove_clause(cl2);
            }
            cl_sig.erase(&subset);
        }
    }
}


void after_preprocessing(set<set<int>>&);

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
        delete proof_file;
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

        set<set<int>> clauses_lits;
        for (int i = 0; i < num_clauses; ++i) {
            set<int> lits_set;  // removes duplicate literals; for detecting tautological clauses
            int lit;
            file >> lit;
            while (lit != 0) {
                lits_set.insert(lit);
                file >> lit;
            }

            original_formula.insert(lits_set);
            
            // Only process non-tautological clauses.
            if (tautology_check(lits_set)) { continue; }

            clauses_lits.insert(lits_set);          
        }

        if (!preprocessings.empty()) {
            Preprocessor prep = Preprocessor(clauses_lits);
            for (Preprocess p: preprocessings) {
                switch(p) {
                    case Preprocess::equisub:
                        prep.equivalence_substitution();
                        break;
                    case Preprocess::subs:
                        prep.eliminate_subsumed_clauses();
                        break;
                    case Preprocess::niver:
                        prep.niver();
                        break;
                    case Preprocess::selfsubs:
                        prep.self_subsume();
                        break;
                }
            }
        }

        after_preprocessing(clauses_lits);
    }
}


Clause* add_unit_clause(const vector<int>& lits, vector<Clause*>& clauses) {
    int first = lits[0];
    Clause* cl = new Clause{lits, lit_to_var(first), lit_to_var(first)};  // every clause is created on the heap
    clauses.push_back(cl);
    (first > 0 ? variables[first].pos_watched_occ : variables[-first].neg_watched_occ).push_back(cl);
    unit_clauses.push_back(cl);
    return cl;
}

Clause* add_clause(const vector<int>& lits, vector<Clause*>& clauses, int first, int second) {
    Clause* cl = new Clause{lits, lit_to_var(first), lit_to_var(second)};
    clauses.push_back(cl);
    (first > 0 ? variables[first].pos_watched_occ : variables[-first].neg_watched_occ).push_back(cl);
    (second > 0 ? variables[second].pos_watched_occ : variables[-second].neg_watched_occ).push_back(cl);
    return cl;   
}

void after_preprocessing(set<set<int>>& clauses) {
    for (set<int> lits_set: clauses) {
        if (!lits_set.empty()) {
            vector<int> lits = vector<int>(lits_set.begin(), lits_set.end());
            if (lits.size() == 1) { add_unit_clause(lits, orig_clauses); }
            // choose two arbitrary literals as the watched literals of the clause
            else { add_clause(lits, orig_clauses, lits[0], lits[1]); }
            
            for (int lit: lits) {
                (lit > 0 ? lit_to_var(lit)->vs_pos_score : lit_to_var(lit)->vs_neg_score) += 1;
            }
        } else {
            exit_unsatisfiable();
        }
    }

    if (heuristic == Heuristic::vmtf) {
        max_vm_score = orig_clauses.size();  // no literal's number of occurrences could exceed the number of clauses
        for (Variable& var: variables) {
            // VMTF initially sorts the literals according to the number of occurrences. To simulate this, we assign the number of occurences as initial score.
            var.vm_pos_score = var.vs_pos_score;
            var.vm_neg_score = var.vs_neg_score;
            var.pos_count = var.vs_pos_score;
            var.neg_count = var.vs_pos_score;
        }
    }
}


// Reduces the size of the learned clause
void minimize_clause(set<int>& cl) {
    for (auto it = cl.begin(); it != cl.end();) {
        bool remove = true;
        if (lit_to_var(*it)->reason) {  // a branching literal does not have a reason
            for (int l: lit_to_var(*it)->reason->lits) {
                if (l != -*it && cl.count(l) == 0) { 
                    remove = false;
                    break;
                }
            }
        } else {
            remove = false;
        }
        if (remove) {
            it = cl.erase(it);
        } else {
            ++it;
        }
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

void backtrack(int);

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
            conflict_cl = resolution(var->reason->lits, move(conflict_cl), var->id());
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
                minimize_clause(conflict_cl);
                vector<int> learned_cl_lits = vector<int>(conflict_cl.begin(), conflict_cl.end());
                Clause* learned_cl;
                if (learned_cl_lits.size() == 1) {
                    learned_cl = add_unit_clause(learned_cl_lits, learned_clauses);
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
                    learned_cl = add_clause(learned_cl_lits, learned_clauses, -watched[0]->var_to_lit(), -watched[1]->var_to_lit());              
                }

                log_new_clause(conflict_cl); 

                // Increments the counters for the literals in the newly learned clause.
                count_incr(learned_cl_lits);
                if (heuristic == Heuristic::vmtf) {
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
                backtrack(assertion_level);
                unit_clauses.push_back(learned_cl);
                return;
            }
        }
        --counter;
    }
    exit_unsatisfiable();
}

// Backtracking
void backtrack(int depth) {
    unit_clauses.clear();
    while(!assignments.empty() && assignments.back()->bd > depth) {
        assignments.back()->unset();
        assignments.pop_back();
    }
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


int clause_score (Clause* cl) {
    int unset_lits = 0;
    for (int l: cl->lits) {
        if (lit_to_var(l)->value == Value::unset) { ++unset_lits; }
    }
    // learned clauses within a certain width and a certain amount of unassigned literals are not deleted
    if (unset_lits <= kept_clause_unset_lits && cl->lits.size() <= kept_clause_width) {
       return 0;
    }
    return unset_lits == 0 ? 0 : unset_lits_weight*unset_lits+cl->lits.size();
}

void delete_watched_occ(vector<Clause*>& watched_occ) {
    watched_occ.erase(remove_if(watched_occ.begin(), watched_occ.end(), [](Clause* cl) { return cl->to_be_deleted; }), watched_occ.end());
}

void deletion(int budget) {   
    vector<pair<Clause*,int>> cl_to_score = {};
    for (Clause* cl: learned_clauses) {
        cl_to_score.push_back(make_pair(cl, clause_score(cl)));
    }
    // sorts the learned clauses ascendingly according to their scores
    sort(cl_to_score.begin(), cl_to_score.end(), [](pair<Clause*,int> p1, pair<Clause*,int> p2) { return p1.second < p2.second; });

    for (int i = budget; i < cl_to_score.size(); ++i) {
        pair<Clause*,int> p = cl_to_score[i];
        if (p.second == 0) { continue; }
        p.first->to_be_deleted = true;
        log_deleted_clause(p.first->lits);
    }
    
    for (Variable& var: variables) {
        // Removes the to-be-deleted learned clauses from the watched occurrences vector of every variable.
        delete_watched_occ(var.pos_watched_occ);
        delete_watched_occ(var.neg_watched_occ);
    }
    for (int i = 0; i < learned_clauses.size();) {
        if (learned_clauses[i]->to_be_deleted) {
            // first frees the memory on the heap
            delete learned_clauses[i];
            // then deletes the pointer from the clauses vector
            swap(learned_clauses[i], learned_clauses.back());
            learned_clauses.pop_back();
        } else {
            ++i;
        }
    }
}


void solve() {
    // There could be unit clauses in the original formula. If unit-propagation solves the whole formula, the following while-loop will not be executed.
    unit_prop();
    
    while (!unassigned_vars.empty()) {   
        if (heuristic == Heuristic::vsids1 || heuristic == Heuristic::vsids2) {
            // only resort the heap when certain number of branchings is reached
            if (branchings <= 255) {
                ++branchings;        
            } else {
                for(Variable& var: variables) {
                    if (heuristic == Heuristic::vsids1) {
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
                if (heuristic == Heuristic::vsids1) {
                    // In VSIDS1 the heap has to be resorted explicitly, because the variables may either move up or down in the heap. VSIDS2 does not need this because it only uses pos_count/neg_count, which are only updated when the variable is assigned and assigned variables are not part of the heap.
                    for (int i = unassigned_vars.heap.size()-1; i > 0; --i) {
                        // heapify the heap from bottom to top
                        unassigned_vars.move_down(unassigned_vars.heap[i]);
                    }
                }
            }
        }

        // We have two restarts strategies, one restarts with a fixed interval, the other one restarts with an interval that grows exponentially. The fixed interval policy sets the interval_growth to 1. 
        if (restart_count_down <= 0) {
            backtrack(0);  // backtracking till the branching depths of variables on the assignments stack are 0 will clear all the branching literals
            restart_count_down = restart_interval;
            restart_interval = restart_interval * interval_growth;
        }

        // We have two deletion strategies: 
        // 1. We keep a budget of learned clauses and the budget grows linearly
        // 2. We do not keep a budget by setting the kept_clauses and kept_clauses_growth to 0. Instead we use the kept_clause_width and kept_clause_unset_lits to control the number of kept clauses.
        if (deletion_count_down < 0) {
            deletion(kept_clauses);
            kept_clauses += kept_clauses_growth;
            deletion_count_down = learned_clauses.size();
        }

        // Always pick the variable of highest priority to branch on.
        Variable* picked_var = unassigned_vars.max();
        picked_var->set(pick_polarity(picked_var), assignments.empty() ? 1 : assignments.back()->bd+1);
        unit_prop();
    }
}


int main(int argc, const char* argv[]) {
    string filename;
     
    for (int i = 1; i < argc; ++i) {
        string option = string(argv[i]);
        
        if (option[0] == '-') {
            if (option == "-vsids1") { heuristic = Heuristic::vsids1; }
            else if (option == "-vsids2") { heuristic = Heuristic::vsids2; }
            else if (option == "-vmtf") { heuristic = Heuristic::vmtf; }
            else if (option == "-equisub") { preprocessings.push_back(Preprocess::equisub); }
            else if (option == "-subs") { preprocessings.push_back(Preprocess::subs); }
            else if (option == "-niver") { preprocessings.push_back(Preprocess::niver); }
            else if (option == "-selfsubs") { preprocessings.push_back(Preprocess::selfsubs); }
            else if (option == "-kept_clauses") {
                kept_clauses = stoi(argv[i+1]);
                ++i;
            }
            else if (option == "-kept_clauses_growth") {
                kept_clauses_growth = stoi(argv[i+1]);
                ++i;
            }
            else if (option == "-kept_clause_width") {
                kept_clause_width = stoi(argv[i+1]);
                ++i;
            }
            else if (option == "-kept_clause_unset_lits") {
                kept_clause_unset_lits = stoi(argv[i+1]);
                ++i;
            }
            else if (option == "-unset_lits_weight") {
                unset_lits_weight = stoi(argv[i+1]);
                ++i;
            }
            else if (option == "-restart_interval") {
                restart_interval = stoi(argv[i+1]);
                ++i;
            }
            else if (option == "-interval_growth") {
                interval_growth = stod(argv[i+1]);
                ++i;
            }
            else if (option == "-no_phase_saving") {
                phase_saving = false;
            }
            else if (option == "-proof") {
                proof_file = new ofstream(argv[i+1]);
                ++i;
            }
            else {
                cout << "Unknown argument: " << option << "\nPossible options:\n";
                cout << "-vsids1    use the VSIDS heuristic (by-the-book implementation)\n";
                cout << "-vsids2    use the VSIDS heuristic (directly update the score in the heap)\n";
                cout << "-vmtf      use the VMTF heuristic\n";
                cout << "\n";
                cout << "-equisub   apply equivalence substitution in preprocessing\n";
                cout << "-niver     apply NiVER in preprocessing\n";
                cout << "-subs      apply subsumption testing in preprocessing\n";
                cout << "-selfsubs  apply self-subsuming resolution in preprocessing\n";
                cout << "\n";
                cout << "-kept_clauses <int>            initial budget of learned clauses to be kept\n";
                cout << "-kept_clauses_growth <int>     rate by which kept_clauses grows\n";
                cout << "-kept_clause_unset_lits <int>  upper bound of number of unset literals in kept learned clauses independent of budget\n";
                cout << "-kept_clause_width <int>       upper bound of width of kept learned clauses independent of budget\n";
                cout << "-unset_lits_weight <int>       the weight for kept_clause_unset_lits while computing the scores for learned clauses\n";
                cout << "\n";
                cout << "-restart_inverval <int>    the initial interval of restarts\n";
                cout << "-inverval_growth <double>  factor by which restart_interval grows\n";
                cout << "-no_phase_saving           disable phase saving\n";
                cout << "\n";
                cout << "-proof <filename>      writes the proof in DRAT format into a file\n";
                exit(1);
            }
        } else { filename = option; }
    }
    // When no file name is given.
    if (filename == "") {
        cout << "No filename specified\n";
        cout << "usage: cdcl_solver <path to a cnf file> [options]\n";
        exit(1);
    }
    
    restart_count_down = restart_interval;

    fromFile(filename);
    set<Variable*> vars;
    for (Clause* cl: orig_clauses) {
        for (int l: cl->lits) {
            vars.insert(lit_to_var(l));
        }
    }
    for (Variable* var: vars) {
        unassigned_vars.insert(var);
    }
    
    solve();

    // Computes the assignments for eliminated variables
    for (int i = eliminated_clause_var_pair.size()-1; i >= 0; --i) {
        set<int>& cl = eliminated_clause_var_pair[i].first;
        int var = eliminated_clause_var_pair[i].second;
        if (!clause_satisfied_check(cl)) {
            for (int l: cl) {
                if (abs(l) == var) {
                    assert(variables[var].value == Value::unset);
                    variables[var].value = make_lit_true(l);
                } else if (lit_to_var(l)->value == Value::unset) {
                    variables[abs(l)].value = Value::t;  // assigns an arbitrary value to variables that were removed while another variables was eliminated
                }
            }
        }
        assert(clause_satisfied_check(cl));
        if (variables[var].value == Value::unset) {
            // If all the clauses the variable has been eliminated from were already satisfied, pick an arbitrary value.
            if (i == 0 || eliminated_clause_var_pair[i-1].second != var) {
                variables[var].value = Value::t;
            }
        }
    }

    // Verifies the satisfying assignment when debugging is enabled.
    for (const set<int>& clause: original_formula) {
        assert(clause_satisfied_check(clause));
    }

    cout << "s SATISFIABLE\n";
    cout << "v ";
    for (int i = 1; i < variables.size(); ++i) {
        cout << ((variables[i].value == Value::t) ? i : -i) << " ";
    }
    cout << "0\n";
    delete proof_file;
    return 0;
}