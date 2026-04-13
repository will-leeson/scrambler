/* -*- C++ -*-
 *
 * A simple scrambler for SMT-LIB 2.6 scripts
 *
 * Copyright (C) 2021 Jochen Hoenicke
 * Copyright (C) 2018-2019 Aina Niemetz
 * Copyright (C) 2015-2018 Tjark Weber
 * Copyright (C) 2011 Alberto Griggio
 *
 * Copyright (C) 2011 Alberto Griggio
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include "scrambler.h"
#include <sstream>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <iostream>
#include <string.h>
#include <iomanip>
#include <fstream>
#include <algorithm>
#include <assert.h>
#include <ctype.h>
#include <stack>
#include <unordered_map>
#include <unordered_set>

////////////////////////////////////////////////////////////////////////////////

/*
 * pseudo-random number generator
 */
uint64_t seed;
const uint64_t a = 25214903917ULL;
const uint64_t c = 11U;
const uint64_t mask = ~(2ULL << 48);

void set_seed(int s)
{
    seed = s;
}

size_t next_rand_int(size_t upper_bound)
{
    seed = ((seed * a) + c) & mask;
    return (size_t)(seed >> 16U) % upper_bound;
}

////////////////////////////////////////////////////////////////////////////////

/* The different modes for term_annot:
 *  all:     keep all term annotations.
 *  pattern: keep pattern annotations, strip named annotations.
 *  none:    remove all term annotations.
 */
enum annotation_mode { none, pattern, all };


/*
 * If set to true, many of the scrambling transformations (e.g., shuffling of
 * assertions, permutation of names, etc.) will not be applied.
 */
bool no_scramble = false;

/*
 * If set to true, intra-assertion term transformations (commutative argument
 * shuffling and antisymmetric operator flipping) will not be applied.
 * Assertion reordering and variable renaming are unaffected.
 */
bool no_term_scramble = false;

/*
 * If set to false, assertion reordering will not be applied.
 * Variable renaming is unaffected.
 */
bool shuffle_asserts = true;

/*
 * If set to false, declaration reordering will not be applied.
 * Variable renaming is unaffected.
 */
bool shuffle_decls = true;

/*
 * If set to true, variables are renamed x1, x2, ... in order of first
 * appearance during printing (rather than by a random permutation of
 * parse-time IDs).
 */
bool sequential_names = false;

/*
 * If set to true, commands are reordered so that all declare-fun appear first,
 * followed by all define-fun (in their original relative order), then all
 * assert commands, then everything else. This makes assertions consecutive so
 * that -shuffle-asserts works correctly even for files with interleaved
 * declarations and assertions.
 */
bool normalize_structure = false;

/*
 * If *not* set to true, the following modifications will be made additionally:
 * 1. The command (set-option :print-success false) is prepended.
 */
bool gen_incremental = false;

/*
 * If set to true, the following modifications will be made additionally:
 * 1. The command (set-option :produce-unsat-cores true) will be prepended.
 * 2. A (get-unsat-core) command will be inserted after each (check-sat) command.
 * 3. Each (assert fmla) will be replaced by (assert (! fmla :named freshId))
 *    where freshId is some fresh identifier.
 */
bool gen_ucore = false;

/*
 * If set to true, the following modifications will be made additionally:
 * 1. The command (set-option :produce-models true) will be prepended.
 * 2. A (get-model) command will be inserted after each (check-sat) command.
 */
bool gen_mval = false;

/*
 * If set to true, the following modifications will be made additionally:
 * 1. The command (set-option :produce-proofs true) will be prepended.
 * 2. A (get-proof) command will be inserted after each (check-sat) command.
 */
bool gen_proof = false;

/*
 * If set to true, support SMTLIB files that have features not supported by
 * SMTCOMP
 */
bool support_non_smtcomp = false;

/*
 * If set to true, support SMTLIB files that have Z3-specific features
 */
bool support_z3 = false;

/*
 * If set to true, the system prints the number of assertions to stdout
 */
bool count_asrts = false;

/*
 * If non-empty, write a mapping of original assertion index to scrambled
 * assertion index (0-based, asserts only) to this file.
 */
std::string assert_map_file;

// accumulated mapping: (orig_idx, new_idx)
std::vector<std::pair<size_t, size_t>> assert_map;

////////////////////////////////////////////////////////////////////////////////

/*
 * Scrambling of symbols (i.e., names) declared in the benchmark. For
 * details see "Scrambling and Descrambling SMT-LIB Benchmarks" (Tjark
 * Weber; in Tim King and Ruzica Piskac, editors, Proceedings of the
 * 14th International Workshop on Satisfiability Modulo Theories,
 * Coimbra, Portugal, July 1-2, 2016, volume 1617 of CEUR Workshop
 * Proceedings, pages 31-40, July 2016).
 *
 * There are three kinds of names: (1) names declared in the input
 * benchmark (e.g., sort symbols, function symbols, bound variables);
 * (2) name identifiers used during parsing; and (3) uniform names
 * (i.e., x1, x2, ...) used when the scrambled benchmark is printed.
 *
 * Benchmark-declared names are read during parsing and stored in the
 * nodes of the parse tree; specifically, in their symbol field (which
 * is otherwise also used to store SMT-LIB commands, keywords, etc.).
 *
 * In addition, a bijection between benchmark-declared names and name
 * identifiers is built during parsing, and extended whenever a
 * declaration or binder (of a new name) is encountered. Note that
 * name identifiers are not necessarily unique, i.e., they do not
 * resolve shadowing.
 *
 * Finally, when the scrambled benchmark is printed, name identifiers
 * are permuted randomly before they are turned into uniform names.
 */

typedef std::unordered_map<std::string, uint64_t> Name_ID_Map;

// a map from benchmark-declared symbols to name identifiers
Name_ID_Map name_ids;

// |foo| and foo denote the same symbol in SMT-LIB, hence the need to
// remove |...| quotes before symbol lookups
const char *unquote(const char *n)
{
    if (!n[0] || n[0] != '|') {
        return n;
    }

    static std::string buf;
    buf = n;
    assert(!buf.empty());
    if (buf.size() > 1 && buf[0] == '|' && buf[buf.size()-1] == '|') {
        buf = buf.substr(1, buf.size()-2);
    }
    return buf.c_str();
}

// the next available name id
uint64_t next_name_id = 1;

namespace scrambler {

// declaring a new name
void set_new_name(const char *n)
{
    n = unquote(n);

    if (name_ids.find(n) == name_ids.end()) {
        name_ids[n] = next_name_id;
        ++next_name_id;
    }
}

} // namespace

uint64_t get_name_id(const char *n)
{
    n = unquote(n);

    return name_ids[n];  // 0 if n is not currently in name_ids
}

////////////////////////////////////////////////////////////////////////////////

namespace scrambler {

void node::add_children(const std::vector<node *> *c)
{
    children.insert(children.end(), c->begin(), c->end());
}

} // namespace

////////////////////////////////////////////////////////////////////////////////

/*
 * The main data structure: here the benchmark's commands are added as
 * they are parsed (and removed when they have been printed).
 */
std::vector<scrambler::node *> commands;

namespace scrambler {

void add_node(const char *s, node *n1, node *n2, node *n3, node *n4)
{
    assert(s); // s must be a top-level SMT-LIB command

    node *ret = new node;
    ret->symbol = s;
    ret->is_name = false;
    ret->needs_parens = true;

    if (n1) {
        ret->children.push_back(n1);
    }
    if (n2) {
        ret->children.push_back(n2);
    }
    if (n3) {
        ret->children.push_back(n3);
    }
    if (n4) {
        ret->children.push_back(n4);
    }

    commands.push_back(ret);
}

node *make_node(const char *s, node *n1, node *n2)
{
    node *ret = new node;
    ret->needs_parens = true;
    if (s) {
        ret->symbol = s;
    }
    ret->is_name = false;
    if (n1) {
        ret->children.push_back(n1);
    }
    if (n2) {
        ret->children.push_back(n2);
    }
    if (!ret->symbol.empty() && ret->children.empty()) {
        ret->needs_parens = false;
    }
    return ret;
}

node *make_node(const std::vector<node *> *v)
{
    node *ret = new node;
    ret->needs_parens = true;
    ret->symbol = "";
    ret->is_name = false;
    ret->children.assign(v->begin(), v->end());
    return ret;
}

node *make_node(node *n, const std::vector<node *> *v)
{
    node *ret = new node;
    ret->needs_parens = true;
    ret->symbol = "";
    ret->is_name = false;
    ret->children.push_back(n);
    ret->children.insert(ret->children.end(), v->begin(), v->end());
    return ret;
}

node *make_name_node(const char* s, node *n1)
{
    node *ret = new node;
    assert(s);
    ret->symbol = s;
    ret->is_name = true;
    ret->needs_parens = false;
    if (n1) {
        ret->children.push_back(n1);
        ret->needs_parens = true;
    }
    return ret;
}

void del_node(node *n)
{
    for (size_t i = 0; i < n->children.size(); ++i) {
        del_node(n->children[i]);
    }
    delete n;
}

} // scrambler

////////////////////////////////////////////////////////////////////////////////

namespace scrambler {

void shuffle_list(std::vector<scrambler::node *> *v, size_t start, size_t end)
{
    if (!no_scramble) {
        size_t n = end - start;
        for (size_t i = n-1; i > 0; --i) {
            std::swap((*v)[i+start], (*v)[next_rand_int(i+1)+start]);
        }
    }
}

void shuffle_list(std::vector<node *> *v)
{
    shuffle_list(v, 0, v->size());
}

} // scrambler

////////////////////////////////////////////////////////////////////////////////

/*
 * functions that set or depend on the benchmark's logic
 */

std::string logic;

namespace scrambler {

void set_logic(const std::string &l)
{
    // each benchmark contains a single set-logic command
    if (!logic.empty()) {
        std::cerr << "ERROR logic is already set" << std::endl;
        exit(1);
    }

    logic = l;
}

} // scrambler

bool logic_is_dl()  // Difference Logic: IDL, RDL
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("IDL") != std::string::npos || logic.find("RDL") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return (result == 1);
}

bool logic_is_arith()  // Arithmetic: IA, RA, IRA
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("IA") != std::string::npos || logic.find("RA") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return (result == 1);
}

bool logic_is_bv()  // BitVectors (BV)
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("BV") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return result == 1;
}

bool logic_is_fp()  // FloatingPoint (FP)
{
    static int result = -1;
    if (result == -1) {
        if (logic.empty()) {
            std::cerr << "ERROR logic has not been set" << std::endl;
            exit(1);
        }

        if (logic.find("FP") != std::string::npos) {
            result = 1;
        } else {
            result = 0;
        }
    }

    return result == 1;
}

namespace scrambler {

// Return vector index >= 0 (from where the list of children is commutative)
// if true, else -1.
int is_commutative(const node *n)
{
    if (no_term_scramble) return -1;
    // *n might be a qualified identifier of the form ('as' identifier sort)
    const std::string *symbol = &(n->symbol);
    if (*symbol == "as") {
        assert(n->children.size() > 0);
        symbol = &(n->children[0]->symbol);
    }
    const std::string &s = *symbol;
    assert(!s.empty());

    // Core theory
    if (s == "and" || s == "or" || s == "xor" || s == "distinct") {
        return 0;
    }
    if (!logic_is_dl()) {
        if (s == "=") {
            return 0;
        }
    }

    // arithmetic (IA, RA, IRA) (but not difference logic)
    if (logic_is_arith()) {
        if (s == "*" || s == "+") {
            return 0;
        }
    }

    // BitVectors
    if (logic_is_bv()) {
        if (s == "bvand" || s == "bvor" || s == "bvxor" ||
            s == "bvnand" || s == "bvnor" || s == "bvcomp" ||
            s == "bvadd" || s == "bvmul") {
            return 0;
        }
    }

    // FloatingPoint
    if (logic_is_fp()) {
        if (s == "fp.eq") {
            return 0;
        }
        if (s == "fp.add" || s == "fp.mul") {
            return 1;
        }
    }

    return -1;
}

bool flip_antisymm(const node *n, node ** const out_n)
{
    if (no_scramble || no_term_scramble) {
        return false;
    }

    if (!next_rand_int(2)) {
        return false;
    }

    // *n might be a qualified identifier of the form ('as' identifier sort)
    const std::string *symbol = &(n->symbol);
    if (*symbol == "as") {
        assert(n->children.size() > 0);
        symbol = &(n->children[0]->symbol);
    }
    const std::string &s = *symbol;
    assert(!s.empty());

    // arithmetic (IA, RA, IRA) (but not difference logic)
    if (logic_is_arith()) {
        if (s == "<") {
            *out_n = make_node(">");
            return true;
        } else if (s == ">") {
            *out_n = make_node("<");
            return true;
        } else if (s == "<=") {
            *out_n = make_node(">=");
            return true;
        } else if (s == ">=") {
            *out_n = make_node("<=");
            return true;
        }
    }

    // BitVectors
    if (logic_is_bv()) {
        if (s == "bvslt") {
            *out_n = make_node("bvsgt");
            return true;
        } else if (s == "bvsle") {
            *out_n = make_node("bvsge");
            return true;
        } else if (s == "bvult") {
            *out_n = make_node("bvugt");
            return true;
        } else if (s == "bvule") {
            *out_n = make_node("bvuge");
            return true;
        } else if (s == "bvsgt") {
            *out_n = make_node("bvslt");
            return true;
        } else if (s == "bvsge") {
            *out_n = make_node("bvsle");
            return true;
        } else if (s == "bvugt") {
            *out_n = make_node("bvult");
            return true;
        } else if (s == "bvuge") {
            *out_n = make_node("bvule");
            return true;
        }
    }

    // FloatingPoint
    if (logic_is_fp()) {
        if (s == "fp.leq") {
            *out_n = make_node("fp.geq");
            return true;
        } else if (s == "fp.lt") {
            *out_n = make_node("fp.gt");
            return true;
        } else if (s == "fp.geq") {
            *out_n = make_node("fp.leq");
            return true;
        } else if (s == "fp.gt") {
            *out_n = make_node("fp.lt");
            return true;
        }
    }

    return false;
}

} // scrambler

////////////////////////////////////////////////////////////////////////////////

/*
 * (scrambled) printing of benchmarks
 */

// a random permutation of name ids
std::vector<uint64_t> permuted_name_ids;

// when sequential_names is true, maps parse-time name id -> output name id
// assigned in order of first appearance during printing
std::unordered_map<uint64_t, uint64_t> output_name_ids;
uint64_t next_output_name_id = 1;

// uniform names
std::string make_name(uint64_t name_id)
{
    std::ostringstream tmp;
    tmp << "x" << name_id;
    return tmp.str();
}

// annotated assertions (for -gen-unsat-core true)
std::string make_annotation_name()
{
    static uint64_t n = 1;
    std::ostringstream tmp;
    tmp << "smtcomp" << n;
    ++n;
    return tmp.str();
}

static bool keep_annotation(const scrambler::node *n, annotation_mode keep_annotations) {
    if (keep_annotations == none)
        return false;
    if (keep_annotations == all)
        return true;
    assert(keep_annotations == pattern);
    return n->children.size() == 2 && n->children[1]->symbol == ":pattern";
}

// Recursively assign sequential output name IDs to all names in a node tree,
// in order of first appearance, without printing anything.
void assign_names(const scrambler::node *n)
{
    if (n->is_name) {
        uint64_t name_id = get_name_id(n->symbol.c_str());
        if (name_id != 0 && output_name_ids.find(name_id) == output_name_ids.end()) {
            output_name_ids[name_id] = next_output_name_id++;
        }
    }
    for (size_t i = 0; i < n->children.size(); ++i) {
        assign_names(n->children[i]);
    }
}

void print_node(std::ostream &out, const scrambler::node *n, annotation_mode keep_annotations)
{
    if (n->symbol == "!" && !keep_annotation(n, keep_annotations)) {
        print_node(out, n->children[0], keep_annotations);
    } else {
        if (n->needs_parens) {
            out << '(';
        }
        if (!n->symbol.empty()) {
            if (no_scramble || !n->is_name) {
                out << n->symbol;
            } else if (sequential_names) {
                uint64_t name_id = get_name_id(n->symbol.c_str());
                if (name_id == 0) {
                    out << n->symbol;
                } else {
                    auto it = output_name_ids.find(name_id);
                    if (it == output_name_ids.end()) {
                        output_name_ids[name_id] = next_output_name_id++;
                        it = output_name_ids.find(name_id);
                    }
                    out << make_name(it->second);
                }
            } else {
                uint64_t name_id = get_name_id(n->symbol.c_str());
                if (name_id == 0) {
                    out << n->symbol;
                } else {
                    assert(name_id < permuted_name_ids.size());
                    out << make_name(permuted_name_ids[name_id]);
                }
            }
        }
        std::string name;
        if (gen_ucore && n->symbol == "assert") {
            name = make_annotation_name();
        }
        if (!name.empty()) {
            out << " (!";
        }
        for (size_t i = 0; i < n->children.size(); ++i) {
            if (i > 0 || !n->symbol.empty()) {
                out << ' ';
            }
            print_node(out, n->children[i], keep_annotations);
        }
        if (!name.empty()) {
            out << " :named " << name << ")";
        }
        if (n->needs_parens) {
            out << ')';
        }
        if (n->symbol == "check-sat") {
            if (gen_ucore) {
                // insert (get-unsat-core) after each check-sat
                out << std::endl << "(get-unsat-core)";
            }
            if (gen_mval) {
                // insert (get-model) after each check-sat
                out << std::endl << "(get-model)";
            }
            if (gen_proof) {
                // insert (get-proof) after each check-sat
                out << std::endl << "(get-proof)";
            }
        }
    }
}

void print_command(std::ostream &out, const scrambler::node *n, annotation_mode keep_annotations)
{
    print_node(out, n, keep_annotations);
    out << std::endl;
}

void print_scrambled(std::ostream &out, annotation_mode keep_annotations)
{
    // capture original assert order before any shuffling
    std::vector<scrambler::node *> orig_assert_order;
    if (!assert_map_file.empty()) {
        for (size_t i = 0; i < commands.size(); ++i) {
            if (commands[i]->symbol == "assert") {
                orig_assert_order.push_back(commands[i]);
            }
        }
    }

    // pre-assign output name IDs in declaration order before any shuffling,
    // so the mapping is stable regardless of assertion/declaration shuffle order
    if (sequential_names) {
        for (size_t i = 0; i < commands.size(); ++i) {
            assign_names(commands[i]);
        }
    }

    if (normalize_structure) {
        // Reorder commands: preamble (set-logic, set-option, etc.) first,
        // then declare-fun, then define-fun (relative order preserved),
        // then assert, then everything else (check-sat, exit, etc.).
        std::vector<scrambler::node *> preamble, decls, defs, asserts, rest;
        for (size_t i = 0; i < commands.size(); ++i) {
            const std::string &sym = commands[i]->symbol;
            if (sym == "set-logic" || sym == "set-option" || sym == "set-info") {
                preamble.push_back(commands[i]);
            } else if (sym == "declare-fun" || sym == "declare-const" || sym == "declare-sort") {
                decls.push_back(commands[i]);
            } else if (sym == "define-fun" || sym == "define-sort") {
                defs.push_back(commands[i]);
            } else if (sym == "assert") {
                asserts.push_back(commands[i]);
            } else {
                rest.push_back(commands[i]);
            }
        }
        commands.clear();
        commands.insert(commands.end(), preamble.begin(), preamble.end());
        commands.insert(commands.end(), decls.begin(), decls.end());
        commands.insert(commands.end(), defs.begin(), defs.end());
        commands.insert(commands.end(), asserts.begin(), asserts.end());
        commands.insert(commands.end(), rest.begin(), rest.end());
    }

    if (!no_scramble) {
        if (shuffle_decls) {
            // identify consecutive declarations and shuffle them
            for (size_t i = 0; i < commands.size(); ) {
                if (commands[i]->symbol == "declare-fun") {
                    size_t j = i+1;
                    while (j < commands.size() &&
                           commands[j]->symbol == "declare-fun") {
                        ++j;
                    }
                    if (j - i > 1) {
                        shuffle_list(&commands, i, j);
                    }
                    i = j;
                } else {
                    ++i;
                }
            }
        }

        if (shuffle_asserts) {
            // identify consecutive assertions and shuffle them
            for (size_t i = 0; i < commands.size(); ) {
                if (commands[i]->symbol == "assert") {
                    size_t j = i+1;
                    while (j < commands.size() &&
                           commands[j]->symbol == "assert"){
                        ++j;
                    }
                    if (j - i > 1) {
                        shuffle_list(&commands, i, j);
                    }
                    i = j;
                } else {
                    ++i;
                }
            }
        }

        if (!sequential_names) {
            // Generate a random permutation of name ids. Note that index
            // 0 is unused in the permuted_name_ids vector (but present to
            // simplify indexing), and index next_name_id is out of range.
            size_t old_size = permuted_name_ids.size();
            assert(old_size <= next_name_id);
            // Since the print_scrambled function may be called multiple
            // times (for different parts of the benchmark), we only need
            // to permute those name ids that have been declared since the
            // last call to print_scrambled.
            if (old_size < next_name_id) {
                permuted_name_ids.reserve(next_name_id);
                for (size_t i = old_size; i < next_name_id; ++i) {
                    permuted_name_ids.push_back(i);
                    assert(permuted_name_ids[i] == i);
                }
                assert(permuted_name_ids.size() == next_name_id);
                // index 0 must not be shuffled
                if (old_size == 0) {
                    old_size = 1;
                }
                // Knuth shuffle
                for (size_t i = old_size; i < next_name_id - 1; ++i) {
                    size_t j = i + next_rand_int(next_name_id - i);
                    std::swap(permuted_name_ids[i], permuted_name_ids[j]);
                }
            }
        }
    }

    // compute assert mapping (orig index -> new index) after all shuffles
    if (!assert_map_file.empty() && !orig_assert_order.empty()) {
        std::unordered_map<scrambler::node *, size_t> orig_index;
        for (size_t i = 0; i < orig_assert_order.size(); ++i) {
            orig_index[orig_assert_order[i]] = i;
        }
        size_t new_idx = 0;
        for (size_t i = 0; i < commands.size(); ++i) {
            if (commands[i]->symbol == "assert") {
                assert_map.push_back({orig_index[commands[i]], new_idx});
                ++new_idx;
            }
        }
    }

    // print all commands
    for (size_t i = 0; i < commands.size(); ++i) {
        print_command(out, commands[i], keep_annotations);
        del_node(commands[i]);
    }
    commands.clear();
}

////////////////////////////////////////////////////////////////////////////////

/*
 * -core
 */

typedef std::unordered_set<std::string> StringSet;

bool parse_core(std::istream &src, StringSet &out)
{
    std::string name;
    src >> name;
    if (!src || name != "unsat") {
        return false;
    }
    // skip chars until a '(' is found
    char c;
    while (src.get(c) && c != '(') {
        if (!isspace(c)) {
            return false;
        }
    }
    if (!src) {
        return false;
    }
    bool done = false;
    while (src && !done) {
        src >> name;
        if (name.empty()) {
            return false;
        }
        if (name[name.size()-1] == ')') {
            name = name.substr(0, name.size()-1);
            done = true;
        }
        if (!name.empty()) {
            out.insert(name);
        }
    }

    std::vector<std::string> outnames(out.begin(), out.end());
    std::sort(outnames.begin(), outnames.end());

    std::cout << ";; parsed " << outnames.size() << " names:";
    for (size_t i = 0; i < outnames.size(); ++i) {
        std::cout << " " << outnames[i];
    }
    std::cout << std::endl;

    return true;
}

std::string get_named_annot(scrambler::node *root)
{
    std::vector<scrambler::node *> to_process;
    std::unordered_set<scrambler::node *> seen;

    to_process.push_back(root);
    while (!to_process.empty()) {
        scrambler::node *cur = to_process.back();
        to_process.pop_back();

        if (!seen.insert(cur).second) {
            continue;
        }
        if (cur->symbol == "!") {
            if (cur->children.size() >= 1) {
                to_process.push_back(cur->children[0]);
            }
            if (cur->children.size() >= 2) {
                for (size_t j = 1; j < cur->children.size(); ++j) {
                    scrambler::node *attr = cur->children[j];
                    if (attr->symbol == ":named" &&
                        !attr->children.empty()) {
                        return attr->children[0]->symbol;
                    }
                }
            }
        } else {
            for (size_t j = 0; j < cur->children.size(); ++j) {
                to_process.push_back(cur->children[j]);
            }
        }
    }

    return "";
}

// Used by the post-processor in the unsat core track to filter the
// assertions and only keep those that appear in the unsat core.
// The string set `to_keep` lists all names that should be kept.
void filter_named(const StringSet &to_keep)
{
    size_t i, k;
    for (i = k = 0; i < commands.size(); ++i) {
        scrambler::node *cur = commands[i];
        bool keep = true;
        if (cur->symbol == "assert") {
            std::string name = get_named_annot(cur);
            if (!name.empty() && to_keep.find(name) == to_keep.end()) {
                keep = false;
            }
        }
        if (keep) {
            commands[k++] = cur;
        }
    }
    commands.resize(k);
}

////////////////////////////////////////////////////////////////////////////////

char *c_strdup(const char *s)
{
    char *ret = (char *)malloc(strlen(s) + 1);
    if (ret == NULL) {
        exit(1);
    }

    strcpy(ret, s);
    return ret;
}

////////////////////////////////////////////////////////////////////////////////

void usage(const char *program)
{
    std::cout << "Syntax: " << program << " [OPTIONS] < INPUT_FILE.smt2\n"
              << "\n"
              << "    -term_annot [true|pattern|false]\n"
              << "        controls whether term annotations are printed "
                 "(default: true)\n"
              << "\n"
              << "    -seed N\n"
              << "        seed value (>= 0) for pseudo-random choices; if 0, "
                 "no scrambling is\n"
              << "        performed (default: time(0))\n"
              << "\n"
              << "    -core FILE\n"
              << "        print only those (named) assertions whose name is "
                 "contained in the\n"
              << "        specified FILE (default: print all assertions)\n"
              << "\n"
              << "    -incremental [true|false]\n"
              << "        produce output in a format suitable for the trace "
                 "executer used in\n"
              << "        the incremental track of SMT-COMP (default: false)\n"
              << "\n"
              << "    -gen-unsat-core [true|false]\n"
              << "        controls whether the output is in a format suitable "
                 "for the unsat-core\n"
              << "        track of SMT-COMP (default: false)\n"
              << "\n"
              << "    -gen-model-val [true|false]\n"
              << "        controls whether the output is in a format suitable "
                 "for the model\n"
              << "        validation track of SMT-COMP (default: false)\n"
              << "\n"
              << "    -gen-proof [true|false]\n"
              << "        controls whether the output is in a format suitable "
                 "for the proof\n"
              << "        track of SMT-COMP (default: false)\n"
              << "\n"
              << "    -support-non-smtcomp [true|false]\n"
              << "        controls whether to support SMTLIB commands that are "
                 "not supported\n"
              << "        by SMTCOMP (default: false)\n"
              << "\n"
              << "    -support-z3 [true|false]\n"
              << "        controls whether to support non-SMTLIB commands that "
                 "are supported\n"
              << "        by Z3 (default: false)\n"
              << "\n"
              << "    -count-asserts [true|false]\n"
              << "        controls whether the number of assertions found in the benchmark\n"
              << "        is printed to stderr (default: false)\n"
              << "\n"
              << "    -sequential-names [true|false]\n"
              << "        if true, variables are renamed x1, x2, ... in order of\n"
              << "        first appearance during printing, rather than by a random\n"
              << "        permutation (default: false)\n"
              << "\n"
              << "    -normalize-structure [true|false]\n"
              << "        if true, reorder commands so declare-fun comes first,\n"
              << "        then define-fun, then assert, then check-sat etc.\n"
              << "        Makes assertions consecutive for reliable shuffling\n"
              << "        in files with interleaved declarations (default: false)\n"
              << "\n"
              << "    -shuffle-asserts [true|false]\n"
              << "        controls whether assertions are reordered;\n"
              << "        variable renaming is unaffected (default: true)\n"
              << "\n"
              << "    -shuffle-decls [true|false]\n"
              << "        controls whether declarations are reordered;\n"
              << "        variable renaming is unaffected (default: true)\n"
              << "\n"
              << "    -term-scramble [true|false]\n"
              << "        controls whether intra-assertion term transformations\n"
              << "        (commutative argument shuffling, operator flipping) are\n"
              << "        applied; assertion reordering and renaming are unaffected\n"
              << "        (default: true)\n"
              << "\n"
              << "    -assert-map-file FILE\n"
              << "        write a mapping of original assertion index to scrambled\n"
              << "        assertion index (0-based, one entry per line: orig -> new)\n"
              << "        to the specified FILE\n\n";
    std::cout.flush();
    exit(1);
}

////////////////////////////////////////////////////////////////////////////////

extern int yyparse();

using namespace scrambler;

int main(int argc, char **argv)
{
    annotation_mode keep_annotations = all;

    bool create_core = false;
    std::string core_file;

    set_seed(time(0));

    for (int i = 1; i < argc; ) {
        if (strcmp(argv[i], "-seed") == 0 && i+1 < argc) {
            std::istringstream s(argv[i+1]);
            int x;
            if (s >> x && x >= 0) {
                if (x > 0) {
                    set_seed(x);
                } else {
                    no_scramble = true;
                }
            } else {
                std::cerr << "Invalid value for -seed: " << argv[i+1] << std::endl;
                return 1;
            }
            i += 2;
        } else if (strcmp(argv[i], "-term_annot") == 0 && i+1 < argc) {
            if (strcmp(argv[i+1], "true") == 0) {
                keep_annotations = all;
            } else if (strcmp(argv[i+1], "pattern") == 0) {
                keep_annotations = pattern;
            } else if (strcmp(argv[i+1], "false") == 0) {
                keep_annotations = none;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-core") == 0 && i+1 < argc) {
            create_core = true;
            core_file = argv[i+1];
            i += 2;
        } else if (strcmp(argv[i], "-incremental") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                gen_incremental = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                gen_incremental = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-gen-unsat-core") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                gen_ucore = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                gen_ucore = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-gen-model-val") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                gen_mval = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                gen_mval = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-gen-proof") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                gen_proof = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                gen_proof = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-support-non-smtcomp") == 0 &&
                   i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                support_non_smtcomp = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                support_non_smtcomp = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-support-z3") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                support_z3 = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                support_z3 = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-count-asserts") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                count_asrts = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                count_asrts = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-sequential-names") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                sequential_names = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                sequential_names = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-normalize-structure") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                normalize_structure = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                normalize_structure = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-shuffle-asserts") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                shuffle_asserts = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                shuffle_asserts = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-shuffle-decls") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                shuffle_decls = true;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                shuffle_decls = false;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-term-scramble") == 0 && i + 1 < argc) {
            if (strcmp(argv[i + 1], "true") == 0) {
                no_term_scramble = false;
            } else if (strcmp(argv[i + 1], "false") == 0) {
                no_term_scramble = true;
            } else {
                usage(argv[0]);
            }
            i += 2;
        } else if (strcmp(argv[i], "-assert-map-file") == 0 && i + 1 < argc) {
            assert_map_file = argv[i + 1];
            i += 2;
        } else {
            usage(argv[0]);
        }
    }

    StringSet core_names;
    if (create_core) {
        std::ifstream src(core_file.c_str());
        if (!parse_core(src, core_names)) {
            std::cerr << "ERROR parsing core names from " << core_file << std::endl;
            return 1;
        }
    }

    if (!gen_incremental && !count_asrts) {
        // prepend SMT-LIB command that suppresses success for non-incremental
        // tracks
        std::cout << "(set-option :print-success false)" << std::endl;
    }

    if (gen_ucore) {
        // prepend SMT-LIB command that enables production of unsat cores
        std::cout << "(set-option :produce-unsat-cores true)" << std::endl;
    }

    if (gen_mval) {
        // prepend SMT-LIB command that enables production of models
        std::cout << "(set-option :produce-models true)" << std::endl;
    }

    if (gen_proof) {
        // prepend SMT-LIB command that enables production of models
        std::cout << "(set-option :produce-proofs true)" << std::endl;
    }

    if (count_asrts) {
        while (!std::cin.eof()) {
            yyparse();
        }
        int asrt_count = 0;
        for (std::vector<scrambler::node*>::iterator it = commands.begin(); it != commands.end(); ++it) {
            if ((*it)->symbol == "assert") {
                asrt_count++;
            }
        }
        std::cerr << "; Number of assertions: " << asrt_count << "\n";
        exit(0);
    }

    while (!std::cin.eof()) {
        yyparse();
        if (!commands.empty() && commands.back()->symbol == "check-sat") {
            if (create_core) {
                filter_named(core_names);
            }
            assert(!commands.empty());
            print_scrambled(std::cout, keep_annotations);
        }
    }

    if (create_core) {
        filter_named(core_names);
    }
    if (!commands.empty()) {
        print_scrambled(std::cout, keep_annotations);
    }

    if (!assert_map_file.empty() && !assert_map.empty()) {
        std::ofstream map_out(assert_map_file.c_str());
        if (!map_out) {
            std::cerr << "ERROR: could not open assert map file: "
                      << assert_map_file << std::endl;
            return 1;
        }
        for (size_t i = 0; i < assert_map.size(); ++i) {
            map_out << assert_map[i].first << " -> " << assert_map[i].second
                    << "\n";
        }
    }

    return 0;
}
