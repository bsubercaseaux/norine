/**
 * Program for dynamic symmetry breaking for Norines conjecture using Cadical as underlying solver.
 */

#include "cadical.hpp"
#include <vector>
#include <cstdlib>
#include <algorithm>

using namespace std;

// TODO check these two
#define flipBit(v, i) ((v) ^ (1 << (i))) // flips the i-th bit of v
#define getBit(v, i) (((v) >> (i)) & 1)  // get the i-th bit of v
#define setBit(v, i, value)     \
    {                           \
        if (value)              \
        {                       \
            (v) |= (1 << (i));  \
        }                       \
        else                    \
        {                       \
            (v) &= ~(1 << (i)); \
        }                       \
    }

typedef enum
{
    truth_value_true,
    truth_value_false,
    truth_value_unknown
} truth_value_t;

class NorinePropagator : public CaDiCaL::ExternalPropagator
{
private:
    int k; // dimensions of hypercube
    int frequency;
    bool all_models;

    int num_edges;
    int calls = 0;

    vector<vector<int>> trail;
    bool change_in_trail = true; // true if some variable has changed since last call of the check
    vector<vector<int>> clauses; // clauses which should be added to the solver

    // storing the current state of the coloring. First value gives the vertex and second the neighbor. The k-th neighbor is exactly different in the k-th bit
    vector<vector<truth_value_t>> matrix;

    vector<pair<int, int>> variable_to_edge; // for a given variable indicate to which edge it maps
    vector<vector<int>> edge_to_variable;    // the inverse

public:
    int num_solutions = 0;
    int num_learned_clauses = 0;

    NorinePropagator(int k, int frequency, bool all_models)
    {
        trail.push_back(vector<int>());
        this->k = k;
        this->frequency = frequency;
        this->all_models = all_models;

        int num_vertices = 1 << k; // 2**k
        this->num_edges = num_vertices * k / 2;

        this->matrix = vector<vector<truth_value_t>>(num_vertices, vector<truth_value_t>(k, truth_value_unknown));
        this->edge_to_variable = vector<vector<int>>(num_vertices, vector<int>(k, 0));

        this->variable_to_edge = vector<pair<int, int>>(num_edges + 1, {-1, -1});

        int var_count = 0;
        // TODO initialize the mappings. Must be the same as in the python script!!!
        for (int v = 0; v < num_vertices; v++)
        {
            for (int i = 0; i < k; i++)
            {
                // if i-th bit is 1 then skip because the neighbor is lex smaller
                if (getBit(v, i))
                    continue;

                var_count++;
                edge_to_variable[v][i] = var_count;
                // also initialize the other edge
                int u = flipBit(v, i);
                edge_to_variable[u][i] = var_count;

                variable_to_edge[var_count].first = v;
                variable_to_edge[var_count].second = i;
            }
        }
    }

    void notify_assignment(const std::vector<int> &lits)
    {
        for (int lit : lits)
        {
            printf("Assign lit: %d\n", lit);
            trail.back().push_back(lit);
            change_in_trail = true;

            // update matrix
            auto edge = variable_to_edge[abs(lit)];
            int v = edge.first;
            int i = edge.second;
            truth_value_t t = lit > 0 ? truth_value_true : truth_value_false;
            matrix[v][i] = t;
            // also set the other edge
            int u = flipBit(v, i); // TODO check whether correct
            matrix[u][i] = t;
        }
    };

    void notify_new_decision_level()
    {
        trail.push_back(vector<int>());
    };

    void notify_backtrack(size_t new_level)
    {
        while (trail.size() > new_level + 1)
        {
            auto last = trail.back();
            for (int lit : last)
            {
                auto edge = variable_to_edge[abs(lit)];
                int v = edge.first;
                int i = edge.second;
                matrix[v][i] = truth_value_unknown;
                // also set the other edge
                int u = flipBit(v, i); // TODO check whether correct
                matrix[u][i] = truth_value_unknown;
            }
            trail.pop_back();
        }
    };

    // print the red edges in python format. The vertices are tuples
    void print_coloring()
    {
        // print solution, i.e., all red edges
        bool first = true;
        printf("[");
        for (int v = 0; v < (1 << k); v++)
            for (int i = 0; i < k; i++)
            {
                if (getBit(v, i))
                    continue;

                if (matrix[v][i] == truth_value_true)
                {
                    if (!first)
                        printf(",");
                    first = false;

                    printf("(");

                    printf("(");
                    printf("%d", getBit(v, 0));
                    for (int j = 1; j < k; j++)
                        printf(",%d", getBit(v, j));
                    printf(")");

                    printf(",");

                    int u = flipBit(v, i);
                    printf("(");
                    printf("%d", getBit(u, 0));
                    for (int j = 1; j < k; j++)
                        printf(",%d", getBit(u, j));
                    printf(")");

                    printf(")");
                }
            }
        printf("]\n");
    }

    // block the current coloring (for enumeration)
    void block_coloring()
    {
        vector<int> clause;

        for (int v = 0; v < (1 << k); v++)
            for (int i = 0; i < k; i++)
            {
                if (getBit(v, i))
                    continue;

                truth_value_t t = matrix[v][i];
                int edgeOrig = edge_to_variable[v][i];

                if (t == truth_value_true)
                {
                    clause.push_back(-edgeOrig);
                }
                else if (t == truth_value_false)
                {
                    clause.push_back(edgeOrig);
                }
                else
                {
                    printf("Error line %d\n", __LINE__);
                    printf("Edge is undefined: %d %d\n", v, i);
                    exit(1);
                }
            }
        clauses.push_back(clause);
    }

    bool cb_check_found_model(const std::vector<int> &)
    {
        checkMinimality();
        if (!clauses.empty())
            return false;

        print_coloring();
        num_solutions++;
        if (all_models)
        {
            block_coloring();
            return false; // continue enumeration
        }

        return true;
    };

    bool cb_has_external_clause(bool &is_forgettable)
    {
        is_forgettable = false; // TODO maybe also try other version

        if (!clauses.empty())
            return true;

        if (calls > frequency)
        {
            calls = 0;
            change_in_trail = false;

            checkMinimality();
            return !clauses.empty();
        }
        return false;
    }

    int cb_add_external_clause_lit()
    {
        vector<int> &lastClause = clauses.back();
        if (lastClause.empty())
        {
            clauses.pop_back(); // delete last clause
            return 0;
        }
        else
        {
            int lit = lastClause.back();
            lastClause.pop_back();
            return lit;
        }
    };

    // checks minimality for the current partially defined hypercube coloring
    void checkMinimality()
    {
        // simple version going over all flips and permutations naively
        for (int v = 0; v < (1 << k); v++)
        {
            vector<int> dimensions;
            for (int i = 0; i < k; i++)
                dimensions.push_back(i);

            do
            {
                if (!testPermutation(v, dimensions))
                    return; // already found a suitable clause
            } while (next_permutation(dimensions.begin(), dimensions.end()));
        }
    }

    /**
     * @brief Test whether a certain symmetry leads to a smaller coloring of the hypercube
     *
     *
     * @param v The vertex which is mapped to (0,..,0). Gives the flips of the dimensions
     * @param permutationOfDimensions A permutation of the dimensions
     * @param negated Whether the coloring should additionally be swapped
     * @return false if it can already be concluded that it is not minimal, true otherwise
     */
    bool testPermutation(int v, const vector<int> &permutationOfDimensions, bool negated = false)
    {
        if (negated)
            exit(1); // not handled yet

        // printf("Permutation:");
        // for (auto i: permutationOfDimensions)
        //     printf(" %d", i);
        // printf("\n");

        vector<int> clause;

        // iterate over all edges in the lexicographic order and compare with permuted version
        for (int u = 0; u < (int)matrix.size(); u++)
        {
            for (int i = 0; i < k; i++)
            {
                int u2 = flipBit(u, i); // TODO check
                if (u2 <= u)            // only consider upper triangular part
                    continue;

                // flip bits where v is 1
                int flipped_u = u ^ v;
                // printf("Flipped u: %d\n", flipped_u);
                int perm_flip_u = 0;
                for (int j = 0; j < k; j++)
                {
                    setBit(perm_flip_u, j, getBit(flipped_u, permutationOfDimensions[j]));
                    // printf("Permflip_u after j=%d: %d\n", j, perm_flip_u);
                }

                // same for u2
                int perm_flip_u2 = flipBit(perm_flip_u, permutationOfDimensions[i]); // TODO check

                // swap perm_flip_u and perm_flip_u2 if necessary
                if (perm_flip_u > perm_flip_u2)
                    std::swap(perm_flip_u, perm_flip_u2);

                if (!negated)
                    if (u == perm_flip_u && u2 == perm_flip_u2)
                        continue; // same edge, skip

                // printf("v: %d\n", v);
                // printf("u: %d\n", u);
                // printf("%d %d %d %d\n",perm_flip_u, permutationOfDimensions[i], (int) matrix.size(), (int) matrix[0].size());

                truth_value_t valOriginal = matrix[u][i];
                truth_value_t valPermuted = matrix[perm_flip_u][permutationOfDimensions[i]];

                if (negated)
                {
                    if (valPermuted == truth_value_true)
                        valPermuted = truth_value_false;
                    else if (valPermuted == truth_value_false)
                        valPermuted = truth_value_true;
                }

                // cases where I can learn a clause
                if ((valOriginal == truth_value_true && valPermuted != truth_value_true) ||
                    (valOriginal != truth_value_false && valPermuted == truth_value_false))
                {
                    // TODO learn clause
                    int edgeOrig = edge_to_variable[u][i];

                    int edgePerm = edge_to_variable[perm_flip_u][permutationOfDimensions[i]]; // TODO check whether this correct
                    if (negated)
                        edgePerm = -edgePerm;

                    clause.push_back(-edgeOrig);
                    clause.push_back(edgePerm); // TODO check whether this correct

                    // Done
                    clauses.push_back(clause);
                    num_learned_clauses++;
                    return false;
                }

                if (valOriginal == truth_value_true)
                {
                    int edgeOrig = edge_to_variable[u][i];
                    clause.push_back(-edgeOrig);
                    continue;
                }

                if (valPermuted == truth_value_false)
                {
                    int edgePerm = edge_to_variable[perm_flip_u][permutationOfDimensions[i]]; // TODO check whether this correct
                    if (negated)
                        edgePerm = -edgePerm;

                    clause.push_back(edgePerm);
                    continue;
                }

                return true; // permutation doesn't lead to a smaller thing so we can stop here
            }
        }
        return true;
    }
};

int main(int argc, char **argv)
{
    CaDiCaL::Solver solver = CaDiCaL::Solver();

    if (argc < 4)
    {
        printf("Expected at least 3 argumens dimensions,frequency,all and evenutally path to encoding");
        exit(1);
    }

    int k = atoi(argv[1]);
    int f = atoi(argv[2]);
    int a = atoi(argv[3]);

    if (argc > 4)
    {
        int vars;
        solver.read_dimacs(argv[4], vars);
    }

    

    // add propagator
    NorinePropagator *p = new NorinePropagator(k, f, a > 0);
    solver.connect_external_propagator(p);

    // add observed variables
    int num_edges = (1 << k) * k / 2;
    for (int i = 1; i <= num_edges; i++)
    {
        solver.add_observed_var(i);
        // solver.add(i);
        // solver.add(0);
    }




    int res = solver.solve();
    printf("Result from solver: %d\n", res);
    printf("Number of solutions: %d\n", p->num_solutions);
    printf("Number of learned clauses: %d\n", p->num_learned_clauses);
    return 0;
}