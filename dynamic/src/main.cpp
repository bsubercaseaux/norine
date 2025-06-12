/**
 * Program for dynamic symmetry breaking for Norines conjecture using Cadical as underlying solver.
 */

#include "cadical.hpp"
#include <vector>
#include <cstdlib>
#include <algorithm>
#include <string>

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
    clock_t time_in_minimality = 0;
    clock_t time_in_propagator = 0;
    int calls_check = 0;

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
        clock_t start = clock();
        for (int lit : lits)
        {
            // printf("Assign lit: %d\n", lit);
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
        time_in_propagator += clock() - start;
    };

    void notify_new_decision_level()
    {
        trail.push_back(vector<int>());
    };

    void notify_backtrack(size_t new_level)
    {
        clock_t start = clock();
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

        time_in_propagator += clock() - start;
    };

    string vertex_to_string(int v)
    {
        string s = "(";
        for (int i = 0; i < k; i++)
        {
            if (i > 0)
                s += ",";
            s += to_string(getBit(v, i));
        }
        s += ")";
        return s;
    }

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

                    int u = flipBit(v, i);
                    printf("(%s,%s)", vertex_to_string(v).c_str(), vertex_to_string(u).c_str());
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
        clock_t start = clock();
        checkMinimality();
        time_in_minimality += clock() - start;

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
        calls++;
        is_forgettable = false; // TODO maybe also try other version

        if (!clauses.empty())
            return true;

        if (calls > frequency)
        {
            calls = 0;
            change_in_trail = false;

            clock_t start = clock();
            checkMinimality();
            time_in_minimality += clock() - start;

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
        calls_check++;
        int version = 1;

        if (version == 0)
        {

            // printf("Start minimality check\n");
            // simple version going over all flips and permutations naively
            for (int v = 0; v < (1 << k); v++)
            {
                vector<int> dimensions;
                for (int i = 0; i < k; i++)
                    dimensions.push_back(i);

                do
                {
                    // printf("Testing permutation: ");
                    // for (int i : dimensions)
                    //     printf(" %d", i);
                    // printf("\n");
                    if (!testPermutation(v, dimensions))
                        return; // already found a suitable clause
                } while (next_permutation(dimensions.begin(), dimensions.end()));
            }
        }

        // second version using the degrees
        if (version == 1)
        {
            // check if first vertex is fully defined and get degree
            int degree = 0;
            for (int i = 0; i < k; i++)
            {
                if (matrix[0][i] == truth_value_unknown)
                    return; // not fully defined
                if (matrix[0][i] == truth_value_true)
                    degree++;
            }

            int numVertices = 1 << k;
            // guess for vertex
            for (int v = 0; v < numVertices; v++)
            {
                // check if vertex is fully defined
                bool isFullyDefined = true;

                vector<int> neighbors;
                vector<int> non_neighbors;

                for (int i = 0; i < k; i++)
                {
                    if (matrix[v][i] == truth_value_unknown)
                    {
                        isFullyDefined = false;
                        break; // not fully defined
                    }
                    else if (matrix[v][i] == truth_value_true)
                        neighbors.push_back(i);
                    else
                        non_neighbors.push_back(i);
                }

                if (!isFullyDefined)
                    continue; // not fully defined

                int degree_v = (int)neighbors.size();         // degree of the vertex
                int antidegree_v = (int)non_neighbors.size(); // antidegree of the vertex

                if (degree_v < degree)
                {
                    vector<int> permutationOfDimensions;

                    for (int i = 0; i < (int)non_neighbors.size(); i++)
                        permutationOfDimensions.push_back(non_neighbors[i]);
                    // insert neighbors
                    for (int i = 0; i < (int)neighbors.size(); i++)
                        permutationOfDimensions.push_back(neighbors[i]);

                    if (testPermutation(v, permutationOfDimensions))
                    {
                        printf("---------------------------------------------\n");
                        printf("Error: should fail\n");
                        printf("Current coloring:");
                        print_coloring();
                        printf("Degree first vertex: %d\n", degree);
                        printf("Degree current vertex: %d\n", degree_v);
                        printf("First vertex: %s\n", vertex_to_string(0).c_str());
                        printf("Current vertex: %s\n", vertex_to_string(v).c_str());

                        printf("Non neighbors:");
                        for (auto i : non_neighbors)
                            printf(" %d", i);
                        printf("\n");

                        printf("Neighbors:");
                        for (auto i : neighbors)
                            printf(" %d", i);
                        printf("\n");

                        printf("---------------------------------------------\n");
                        exit(1);
                    }
                    return;
                }

                if (degree_v <= degree)
                {
                    // consider all permutations of the neighbors and non neighbors
                    do
                    {
                        do
                        {
                            vector<int> permutationOfDimensions;
                            // insert non_neighbors first
                            for (int i = 0; i < (int)non_neighbors.size(); i++)
                                permutationOfDimensions.push_back(non_neighbors[i]);
                            // insert neighbors
                            for (int i = 0; i < (int)neighbors.size(); i++)
                                permutationOfDimensions.push_back(neighbors[i]);

                            if (!testPermutation(v, permutationOfDimensions))
                                return;

                        } while (std::next_permutation(non_neighbors.begin(), non_neighbors.end()));
                    } while (std::next_permutation(neighbors.begin(), neighbors.end()));

                    // TODO improvement; also kinda sort non_neighbors by their degree
                }

                if ((antidegree_v < degree))
                {
                    vector<int> permutationOfDimensions;

                    // insert neighbors first
                    for (int i = 0; i < (int)neighbors.size(); i++)
                        permutationOfDimensions.push_back(neighbors[i]);
                    for (int i = 0; i < (int)non_neighbors.size(); i++)
                        permutationOfDimensions.push_back(non_neighbors[i]);

                    if (testPermutation(v, permutationOfDimensions, true))
                    {
                        printf("---------------------------------------------\n");
                        printf("Error: should fail\n");
                        exit(1);
                    }
                    return;
                }

                if (antidegree_v == degree)
                {
                    do
                    {
                        do
                        {
                            vector<int> permutationOfDimensions;
                            // insert neighbors
                            for (int i = 0; i < (int)neighbors.size(); i++)
                                permutationOfDimensions.push_back(neighbors[i]);
                            // insert non_neighbors first
                            for (int i = 0; i < (int)non_neighbors.size(); i++)
                                permutationOfDimensions.push_back(non_neighbors[i]);

                            if (!testPermutation(v, permutationOfDimensions, true))
                                return;

                        } while (std::next_permutation(non_neighbors.begin(), non_neighbors.end()));
                    } while (std::next_permutation(neighbors.begin(), neighbors.end()));
                    // TODO improvement; also kinda sort non_neighbors by their degree
                }
            }
        }
    }

    /**
     * @brief Test whether a certain symmetry leads to a smaller coloring of the hypercube
     *
     *
     * @param v The vertex which is mapped to (0,..,0). Gives the flips of the dimensions
     * @param permutationOfDimensions A permutation of the dimensions; permutationOfDimensions[0] gives the value mapped to 0
     * @param negated Whether the coloring should additionally be swapped
     * @return false if it can already be concluded that it is not minimal, true otherwise
     */
    bool testPermutation(int v, const vector<int> &permutationOfDimensions, bool negated = false)
    {

        // printf("Flip: %s\n", vertex_to_string(v).c_str());
        // printf("Permutation:");
        // for (auto i : permutationOfDimensions)
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

                int perm_flip_u;
                int perm_flip_u2;

                if (true)
                {

                    int perm_u = 0;
                    for (int j = 0; j < k; j++)
                    {
                        setBit(perm_u, permutationOfDimensions[j], getBit(u, j));
                    }
                    perm_flip_u = perm_u ^ v; // flip bits where v is 1

                    // same for u2
                    // WRONG but don't know why yet: int perm_flip_u2 = flipBit(perm_flip_u, permutationOfDimensions[i]); // TODO check

                    int perm_u2 = 0;
                    for (int j = 0; j < k; j++)
                    {
                        setBit(perm_u2, permutationOfDimensions[j], getBit(u2, j));
                    }
                    perm_flip_u2 = perm_u2 ^ v; // flip bits where v is 1
                }
                else
                {
                    // first flip then permute
                    int flip_u = u ^ v;
                    perm_flip_u = 0;
                    for (int j = 0; j < k; j++)
                    {
                        setBit(perm_flip_u, j, getBit(flip_u, permutationOfDimensions[j]));
                    }

                    int flip_u2 = u2 ^ v;
                    perm_flip_u2 = 0;
                    for (int j = 0; j < k; j++)
                    {
                        setBit(perm_flip_u2, j, getBit(flip_u2, permutationOfDimensions[j]));
                    }
                }

                // printf("test edge %s %s\n", vertex_to_string(u).c_str(), vertex_to_string(u2).c_str());
                // printf("vs   edge %s %s\n", vertex_to_string(perm_flip_u).c_str(), vertex_to_string(perm_flip_u2).c_str());

                // swap perm_flip_u and perm_flip_u2 if necessary
                if (perm_flip_u > perm_flip_u2)
                    std::swap(perm_flip_u, perm_flip_u2);

                if (!negated)
                    if (u == perm_flip_u && u2 == perm_flip_u2)
                        continue; // same edge, skip

                // printf("v: %d\n", v);
                // printf("u: %d\n", u);
                // printf("%d %d %d %d\n",perm_flip_u, permutationOfDimensions[i], (int) matrix.size(), (int) matrix[0].size());

                // TODO learn clause
                int edgeOrig = edge_to_variable[u][i];

                // get the bit where they are different
                int m = 0;
                for (; m < k; m++)
                    if (getBit(perm_flip_u, m) != getBit(perm_flip_u2, m))
                        break;
                if (m == k)
                    exit(1);
                if (flipBit(perm_flip_u, m) != perm_flip_u2)
                {
                    printf("Error\n");
                    exit(1);
                }

                int edgePerm = edge_to_variable[perm_flip_u][m]; // TODO check whether this correct

                truth_value_t valOriginal = matrix[u][i];
                truth_value_t valPermuted = matrix[perm_flip_u][m];

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

                    clause.push_back(-edgeOrig);
                    if (!negated)
                        clause.push_back(edgePerm); // TODO check whether this correct
                    else
                        clause.push_back(-edgePerm);

                    // Done
                    clauses.push_back(clause);
                    num_learned_clauses++;

                    // printf("Symmetry breaking clause: ");
                    // for (auto lit: clause)
                    //     printf(" %d", lit);
                    // printf("\n");
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
                    if (!negated)
                        clause.push_back(edgePerm);
                    else
                        clause.push_back(-edgePerm);
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
    printf("Time in minimality check: %f\n", ((double)p->time_in_minimality) / CLOCKS_PER_SEC);
    printf("Time in propagator: %f\n", ((double)p->time_in_minimality + p->time_in_propagator) / CLOCKS_PER_SEC);
    printf("Calls of mincheck %d\n", p->calls_check);
    printf("Number of learned clauses: %d\n", p->num_learned_clauses);
    printf("Number of edges: %d\n", num_edges);
    return 0;
}