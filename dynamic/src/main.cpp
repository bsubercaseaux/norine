/**
 * Program for dynamic symmetry breaking for Norines conjecture using Cadical as underlying solver.
 */

#include "cadical.hpp"
#include <vector>
#include <cstdlib>

using namespace std;

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
    int num_edges;
    int frequency;
    int calls = 0;

    vector<vector<int>> trail;
    bool change_in_trail = true; // true if some variable has changed since last call of the check
    vector<vector<int>> clauses; // clauses which should be added to the solver

    // storing the current state of the coloring. First value gives the vertex and second the neighbor. The k-th neighbor is exactly different in the k-th bit
    vector<vector<truth_value_t>> matrix;

    vector<pair<int, int>> variable_to_edge; // for a given variable indicate to which edge it maps
    vector<vector<int>> edge_to_variable;    // the inverse

public:
    NorinePropagator(int k, int frequency)
    {
        trail.push_back(vector<int>());
        this->k = k;
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
                if ((1 << i) & v)
                    continue;

                var_count++;
                edge_to_variable[v][i] = var_count;
                // also initialize the other edge
                int u = v ^ (1 << i);
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
            trail.back().push_back(lit);
            change_in_trail = true;

            // update matrix
            auto edge = variable_to_edge[abs(lit)];
            int v = edge.first;
            int i = edge.second;
            truth_value_t t = lit > 0 ? truth_value_true : truth_value_false;
            matrix[v][i] = t;
            // also set the other edge
            int u = v ^ (1 << i); // TODO check whether correct
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
                int u = v ^ (1 << i); // TODO check whether correct
                matrix[u][i] = truth_value_unknown;
            }
            trail.pop_back();
        }
    };

    bool cb_check_found_model(const std::vector<int> &model)
    {
        // TODO check

        return true;
    };

    bool cb_has_external_clause(bool &is_forgettable)
    {
        if (!clauses.empty())
            return true;

        if (calls > frequency)
        {
            calls = 0;
            change_in_trail = false;

            // TODO check minimality
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
};

int main(int argc, char **argv)
{
    CaDiCaL::Solver solver = CaDiCaL::Solver();

    if (argc < 3)
    {
        printf("Expected at least 2 argumens dimensions,frequency and evenutally path to encoding");
        exit(1);
    }

    int k = atoi(argv[1]);
    int f = atoi(argv[2]);

    if (argc > 3)
    {
        int vars;
        solver.read_dimacs(argv[3], vars);
    }

    // add propagator
    NorinePropagator *p = new NorinePropagator(k, f);
    solver.connect_external_propagator(p);

    return 0;
}