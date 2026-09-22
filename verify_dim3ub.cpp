// Exhaustive verification of Lemma \ref{lem:dim3ub} in draft5copy.tex.
//
// Build and run:
//   clang++ -std=c++17 -O2 -Wall -Wextra -Wpedantic \
//       Miscellaneous/verify_dim3ub.cpp -o verify_dim3ub
//   ./verify_dim3ub

#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Vertex = std::array<int, 3>;

int f(int a) {
    switch (a) {
        case 3: return 7;
        case 4: return 8;
        case 5:
        case 6: return 9;
        default: throw std::invalid_argument("a must be one of 3, 4, 5, 6");
    }
}

std::vector<Vertex> proposed_set(int a) {
    if (a == 3) {
        return {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 0},
                {0, 2, 0}, {1, 0, 0}, {2, 0, 0}};
    }
    if (a == 4) {
        return {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 0, 3},
                {0, 1, 0}, {0, 2, 0}, {1, 0, 0}, {2, 0, 0}};
    }
    if (a == 5 || a == 6) {
        return {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 0},
                {0, 2, 0}, {1, 0, 0}, {2, 0, 0}, {1, 1, 1},
                {2, 2, 2}};
    }
    throw std::invalid_argument("a must be one of 3, 4, 5, 6");
}

// Distance in a Cartesian product of complete graphs is Hamming distance.
int distance(const Vertex& x, const Vertex& y) {
    return (x[0] != y[0]) + (x[1] != y[1]) + (x[2] != y[2]);
}

std::string vertex_string(const Vertex& v) {
    return "(" + std::to_string(v[0]) + "," + std::to_string(v[1]) +
           "," + std::to_string(v[2]) + ")";
}

std::vector<Vertex> vertices(int a) {
    // K_{a+1} square K_{a+1} square K_a has coordinates
    // [a+1] x [a+1] x [a], with [m] = {0,...,m-1}.
    std::vector<Vertex> result;
    for (int x = 0; x <= a; ++x)
        for (int y = 0; y <= a; ++y)
            for (int z = 0; z < a; ++z)
                result.push_back({x, y, z});
    return result;
}

struct CheckResult {
    std::uint64_t outside_pairs = 0;
    int minimum_equalizers = 0;
};

CheckResult verify(int a) {
    const std::vector<Vertex> t = proposed_set(a);
    const std::set<Vertex> t_set(t.begin(), t.end());

    if (static_cast<int>(t.size()) != f(a))
        throw std::runtime_error("wrong cardinality for a=" + std::to_string(a));
    if (t_set.size() != t.size())
        throw std::runtime_error("duplicate vertex in T for a=" + std::to_string(a));
    for (const Vertex& x : t) {
        // This is the lemma's stronger containment T subset [a]^3.
        for (int coordinate : x) {
            if (coordinate < 0 || coordinate >= a)
                throw std::runtime_error("T is not contained in [a]^3 for a=" +
                                         std::to_string(a));
        }
    }

    std::vector<Vertex> outside;
    for (const Vertex& v : vertices(a))
        if (!t_set.count(v)) outside.push_back(v);

    CheckResult result;
    result.minimum_equalizers = static_cast<int>(t.size());
    for (std::size_t i = 0; i < outside.size(); ++i) {
        for (std::size_t j = i + 1; j < outside.size(); ++j) {
            ++result.outside_pairs;
            int equalizers = 0;
            for (const Vertex& x : t)
                equalizers += distance(outside[i], x) == distance(outside[j], x);
            if (equalizers == 0) {
                throw std::runtime_error(
                    "uncovered pair for a=" + std::to_string(a) + ": " +
                    vertex_string(outside[i]) + " and " +
                    vertex_string(outside[j]));
            }
            if (equalizers < result.minimum_equalizers)
                result.minimum_equalizers = equalizers;
        }
    }
    return result;
}

}  // namespace

int main() {
    try {
        std::uint64_t total_pairs = 0;
        for (int a : {3, 4, 5, 6}) {
            const CheckResult result = verify(a);
            total_pairs += result.outside_pairs;
            const int vertex_count = (a + 1) * (a + 1) * a;
            std::cout << "a=" << a << " |T|=" << f(a)
                      << " vertices=" << vertex_count
                      << " outside_pairs=" << result.outside_pairs
                      << " minimum_equalizers_per_pair="
                      << result.minimum_equalizers << " PASS\n";
        }
        std::cout << "lemma_dim3ub=PASS total_outside_pairs=" << total_pairs
                  << '\n';
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "lemma_dim3ub=FAIL " << e.what() << '\n';
        return 1;
    }
}
