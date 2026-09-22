// Exact verifier for the r*(n) problem in 9-20/draft5copy.tex.
//
// Build and run the complete n < 64 certificate:
//   clang++ -std=c++17 -O3 -DNDEBUG Miscellaneous/exact_rstar.cpp -o exact_rstar
//   ./exact_rstar
// List every maximizer for one value of n:
//   ./exact_rstar --list 31
//
// The zero-based rewrite in draft5copy has two transcription slips.  The
// reflected gap is n-2-u_i (not n-1-u_i), and the even bound is
// n/2+tau(n+1).  Both corrections follow directly from the earlier one-based
// version in 9-13/draft5.tex.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <functional>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace rstar {

using Mask = std::uint64_t;

static int popcount(Mask x) { return __builtin_popcountll(x); }
static int ctz(Mask x) { return __builtin_ctzll(x); }

static Mask universe_mask(int n) {
    if (n < 1 || n > 63) throw std::invalid_argument("n must be in [1,63]");
    return (Mask{1} << n) - 1;
}

struct Hypergraph {
    int n = 0;
    Mask universe = 0;
    std::vector<Mask> edges;

    explicit Hypergraph(int n_) : n(n_), universe(universe_mask(n_)) {
        for (int ell = 1; 2 * ell + 1 < n; ell += 2) {
            for (int m = 0; m + 2 * ell + 1 < n; ++m) {
                Mask e = (Mask{1} << m) | (Mask{1} << (m + ell)) |
                         (Mask{1} << (m + ell + 1)) |
                         (Mask{1} << (m + 2 * ell + 1));
                edges.push_back(e);
            }
        }
    }
};

// Exact independent-set solver for the four-uniform hypergraph of banned
// patterns.  IN vertices belong to the candidate set and OUT vertices do not.
// The callback version visits every pattern-free set of exactly target_ points.
class IndependentSetSolver {
public:
    explicit IndependentSetSolver(const Hypergraph& graph) : g(graph) {}

    bool exists_at_least(int target, Mask* witness = nullptr) {
        target_ = target;
        witness_ = 0;
        nodes_ = 0;
        const bool ok = search_one(0, 0);
        if (ok && witness) *witness = witness_;
        return ok;
    }

    // Return false only when the visitor asks to stop early.  Each exact-size
    // solution is produced once; OUT/IN branching partitions all assignments.
    bool enumerate_exact(int target,
                         const std::function<bool(Mask)>& visitor) {
        target_ = target;
        nodes_ = 0;
        visitor_ = &visitor;
        const bool completed = search_all(0, 0);
        visitor_ = nullptr;
        return completed;
    }

    std::uint64_t nodes() const { return nodes_; }

private:
    const Hypergraph& g;
    int target_ = 0;
    Mask witness_ = 0;
    std::uint64_t nodes_ = 0;
    const std::function<bool(Mask)>* visitor_ = nullptr;

    // If an active edge has three IN vertices, its final undecided vertex must
    // be OUT.  Return false on a completed banned pattern.
    bool propagate(Mask in, Mask& out) const {
        bool changed;
        do {
            changed = false;
            for (Mask e : g.edges) {
                if (e & out) continue;
                const Mask undecided = e & ~(in | out);
                if (!undecided) return false;
                if ((undecided & (undecided - 1)) == 0) {
                    out |= undecided;
                    changed = true;
                }
            }
        } while (changed);
        return true;
    }

    // A disjoint packing of active residual edges requires one distinct future
    // OUT vertex per packed edge.  Consequently it is an upper bound on how
    // many of the undecided vertices can eventually be put IN.
    int packing_bound(Mask in, Mask out, std::vector<Mask>& residuals) const {
        residuals.clear();
        for (Mask e : g.edges)
            if (!(e & out)) residuals.push_back(e & ~(in | out));
        int best = 0;
        for (int pass = 0; pass < 4; ++pass) {
            Mask used = 0;
            int count = 0;
            if (pass == 0) {
                for (Mask e : residuals) if (!(e & used)) { used |= e; ++count; }
            } else if (pass == 1) {
                for (auto it = residuals.rbegin(); it != residuals.rend(); ++it)
                    if (!(*it & used)) { used |= *it; ++count; }
            } else {
                std::vector<Mask> ordered = residuals;
                std::sort(ordered.begin(), ordered.end(), [pass](Mask a, Mask b) {
                    if (popcount(a) != popcount(b)) return popcount(a) < popcount(b);
                    return pass == 2 ? a < b : a > b;
                });
                for (Mask e : ordered) if (!(e & used)) { used |= e; ++count; }
            }
            best = std::max(best, count);
        }
        return best;
    }

    // Favor variables in almost-completed patterns.  score weights an active
    // edge by 4^(number already IN), making propagation happen early.
    int branch_vertex(Mask in, Mask out) const {
        std::array<int, 64> score{};
        for (Mask e : g.edges) {
            if (e & out) continue;
            const int weight = 1 << (2 * popcount(e & in));
            Mask t = e & ~(in | out);
            while (t) {
                const int v = ctz(t);
                t &= t - 1;
                score[v] += weight;
            }
        }
        int best = -1;
        Mask undecided = g.universe & ~(in | out);
        while (undecided) {
            const int v = ctz(undecided);
            undecided &= undecided - 1;
            if (best < 0 || score[v] > score[best]) best = v;
        }
        return best;
    }

    bool prepare(Mask in, Mask& out, int& branch) const {
        if (!propagate(in, out)) return false;
        const int have = popcount(in);
        const Mask undecided = g.universe & ~(in | out);
        if (have + popcount(undecided) < target_) return false;
        std::vector<Mask> residuals;
        const int forced_out = packing_bound(in, out, residuals);
        if (have + popcount(undecided) - forced_out < target_) return false;
        branch = branch_vertex(in, out);
        return true;
    }

    bool search_one(Mask in, Mask out) {
        ++nodes_;
        int branch = -1;
        if (!prepare(in, out, branch)) return false;
        if (popcount(in) >= target_) {
            witness_ = in;
            return true;
        }
        const Mask undecided = g.universe & ~(in | out);
        if (popcount(in) + popcount(undecided) == target_) {
            const Mask candidate = in | undecided;
            for (Mask e : g.edges) if ((candidate & e) == e) return false;
            witness_ = candidate;
            return true;
        }
        const Mask bit = Mask{1} << branch;
        if (search_one(in | bit, out)) return true;
        return search_one(in, out | bit);
    }

    bool emit_free_choices(Mask in, Mask undecided, int need) {
        if (need == 0) return (*visitor_)(in);
        if (popcount(undecided) < need) return true;
        if (popcount(undecided) == need) return (*visitor_)(in | undecided);
        const int v = ctz(undecided);
        const Mask bit = Mask{1} << v;
        undecided &= ~bit;
        if (!emit_free_choices(in | bit, undecided, need - 1)) return false;
        return emit_free_choices(in, undecided, need);
    }

    bool search_all(Mask in, Mask out) {
        ++nodes_;
        int branch = -1;
        if (!prepare(in, out, branch)) return true;
        const int have = popcount(in);
        const Mask undecided = g.universe & ~(in | out);
        if (have == target_) return (*visitor_)(in);

        bool has_active_edge = false;
        for (Mask e : g.edges) if (!(e & out)) { has_active_edge = true; break; }
        if (!has_active_edge)
            return emit_free_choices(in, undecided, target_ - have);

        if (have + popcount(undecided) == target_) {
            const Mask candidate = in | undecided;
            for (Mask e : g.edges) if ((candidate & e) == e) return true;
            return (*visitor_)(candidate);
        }

        const Mask bit = Mask{1} << branch;
        if (!search_all(in | bit, out)) return false;
        return search_all(in, out | bit);
    }
};

int lower_bound(int n); // forward declaration for compute_r_star

int compute_r_star(int n, std::uint64_t* nodes = nullptr) {
    Hypergraph g(n);
    IndependentSetSolver solver(g);
    int answer = lower_bound(n);
    std::uint64_t total_nodes = 0;
    Mask witness = 0;
    if (!solver.exists_at_least(answer, &witness))
        throw std::logic_error("the claimed constructive lower bound is infeasible");
    total_nodes += solver.nodes();
    while (solver.exists_at_least(answer + 1, &witness)) {
        total_nodes += solver.nodes();
        ++answer;
    }
    total_nodes += solver.nodes();
    if (nodes) *nodes = total_nodes;
    return answer;
}

std::vector<Mask> list_sets_of_size(int n, int size) {
    Hypergraph g(n);
    IndependentSetSolver solver(g);
    std::vector<Mask> result;
    const std::function<bool(Mask)> collect = [&](Mask s) {
        result.push_back(s);
        return true;
    };
    solver.enumerate_exact(size, collect);
    return result;
}

std::vector<Mask> list_sets_hitting_lower_bound(int n) {
    return list_sets_of_size(n, lower_bound(n));
}

bool visit_sets_of_size(int n, int size,
                        const std::function<bool(Mask)>& visitor,
                        std::uint64_t* nodes = nullptr) {
    Hypergraph g(n);
    IndependentSetSolver solver(g);
    const bool completed = solver.enumerate_exact(size, visitor);
    if (nodes) *nodes = solver.nodes();
    return completed;
}

int tau(int m) {
    if (m < 3) return 0;
    int j = 1;
    long long t = 3;
    while (true) {
        long long next = (j % 2 == 0) ? 2 * t - 1 : 2 * t + 1;
        if (next > m) return j;
        t = next;
        ++j;
    }
}

int lower_bound(int n) {
    if (n & 1) {
        int k = 0;
        for (int x = n + 1; x >= 2; x >>= 1) ++k;
        return (n - 1) / 2 + k;
    }
    return n / 2 + tau(n + 1);
}

Mask construction(int n) {
    std::vector<int> u;
    u.push_back(0);
    for (int i = 0; i < 20; ++i) {
        long long next = 2LL * u.back() + ((i % 2 == 0) ? 1 : 2);
        if (next >= n) break;
        u.push_back(static_cast<int>(next));
    }
    Mask gaps = 0;
    if (n & 1) {
        int k = 0;
        for (int x = n + 1; x >= 2; x >>= 1) ++k;
        for (int i = 0; i <= k - 2; ++i) {
            gaps |= Mask{1} << u[i];
            gaps |= Mask{1} << (n - 2 - u[i]);
        }
    } else {
        int k = tau(n + 1);
        for (int i = 0; i <= k - 1; ++i) gaps |= Mask{1} << u[i];
        for (int i = 0; i <= k - 2; ++i) gaps |= Mask{1} << (n - 2 - u[i]);
    }
    Mask s = 1;
    for (int i = 0; i + 1 < n; ++i) {
        if ((gaps & (Mask{1} << i)) || !(s & (Mask{1} << i)))
            s |= Mask{1} << (i + 1);
    }
    return s;
}

static bool pattern_free(const Hypergraph& g, Mask s) {
    for (Mask e : g.edges) if ((s & e) == e) return false;
    return true;
}

static std::string set_string(Mask s, int n) {
    std::string out = "{";
    bool first = true;
    for (int i = 0; i < n; ++i) if (s & (Mask{1} << i)) {
        if (!first) out += ',';
        first = false;
        out += std::to_string(i);
    }
    return out + "}";
}

static Mask reverse_mask(Mask s, int n) {
    Mask reversed = 0;
    for (int i = 0; i < n; ++i)
        if (s & (Mask{1} << i)) reversed |= Mask{1} << (n - 1 - i);
    return reversed;
}

static bool isomorphic_to(Mask a, Mask b, int n) {
    // These are the two path isomorphisms: identity and interval reversal.
    return a == b || reverse_mask(a, n) == b;
}

struct EnumerationSummary {
    std::uint64_t sets = 0;
    std::uint64_t reversal_fixed_sets = 0;
    std::uint64_t nodes = 0;
    bool construction_orbit_only = true;
    Mask first_other = 0;

    std::uint64_t reversal_orbits() const {
        return (sets + reversal_fixed_sets) / 2;
    }
};

static EnumerationSummary summarize_sets(int n, int size, Mask built) {
    EnumerationSummary summary;
    const std::function<bool(Mask)> inspect = [&](Mask s) {
        ++summary.sets;
        if (reverse_mask(s, n) == s) ++summary.reversal_fixed_sets;
        if (summary.construction_orbit_only && !isomorphic_to(s, built, n)) {
            summary.construction_orbit_only = false;
            summary.first_other = s;
        }
        return true;
    };
    visit_sets_of_size(n, size, inspect, &summary.nodes);
    return summary;
}

static void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error("CHECK FAILED: " + message);
}

// A deliberately simple independent oracle for small n.  It validates both
// the optimized recursion and its enumeration before the large certificates.
static std::pair<int, std::uint64_t> brute_force(int n) {
    Hypergraph g(n);
    int best = -1;
    std::uint64_t count = 0;
    const Mask end = Mask{1} << n;
    for (Mask s = 0; s < end; ++s) {
        if (!pattern_free(g, s)) continue;
        const int size = popcount(s);
        if (size > best) { best = size; count = 1; }
        else if (size == best) { ++count; }
    }
    return {best, count};
}

static void self_test() {
    for (int n = 1; n <= 20; ++n) {
        Hypergraph g(n);
        const Mask built = construction(n);
        require(pattern_free(g, built), "construction contains a pattern at n=" + std::to_string(n));
        require(popcount(built) == lower_bound(n), "construction has wrong size at n=" + std::to_string(n));
        for (Mask e : g.edges) {
            const Mask reversed = reverse_mask(e, n);
            require(std::find(g.edges.begin(), g.edges.end(), reversed) != g.edges.end(),
                    "reversal does not preserve the banned hypergraph at n=" + std::to_string(n));
        }

        const auto [brute_best, brute_count] = brute_force(n);
        const int exact = compute_r_star(n);
        require(exact == brute_best, "optimized r*(n) disagrees with brute force at n=" + std::to_string(n));
        auto listed = list_sets_of_size(n, exact);
        require(listed.size() == brute_count, "enumerator disagrees with brute force at n=" + std::to_string(n));
        for (Mask s : listed) {
            require(popcount(s) == exact && pattern_free(g, s),
                    "enumerator emitted an invalid set at n=" + std::to_string(n));
        }
        std::sort(listed.begin(), listed.end());
        require(std::adjacent_find(listed.begin(), listed.end()) == listed.end(),
                "enumerator emitted a duplicate at n=" + std::to_string(n));
    }
}

} // namespace rstar

int main(int argc, char** argv) {
    using namespace rstar;
    try {
    if (argc == 3 && std::string(argv[1]) == "--list") {
        const int n = std::stoi(argv[2]);
        const int exact = compute_r_star(n);
        const auto sets = list_sets_of_size(n, exact);
        std::cout << "r*(" << n << ")=" << exact << "; " << sets.size()
                  << " maximum set(s):\n";
        for (Mask s : sets) std::cout << set_string(s, n) << '\n';
        return 0;
    }

    int k = 6;
    if (argc == 3 && std::string(argv[1]) == "--sweep-k") k = std::stoi(argv[2]);
    else if (argc != 1) {
        std::cerr << "usage: " << argv[0] << " [--sweep-k k | --list n]\n";
        return 2;
    }
    require(k >= 0 && k <= 6, "this 64-bit verifier requires 0 <= k <= 6");
    self_test();
    std::cout << "small_bruteforce_cross_check=PASS (n<=20)\n";
    std::cout << "isomorphism=identity_or_reversal_i_to_n-1-i\n";
    std::cout << "n lower rstar maximum_sets reversal_orbits construction_orbit_only exact_s enum_s\n";

    const int max_n = (1 << k) - 1;
    double total_seconds = 0.0;
    bool all_equal = true;
    bool all_unique_to_construction = true;
    bool special_claims = true;
    std::vector<int> construction_orbit_only_values;
    std::vector<int> literally_unique_values;
    for (int n = 1; n <= max_n; ++n) {
        auto start = std::chrono::steady_clock::now();
        std::uint64_t nodes = 0;
        int exact = compute_r_star(n, &nodes);
        const double exact_seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        Mask built = construction(n);
        Hypergraph g(n);
        require(pattern_free(g, built) && popcount(built) == lower_bound(n),
                "invalid construction for n=" + std::to_string(n));
        all_equal &= exact == lower_bound(n);

        start = std::chrono::steady_clock::now();
        const EnumerationSummary summary = summarize_sets(n, exact, built);
        const double enum_seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        all_unique_to_construction &= summary.construction_orbit_only;
        if (summary.construction_orbit_only) construction_orbit_only_values.push_back(n);
        if (summary.sets == 1) literally_unique_values.push_back(n);
        if (n == 15 || n == 31 || n == 63) {
            const bool claim = exact == lower_bound(n) && summary.sets == 1 &&
                               summary.construction_orbit_only;
            special_claims &= claim;
            require(claim, "the stated uniqueness claim failed at n=" + std::to_string(n));
        }
        total_seconds += exact_seconds + enum_seconds;

        std::cout << std::setw(2) << n << ' ' << std::setw(5) << lower_bound(n)
                  << ' ' << std::setw(5) << exact << ' ' << std::setw(12) << summary.sets
                  << ' ' << std::setw(15) << summary.reversal_orbits() << ' '
                  << (summary.construction_orbit_only ? "YES" : "NO ") << ' '
                  << std::fixed << std::setprecision(4) << exact_seconds << ' '
                  << enum_seconds;
        if (!summary.construction_orbit_only)
            std::cout << " other=" << set_string(summary.first_other, n);
        std::cout << '\n';
    }
    std::cout << "all_rstar_equal_lower_bound=" << (all_equal ? "PASS" : "FAIL") << '\n';
    std::cout << "claims_for_n_15_31_63=" << (special_claims ? "PASS" : "FAIL") << '\n';
    std::cout << "all_maximizers_in_construction_orbit="
              << (all_unique_to_construction ? "PASS" : "FAIL") << '\n';
    std::cout << "construction_orbit_only_n=";
    for (std::size_t i = 0; i < construction_orbit_only_values.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << construction_orbit_only_values[i];
    }
    std::cout << '\n';
    std::cout << "literally_unique_n=";
    for (std::size_t i = 0; i < literally_unique_values.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << literally_unique_values[i];
    }
    std::cout << '\n';
    std::cout << "verified_range=1.." << max_n << " (all n < 2^" << k << ")\n";
    std::cout << "total_solver_seconds=" << std::fixed << std::setprecision(3)
              << total_seconds << '\n';
    return all_equal ? 0 : 1;
    } catch (const std::exception& e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
