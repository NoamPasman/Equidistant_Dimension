#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

// The largest set considered has eight elements.  Shorter cases use only the
// first q entries of these arrays.
constexpr int max_q = 8;
using Partition = std::array<std::uint8_t, max_q>;
using Permutation = std::array<std::uint8_t, max_q>;
using Vertex = std::array<int, 3>;

struct TestResult {
  bool is_equalizer = true;
  Vertex bad_x{};
  Vertex bad_y{};
};

struct CaseResult {
  std::uint64_t orbit_count = 0;
  std::uint64_t equalizer_count = 0;
  std::uint64_t labeled_orbit_sum = 0;
  std::uint64_t expected_labeled_sets = 0;
};

int f(int a) {
  switch (a) {
    case 3:
      return 7;
    case 4:
      return 8;
    case 5:
    case 6:
      return 9;
    default:
      throw std::invalid_argument("a must be one of 3, 4, 5, 6");
  }
}

std::uint64_t factorial(int n) {
  std::uint64_t result = 1;
  for (int i = 2; i <= n; ++i) {
    result *= i;
  }
  return result;
}

std::uint64_t choose(int n, int k) {
  __uint128_t result = 1;
  for (int i = 1; i <= k; ++i) {
    result = result * (n - k + i) / i;
  }
  return static_cast<std::uint64_t>(result);
}

int integer_power(int base, int exponent) {
  int result = 1;
  for (int i = 0; i < exponent; ++i) {
    result *= base;
  }
  return result;
}

int partition_code(const Partition& partition, int q) {
  int code = 0;
  for (int i = 0; i < q; ++i) {
    code = q * code + partition[i];
  }
  return code;
}

int block_count(const Partition& partition, int q) {
  return 1 + *std::max_element(partition.begin(), partition.begin() + q);
}

std::uint32_t equality_mask(const Partition& partition, int q) {
  std::uint32_t mask = 0;
  int bit = 0;
  for (int i = 0; i < q; ++i) {
    for (int j = i + 1; j < q; ++j, ++bit) {
      if (partition[i] == partition[j]) {
        mask |= std::uint32_t{1} << bit;
      }
    }
  }
  return mask;
}

// A restricted-growth string is a canonical encoding of a set partition.
void generate_partitions_at(int q, int position, int maximum,
                            Partition& current,
                            std::vector<Partition>& partitions) {
  if (position == q) {
    partitions.push_back(current);
    return;
  }
  for (int value = 0; value <= maximum + 1; ++value) {
    current[position] = value;
    generate_partitions_at(q, position + 1, std::max(maximum, value), current,
                           partitions);
  }
}

std::vector<Partition> generate_partitions(int q) {
  std::vector<Partition> partitions;
  Partition current{};
  current[0] = 0;
  generate_partitions_at(q, 1, 0, current, partitions);
  return partitions;
}

void generate_shapes_at(int maximum_blocks, int remaining, int maximum_part,
                        std::vector<int>& block_sizes,
                        std::vector<Partition>& shapes) {
  if (static_cast<int>(block_sizes.size()) > maximum_blocks) {
    return;
  }
  if (remaining == 0) {
    Partition shape{};
    int position = 0;
    for (int label = 0; label < static_cast<int>(block_sizes.size()); ++label) {
      for (int count = 0; count < block_sizes[label]; ++count) {
        shape[position++] = label;
      }
    }
    shapes.push_back(shape);
    return;
  }

  for (int part = std::min(remaining, maximum_part); part >= 1; --part) {
    block_sizes.push_back(part);
    generate_shapes_at(maximum_blocks, remaining - part, part, block_sizes,
                       shapes);
    block_sizes.pop_back();
  }
}

// One representative for every possible multiplicity pattern in coordinate 3.
std::vector<Partition> generate_third_coordinate_shapes(int q, int a) {
  std::vector<Partition> shapes;
  std::vector<int> block_sizes;
  generate_shapes_at(a, q, q, block_sizes, shapes);
  std::sort(shapes.begin(), shapes.end(), [q](const auto& left,
                                               const auto& right) {
    const int left_blocks = block_count(left, q);
    const int right_blocks = block_count(right, q);
    if (left_blocks != right_blocks) {
      return left_blocks < right_blocks;
    }
    return left < right;
  });
  return shapes;
}

std::string vertex_string(const Vertex& vertex) {
  std::ostringstream out;
  out << '(' << vertex[0] + 1 << ',' << vertex[1] + 1 << ','
      << vertex[2] + 1 << ')';
  return out.str();
}

std::string set_string(const Partition& p1, const Partition& p2,
                       const Partition& p3, int q) {
  std::vector<Vertex> vertices;
  vertices.reserve(q);
  for (int i = 0; i < q; ++i) {
    vertices.push_back({p1[i], p2[i], p3[i]});
  }
  std::sort(vertices.begin(), vertices.end());

  std::ostringstream out;
  out << '{';
  for (int i = 0; i < q; ++i) {
    if (i != 0) {
      out << ',';
    }
    out << vertex_string(vertices[i]);
  }
  out << '}';
  return out.str();
}

std::string multiplicity_string(const Partition& partition, int q) {
  std::vector<int> sizes(block_count(partition, q), 0);
  for (int i = 0; i < q; ++i) {
    ++sizes[partition[i]];
  }
  std::sort(sizes.rbegin(), sizes.rend());

  std::ostringstream out;
  for (std::size_t i = 0; i < sizes.size(); ++i) {
    if (i != 0) {
      out << '+';
    }
    out << sizes[i];
  }
  return out.str();
}

int projected_side(int ell, int a) {
  return ell >= a ? ell : ell + 1;
}

// In a product of complete graphs, distance is Hamming distance.  The two-bit
// field for s stores the number of coordinates shared with the sth element of
// S.  A pair is bad exactly when all corresponding fields are different.
TestResult test_equalizer(const Partition& p1, const Partition& p2,
                          const Partition& p3, int q, int m1, int m2,
                          int m3) {
  std::vector<bool> selected(m1 * m2 * m3, false);
  for (int s = 0; s < q; ++s) {
    selected[(p1[s] * m2 + p2[s]) * m3 + p3[s]] = true;
  }

  std::vector<Vertex> outside;
  std::vector<std::uint16_t> signatures;
  outside.reserve(m1 * m2 * m3 - q);
  signatures.reserve(m1 * m2 * m3 - q);

  for (int x1 = 0; x1 < m1; ++x1) {
    for (int x2 = 0; x2 < m2; ++x2) {
      for (int x3 = 0; x3 < m3; ++x3) {
        if (selected[(x1 * m2 + x2) * m3 + x3]) {
          continue;
        }
        outside.push_back({x1, x2, x3});
        std::uint16_t signature = 0;
        for (int s = 0; s < q; ++s) {
          const int matches = (p1[s] == x1) + (p2[s] == x2) +
                              (p3[s] == x3);
          signature |= static_cast<std::uint16_t>(matches << (2 * s));
        }
        signatures.push_back(signature);
      }
    }
  }

  std::uint16_t field_mask = 0;
  for (int s = 0; s < q; ++s) {
    field_mask |= static_cast<std::uint16_t>(1u << (2 * s));
  }

  for (std::size_t i = 0; i < outside.size(); ++i) {
    for (std::size_t j = i + 1; j < outside.size(); ++j) {
      const std::uint16_t difference = signatures[i] ^ signatures[j];
      const std::uint16_t nonzero_fields =
          (difference | (difference >> 1)) & field_mask;
      if (nonzero_fields == field_mask) {
        return {false, outside[i], outside[j]};
      }
    }
  }
  return {};
}

class PartitionSystem {
 public:
  explicit PartitionSystem(int q)
      : q(q),
        partitions(generate_partitions(q)),
        partition_count(static_cast<int>(partitions.size())),
        code_to_index(integer_power(q, q), no_index) {
    equality_masks.reserve(partitions.size());
    for (int i = 0; i < partition_count; ++i) {
      code_to_index[partition_code(partitions[i], q)] = i;
      equality_masks.push_back(equality_mask(partitions[i], q));
    }

    Permutation permutation{};
    std::iota(permutation.begin(), permutation.begin() + q, 0);
    do {
      permutations.push_back(permutation);
    } while (std::next_permutation(permutation.begin(),
                                   permutation.begin() + q));

    std::cout << "q=" << q << ": " << partition_count
              << " set partitions and " << permutations.size()
              << " permutations; building action table..." << std::flush;

    action_table.resize(permutations.size() * partitions.size());
    for (std::size_t g = 0; g < permutations.size(); ++g) {
      for (int p = 0; p < partition_count; ++p) {
        const Partition image = permute_and_normalize(partitions[p],
                                                      permutations[g]);
        const auto image_index = code_to_index[partition_code(image, q)];
        if (image_index == no_index) {
          throw std::logic_error("partition action lookup failed");
        }
        action_table[g * partitions.size() + p] = image_index;
      }
    }
    std::cout << " done\n";
  }

  int code(const Partition& partition) const {
    return partition_code(partition, q);
  }

  Partition permute_and_normalize(const Partition& partition,
                                  const Permutation& permutation) const {
    std::array<int, max_q> new_label;
    new_label.fill(-1);
    int next_label = 0;
    Partition result{};
    for (int i = 0; i < q; ++i) {
      const int old_label = partition[permutation[i]];
      if (new_label[old_label] == -1) {
        new_label[old_label] = next_label++;
      }
      result[i] = new_label[old_label];
    }
    return result;
  }

  const std::uint16_t* action_row(int permutation_index) const {
    return &action_table[static_cast<std::size_t>(permutation_index) *
                         partitions.size()];
  }

  static constexpr std::uint16_t no_index =
      std::numeric_limits<std::uint16_t>::max();

  int q;
  std::vector<Partition> partitions;
  int partition_count;
  std::vector<std::uint16_t> code_to_index;
  std::vector<std::uint32_t> equality_masks;
  std::vector<Permutation> permutations;
  std::vector<std::uint16_t> action_table;
};

CaseResult verify_case(int a, const PartitionSystem& system,
                       const std::string& csv_prefix) {
  const int q = f(a) - 1;
  if (system.q != q) {
    throw std::logic_error("partition system has the wrong value of q");
  }

  std::ofstream csv;
  std::vector<char> csv_buffer;
  if (!csv_prefix.empty()) {
    csv_buffer.resize(1 << 20);
    csv.rdbuf()->pubsetbuf(csv_buffer.data(), csv_buffer.size());
    const std::string path = csv_prefix + "_a" + std::to_string(a) + ".csv";
    csv.open(path);
    if (!csv) {
      throw std::runtime_error("could not open " + path);
    }
    csv << "class_id,third_coordinate_multiplicities,projection_1,"
           "projection_2,projection_3,H,labeled_orbit_size,representative,"
           "is_distance_equalizer,bad_x,bad_y\n";
  }

  const auto shapes = generate_third_coordinate_shapes(q, a);
  const std::uint64_t automorphism_group_size =
      2 * factorial(q) * factorial(q) * factorial(a);
  CaseResult result;
  result.expected_labeled_sets = choose(q * q * a, q);
  std::map<std::array<int, 3>, std::uint64_t> classes_by_graph;

  std::cout << "\nChecking a=" << a << ", q=f(a)-1=" << q << " across "
            << shapes.size() << " third-coordinate shapes\n";

  for (const auto& p3 : shapes) {
    const int ell3 = block_count(p3, q);
    const auto p3_index = system.code_to_index[system.code(p3)];
    std::vector<int> stabilizer_rows;
    for (int g = 0; g < static_cast<int>(system.permutations.size()); ++g) {
      if (system.action_row(g)[p3_index] == p3_index) {
        stabilizer_rows.push_back(g);
      }
    }

    // Coordinates 1 and 2 have the same ambient size, so their two partition
    // indices are stored in increasing order.  The visited table quotients by
    // both their swap and the stabilizer of the fixed third-coordinate shape.
    std::vector<bool> visited(
        static_cast<std::size_t>(system.partition_count) *
            system.partition_count,
        false);
    const std::uint32_t p3_mask = equality_mask(p3, q);
    std::uint64_t shape_orbits = 0;

    for (int i = 0; i < system.partition_count; ++i) {
      for (int j = i; j < system.partition_count; ++j) {
        const std::size_t pair_key =
            static_cast<std::size_t>(i) * system.partition_count + j;
        if (visited[pair_key]) {
          continue;
        }

        // If two selected positions agree in all three partitions, they would
        // represent the same vertex, so this is not a q-element subset.
        if ((system.equality_masks[i] & system.equality_masks[j] & p3_mask) !=
            0) {
          continue;
        }

        std::uint64_t direct_stabilizer = 0;
        std::uint64_t swapped_stabilizer = 0;
        for (const int g : stabilizer_rows) {
          const auto* action = system.action_row(g);
          int image_i = action[i];
          int image_j = action[j];
          if (image_i > image_j) {
            std::swap(image_i, image_j);
          }
          visited[static_cast<std::size_t>(image_i) *
                      system.partition_count +
                  image_j] = true;
          direct_stabilizer += action[i] == i && action[j] == j;
          swapped_stabilizer += action[i] == j && action[j] == i;
        }

        const auto& p1 = system.partitions[i];
        const auto& p2 = system.partitions[j];
        const int ell1 = block_count(p1, q);
        const int ell2 = block_count(p2, q);
        const int m1 = projected_side(ell1, a);
        const int m2 = projected_side(ell2, a);
        const int m3 = projected_side(ell3, a);
        const TestResult test =
            test_equalizer(p1, p2, p3, q, m1, m2, m3);

        const std::uint64_t unused_label_stabilizer =
            factorial(q - ell1) * factorial(q - ell2) * factorial(a - ell3);
        const std::uint64_t set_stabilizer =
            (direct_stabilizer + swapped_stabilizer) *
            unused_label_stabilizer;
        if (set_stabilizer == 0 ||
            automorphism_group_size % set_stabilizer != 0) {
          throw std::logic_error("invalid orbit-stabilizer calculation");
        }
        const std::uint64_t labeled_orbit_size =
            automorphism_group_size / set_stabilizer;

        ++result.orbit_count;
        ++shape_orbits;
        result.equalizer_count += test.is_equalizer;
        result.labeled_orbit_sum += labeled_orbit_size;
        ++classes_by_graph[{m1, m2, m3}];

        if (test.is_equalizer) {
          std::cout << "  EQUALIZER FOUND: a=" << a << ", H=K" << m1
                    << " x K" << m2 << " x K" << m3 << ", S="
                    << set_string(p1, p2, p3, q) << '\n';
        }

        if (csv) {
          csv << result.orbit_count << ',' << multiplicity_string(p3, q) << ','
              << ell1 << ',' << ell2 << ',' << ell3 << ',' << m1 << 'x' << m2
              << 'x' << m3 << ',' << labeled_orbit_size << ",\""
              << set_string(p1, p2, p3, q) << "\"," << test.is_equalizer
              << ',';
          if (test.is_equalizer) {
            csv << ",\n";
          } else {
            csv << '\"' << vertex_string(test.bad_x) << "\",\""
                << vertex_string(test.bad_y) << "\"\n";
          }
        }
      }
    }

    std::cout << "  shape " << multiplicity_string(p3, q) << ": "
              << shape_orbits << " orbits checked\n"
              << std::flush;
  }

  std::cout << "Summary for a=" << a << ":\n"
            << "  symmetry classes: " << result.orbit_count << '\n'
            << "  distance-equalizing classes: " << result.equalizer_count
            << '\n'
            << "  labeled orbit-size sum: " << result.labeled_orbit_sum << '\n'
            << "  all labeled q-subsets: " << result.expected_labeled_sets
            << '\n'
            << "  completeness: "
            << (result.labeled_orbit_sum == result.expected_labeled_sets
                    ? "PASS"
                    : "FAIL")
            << '\n';
  std::cout << "  classes by H:\n";
  for (const auto& [graph, count] : classes_by_graph) {
    std::cout << "    K" << graph[0] << " x K" << graph[1] << " x K"
              << graph[2] << ": " << count << '\n';
  }

  return result;
}

void print_usage(const char* program) {
  std::cout << "Usage: " << program
            << " [--a 3|4|5|6] [--csv-prefix PREFIX]\n"
            << "With no --a option, all four cases are checked.\n"
            << "CSV output is optional because the a=5,6 files are large.\n";
}

}  // namespace

int main(int argc, char** argv) {
  int requested_a = 0;
  std::string csv_prefix;
  for (int i = 1; i < argc; ++i) {
    const std::string argument = argv[i];
    if (argument == "--a" && i + 1 < argc) {
      requested_a = std::stoi(argv[++i]);
      if (requested_a < 3 || requested_a > 6) {
        print_usage(argv[0]);
        return 2;
      }
    } else if (argument == "--csv-prefix" && i + 1 < argc) {
      csv_prefix = argv[++i];
    } else if (argument == "--help") {
      print_usage(argv[0]);
      return 0;
    } else {
      print_usage(argv[0]);
      return 2;
    }
  }

  bool all_cases_pass = true;
  for (const int q : {6, 7, 8}) {
    std::vector<int> cases;
    for (const int a : {3, 4, 5, 6}) {
      if (f(a) - 1 == q && (requested_a == 0 || requested_a == a)) {
        cases.push_back(a);
      }
    }
    if (cases.empty()) {
      continue;
    }

    // The large q=8 action table is built once and reused for a=5 and a=6.
    const PartitionSystem system(q);
    for (const int a : cases) {
      const CaseResult result = verify_case(a, system, csv_prefix);
      const bool complete =
          result.labeled_orbit_sum == result.expected_labeled_sets;
      const bool no_equalizer = result.equalizer_count == 0;
      all_cases_pass = all_cases_pass && complete && no_equalizer;
    }
  }

  std::cout << "\nComputational lemma: "
            << (all_cases_pass ? "VERIFIED" : "NOT VERIFIED") << '\n';
  return all_cases_pass ? 0 : 1;
}
