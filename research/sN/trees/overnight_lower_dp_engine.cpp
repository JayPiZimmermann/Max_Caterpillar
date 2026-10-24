// Single-thread modular evaluator for the independently controlled subset DAG.
// Compile: g++ -O3 -std=c++17 overnight_lower_dp_engine.cpp -o /tmp/overnight_lower_dp_engine
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

static constexpr uint64_t P = 1000003;

static uint64_t residue(int64_t x) {
    int64_t r = x % int64_t(P);
    return r < 0 ? r + P : r;
}

static uint64_t power(uint64_t value, uint64_t exponent) {
    uint64_t out = 1;
    while (exponent) {
        if (exponent & 1) out = out * value % P;
        value = value * value % P;
        exponent >>= 1;
    }
    return out;
}

static std::vector<uint32_t> read_array(std::ifstream &input, size_t count) {
    std::vector<uint32_t> out(count);
    input.read(reinterpret_cast<char *>(out.data()), count * sizeof(uint32_t));
    if (!input) throw std::runtime_error("truncated DAG");
    return out;
}

int main(int argc, char **argv) {
    try {
        if (argc != 4) throw std::runtime_error("arguments: DAG POINTS_TEXT OUTPUT_U32");
        const auto started = std::chrono::steady_clock::now();
        std::ifstream dag(argv[1], std::ios::binary);
        uint64_t header[6];
        dag.read(reinterpret_cast<char *>(header), sizeof(header));
        if (!dag || header[0] != 0x445053594D545245ULL) throw std::runtime_error("bad DAG header/endian");
        const uint64_t N = header[1], states = header[2], terms = header[3], columns = header[4], factors_used = header[5];
        auto starts = read_array(dag, states + 1);
        auto left = read_array(dag, terms), right = read_array(dag, terms), bridge = read_array(dag, terms);
        auto roots = read_array(dag, columns), used = read_array(dag, factors_used);
        if (N < 4 || N > 20 || starts.back() != terms) throw std::runtime_error("invalid DAG dimensions");
        for (uint64_t state = 1; state <= states; ++state)
            for (uint64_t j = starts[state - 1]; j < starts[state]; ++j)
                if (left[j] >= state || right[j] >= state) throw std::runtime_error("non-topological DAG");
        std::ifstream points(argv[2]);
        uint64_t rows, point_arity;
        points >> rows >> point_arity;
        if (!points || point_arity != N) throw std::runtime_error("bad point header");
        std::ofstream output(argv[3], std::ios::binary);
        const uint64_t masks = 1ULL << (N - 1);
        std::vector<int64_t> point(N), frequencies(N - 1), sums(masks);
        std::vector<uint64_t> factors(2 * masks), denominator(factors_used), prefix(factors_used + 1), values(states + 1), total(columns);
        std::vector<uint32_t> row(columns + 1);
        values[0] = 1;
        factors[0] = 1;
        for (uint64_t row_index = 0; row_index < rows; ++row_index) {
            int64_t sum = 0;
            for (auto &v : point) { points >> v; sum += v; }
            if (!points || sum) throw std::runtime_error("point missing or not sum-zero");
            std::fill(total.begin(), total.end(), 0);
            for (uint64_t apex = 0; apex < N; ++apex) {
                const int64_t a = point[apex];
                uint64_t pos = 0;
                for (uint64_t v = 0; v < N; ++v) if (v != apex) frequencies[pos++] = point[v];
                sums[0] = 0;
                for (uint64_t mask = 1; mask < masks; ++mask) {
                    uint64_t bit = mask & -mask;
                    sums[mask] = sums[mask ^ bit] + frequencies[__builtin_ctzll(bit)];
                }
                prefix[0] = 1;
                for (uint64_t j = 0; j < factors_used; ++j) {
                    const uint64_t index = used[j];
                    const int64_t q = sums[index / 2], shift = index & 1 ? -a : a;
                    denominator[j] = residue(q) * residue(q + shift) % P;
                    if (!denominator[j]) throw std::runtime_error("singular point");
                    prefix[j + 1] = prefix[j] * denominator[j] % P;
                }
                uint64_t inverse = power(prefix[factors_used], P - 2);
                for (uint64_t j = factors_used; j-- > 0;) {
                    factors[used[j]] = inverse * prefix[j] % P;
                    inverse = inverse * denominator[j] % P;
                }
                for (uint64_t state = 1; state <= states; ++state) {
                    uint64_t sum_value = 0;
                    for (uint64_t term = starts[state - 1]; term < starts[state]; ++term) {
                        uint64_t value = values[left[term]] * values[right[term]] % P;
                        sum_value += value * factors[bridge[term]] % P;
                    }
                    values[state] = sum_value % P;
                }
                const uint64_t multiplier = power(residue(-a), N - 4);
                for (uint64_t j = 0; j < columns; ++j) total[j] += multiplier * values[roots[j]];
            }
            for (uint64_t j = 0; j < columns; ++j) row[j] = total[j] % P;
            uint64_t target_denominator = 1;
            for (const auto v : point) target_denominator = target_denominator * residue(v) % P;
            if (!target_denominator) throw std::runtime_error("zero target denominator");
            uint64_t target = power(target_denominator, P - 2);
            if ((N - 1) & 1) target = P - target;
            row[columns] = target;
            output.write(reinterpret_cast<char *>(row.data()), row.size() * sizeof(uint32_t));
            if ((row_index + 1) % 16 == 0 || row_index + 1 == rows) {
                output.flush();
                const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
                std::cout << "ROWS " << row_index + 1 << " SECONDS " << seconds << std::endl;
            }
        }
        if (!output) throw std::runtime_error("output write failure");
        const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
        std::cout << "DONE " << rows << " ROWS " << columns << " COLUMNS " << states
                  << " STATES " << terms << " TERMS SECONDS " << seconds << std::endl;
    } catch (const std::exception &error) {
        std::cerr << "ERROR " << error.what() << std::endl;
        return 2;
    }
    return 0;
}
