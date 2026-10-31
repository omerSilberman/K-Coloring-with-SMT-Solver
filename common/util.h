// Small helpers shared by several encodings.
#pragma once

inline bool is_prime(int n) {
    if (n < 2) return false;
    for (int d = 2; d * d <= n; d++) {
        if (n % d == 0) return false;
    }
    return true;
}

#include <vector>

// The prime factors of n with repetition, smallest first (12 -> 2, 2, 3; 1 -> none)
inline std::vector<int> prime_factors(int n) {
    std::vector<int> factors;
    for (int p = 2; (long long)p * p <= n; p++) {
        while (n % p == 0) {
            factors.push_back(p);
            n /= p;
        }
    }
    if (n > 1) factors.push_back(n);
    return factors;
}
