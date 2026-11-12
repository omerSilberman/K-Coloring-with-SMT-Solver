// String helpers shared by the string encodings of every engine.
#pragma once

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

// The n-th name in A, B, ..., Z, a, ..., z, AA, AB, ... (n >= 1): the color literals
// of STRING and STR-REG
inline std::string int_to_alpha(int n) {
    std::string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    std::string result = "";
    while (n > 0) {
        n--;
        result = chars[n % 52] + result;
        n /= 52;
    }
    return result;
}

#ifndef SUBSTRING_TABLE_PATH
#define SUBSTRING_TABLE_PATH "substring_strings.txt"
#endif

// STR-SUB's word: a string with exactly K distinct substrings (the empty one included).
// Looks K up in the table written by gen_substring_strings.py ("K string" per line).
// Outside the table, 'a' repeated K-1 times has exactly K distinct substrings
// ("", "a", ..., "a"*(K-1)).
inline std::string substring_word(int K) {
    std::ifstream table(SUBSTRING_TABLE_PATH);
    if (!table.is_open()) {
        std::cerr << "Warning: could not open " << SUBSTRING_TABLE_PATH
                  << ", using the fallback string" << std::endl;
    }
    std::string line;
    while (std::getline(table, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::stringstream ss(line);
        int k;
        std::string w;  // stays empty for K = 1, whose only substring is ""
        ss >> k >> w;
        if (k == K) return w;
    }
    return std::string(K - 1, 'a');
}

#include <algorithm>
#include <set>
#include <vector>

// The distinct substrings of word, the empty one included, shortest first (STR-SUB's colors)
inline std::vector<std::string> distinct_substrings(const std::string& word) {
    std::set<std::string> found{""};
    for (size_t i = 0; i < word.size(); i++) {
        for (size_t len = 1; i + len <= word.size(); len++) found.insert(word.substr(i, len));
    }
    std::vector<std::string> out(found.begin(), found.end());
    std::stable_sort(out.begin(), out.end(), [](const std::string& a, const std::string& b) { return a.size() < b.size(); });
    return out;
}
