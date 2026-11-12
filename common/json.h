// Tiny JSON writing helpers (for --list-json and the STRATEGY-JSON lines).
#pragma once

#include <sstream>
#include <string>
#include <vector>

inline std::string json_string(const std::string& s) {
    std::ostringstream out;
    out << '"';
    for (char c : s) {
        switch (c) {
        case '"': out << "\\\""; break;
        case '\\': out << "\\\\"; break;
        case '\n': out << "\\n"; break;
        default:
            if ((unsigned char)c < 0x20) out << "\\u00" << "0123456789abcdef"[c >> 4] << "0123456789abcdef"[c & 15];
            else out << c;
        }
    }
    out << '"';
    return out.str();
}

inline std::string json_ints(const std::vector<int>& values) {
    std::string out = "[";
    for (size_t i = 0; i < values.size(); i++) out += (i ? "," : "") + std::to_string(values[i]);
    return out + "]";
}
