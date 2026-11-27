// Enumerate the axis moment invariant for the case of 15 pairs in all four families.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

struct Moments {
    int sum{};
    int squares{};
};

int main() {
    constexpr unsigned half = 1U << 15;
    std::array<Moments,half> lower{}, upper{};
    for (unsigned mask = 1; mask < half; ++mask) {
        const unsigned prev = mask & (mask-1);
        const int i = std::countr_zero(mask);
        const int a = 2*i-29, b = a+30;
        lower[mask] = {lower[prev].sum+a, lower[prev].squares+a*a};
        upper[mask] = {upper[prev].sum+b, upper[prev].squares+b*b};
    }
    // |sum| <= 225 and each of the fifteen squared coordinates is <= 29^2.
    constexpr int bias = 5*15*29*29;
    std::vector<std::uint64_t> buckets(bias+21*225*225+1);
    std::uint64_t sets = 0;
    for (unsigned mask = half-1; mask < (1U<<30); ) {
        const auto a = lower[mask&(half-1)], b = upper[mask>>15];
        const int sum = a.sum+b.sum, squares = a.squares+b.squares;
        ++buckets.at(bias+21*sum*sum-5*squares);
        ++sets;
        const unsigned low = mask&-mask, bumped = mask+low;
        mask = bumped|(((bumped^mask)>>2)/low);
    }
    std::uint64_t pairs = 0, nonempty = 0, largest = 0;
    for (auto n : buckets) if (n) {
        ++nonempty;
        if (n>largest) largest=n;
        pairs += n*n;
    }
    std::cout << "axis_masks " << sets << "\nordered_pairs " << sets*sets
              << "\ninvariant_values " << nonempty << "\nlargest_class " << largest
              << "\ncompatible_ordered_pairs " << pairs << "\n";
    return sets==155117520 ? 0 : 1;
}
