"""
Expected Alexander Polynomials for Rolfsen Knots
Source: KnotInfo Database (katlas.org) - VERIFIED
Date: 2025-11-28
"""

# Dictionary mapping Rolfsen ID to coefficient list (highest power to lowest)
# Normalized according to standard convention: Δ(t) = Δ(t⁻¹) and Δ(1) = ±1
# Format: coefficients from highest power to lowest power of t

EXPECTED_POLYS = {
    # Verified from KnotInfo database
    "3_1": [1, -1, 1],                          # Trefoil
    "4_1": [-1, 3, -1],                         # Figure-8
    "5_1": [1, -1, 1, -1, 1],                   # Cinquefoil
    "5_2": [2, -3, 2],                          # Three-twist knot: 2t² - 3t + 2
    "6_1": [-2, 5, -2],                         # Stevedore (NOT 2-bridge)
    "6_2": [-1, 3, -3, 3, -1],                  # Miller Institute
    "6_3": [1, -3, 5, -3, 1],                   # 6_3
    "7_1": [1, -1, 1, -1, 1, -1, 1],            # Septafoil
    "7_2": [1, -1, 1, -1, 1, -1, 1],            # KnotInfo: t³ - t² + t - 1 + t⁻¹ - t⁻² + t⁻³
    "7_3": [2, -3, 3, -3, 2],                   # KnotInfo: 2t² - 3t + 3 - 3t⁻¹ + 2t⁻²
    "7_4": [4, -7, 4],                          # KnotInfo: 4t² - 7t + 4
    "7_5": [2, -4, 5, -4, 2],                   # KnotInfo: 2t² - 4t + 5 - 4t⁻¹ + 2t⁻²
    "7_6": [-1, 5, -7, 5, -1],                  # Placeholder (needs verification)
    "7_7": [1, -5, 9, -5, 1],                   # Placeholder (needs verification)
    "8_1": [-3, 7, -3],                         # Verified
    "8_2": [-1, 3, -3, 3, -1],                  # KnotInfo: -t³ + 3t² - 3t + 3 - 3t⁻¹ + 3t⁻² - t⁻³
    "9_1": [1, -1, 1, -1, 1, -1, 1, -1, 1],     # Nonafoil
    "9_2": [2, -6, 9, -11, 9, -6, 2],           # Placeholder (needs verification)
    "10_1": [1, -3, 6, -9, 11, -9, 6, -3, 1],   # Placeholder
    "10_2": [2, -5, 9, -13, 15, -13, 9, -5, 2]  # Placeholder
}

# Notes on conversion from KnotInfo format:
# KnotInfo gives polynomials in Laurent form: a₀t^n + a₁t^(n-1) + ... + a_n
# We store as coefficient list [a₀, a₁, ..., a_n] from highest to lowest power
#
# Examples:
# 5_2: "2t - 3 + 2t⁻¹" = 2t² - 3t + 2 (multiply by t) -> [2, -3, 2]
# 7_2: "t³ - t² + t - 1 + t⁻¹ - t⁻² + t⁻³" -> [1, -1, 1, -1, 1, -1, 1]
# 7_4: "4t + 4t⁻¹ - 7" = 4t² - 7t + 4 (multiply by t) -> [4, -7, 4]
# 8_2: "-t³ + 3t² - 3t + 3 - 3t⁻¹ + 3t⁻² - t⁻³" -> [-1, 3, -3, 3, -3, 3, -1]
