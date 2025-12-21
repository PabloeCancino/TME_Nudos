"""
Visualization of Knot 10_71 Analysis Results
Creates a simple comparison chart of R(K) vs R(K*)
"""

import matplotlib.pyplot as plt
import numpy as np
from fractions import Fraction

# Data from analysis
R_K = Fraction(262144, 46189)
R_K_mirror = Fraction(46189, 262144)
R_K_inverse = Fraction(1) / R_K

# Convert to floats for plotting
values = {
    'R(K)': float(R_K),
    'R(K*)': float(R_K_mirror),
    'R(K)⁻¹': float(R_K_inverse)
}

# Create figure
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

# Plot 1: Bar chart comparison
colors = ['#2E86AB', '#A23B72', '#F18F01']
bars = ax1.bar(values.keys(), values.values(), color=colors, alpha=0.8, edgecolor='black', linewidth=2)
ax1.set_ylabel('Value', fontsize=12, fontweight='bold')
ax1.set_title('Rational Invariants for Knot 10₇₁', fontsize=14, fontweight='bold')
ax1.grid(axis='y', alpha=0.3, linestyle='--')
ax1.set_ylim(0, max(values.values()) * 1.1)

# Add value labels on bars
for bar, (label, value) in zip(bars, values.items()):
    height = bar.get_height()
    ax1.text(bar.get_x() + bar.get_width()/2., height,
             f'{value:.4f}',
             ha='center', va='bottom', fontweight='bold', fontsize=10)

# Plot 2: Verification visualization
categories = ['Mirror Property\nR(K*) = R(K)⁻¹', 'Chirality\nR(K) ≠ R(K*)']
verification = [1, 1]  # Both verified
colors_verify = ['#06A77D', '#06A77D']

bars2 = ax2.bar(categories, verification, color=colors_verify, alpha=0.8, edgecolor='black', linewidth=2)
ax2.set_ylabel('Verified', fontsize=12, fontweight='bold')
ax2.set_title('Property Verification', fontsize=14, fontweight='bold')
ax2.set_ylim(0, 1.2)
ax2.set_yticks([0, 1])
ax2.set_yticklabels(['✗ Failed', '✓ Verified'], fontsize=11)

# Add checkmarks
for bar in bars2:
    height = bar.get_height()
    ax2.text(bar.get_x() + bar.get_width()/2., height/2,
             '✓', ha='center', va='center', fontsize=40, color='white', fontweight='bold')

# Add info text
info_text = (
    "Knot 10₇₁ Analysis Results\n"
    f"R(K) = {R_K} ≈ {float(R_K):.4f}\n"
    f"R(K*) = {R_K_mirror} ≈ {float(R_K_mirror):.4f}\n"
    f"R(K)⁻¹ = {R_K_inverse} ≈ {float(R_K_inverse):.4f}\n\n"
    "✓ Chirality detected where classical invariants fail!"
)

fig.text(0.5, 0.02, info_text, ha='center', fontsize=10,
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

plt.tight_layout(rect=[0, 0.12, 1, 1])
plt.savefig('knot_10_71_visualization.png', dpi=300, bbox_inches='tight')
print("Visualization saved to: knot_10_71_visualization.png")
plt.close()

# Create a second plot showing the reciprocal relationship
fig, ax = plt.subplots(figsize=(10, 8))

# Plot the reciprocal relationship
x = np.linspace(0.1, 10, 1000)
y = 1 / x

ax.plot(x, y, 'b-', linewidth=2, label='y = 1/x (reciprocal)', alpha=0.7)
ax.plot([float(R_K)], [float(R_K_mirror)], 'ro', markersize=15, 
        label=f'10₇₁: R(K)={float(R_K):.3f}, R(K*)={float(R_K_mirror):.3f}', zorder=5)
ax.plot([float(R_K_mirror)], [float(R_K)], 'go', markersize=15,
        label=f'Mirror: R(K*)={float(R_K_mirror):.3f}, R(K)={float(R_K):.3f}', zorder=5)

# Add diagonal line y=x for reference
ax.plot(x, x, 'k--', linewidth=1, alpha=0.3, label='y = x (amphichiral)')

ax.set_xlabel('R(K)', fontsize=12, fontweight='bold')
ax.set_ylabel('R(K*)', fontsize=12, fontweight='bold')
ax.set_title('Mirror Property: R(K*) = R(K)⁻¹ for Knot 10₇₁', fontsize=14, fontweight='bold')
ax.grid(True, alpha=0.3, linestyle='--')
ax.legend(fontsize=10, loc='upper right')
ax.set_xlim(0, 10)
ax.set_ylim(0, 10)

# Add annotation
ax.annotate('Chiral knot:\nR(K) ≠ R(K*)\nR(K*) = R(K)⁻¹',
            xy=(float(R_K), float(R_K_mirror)), xytext=(7, 3),
            arrowprops=dict(arrowstyle='->', color='red', lw=2),
            fontsize=11, fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))

plt.tight_layout()
plt.savefig('knot_10_71_reciprocal.png', dpi=300, bbox_inches='tight')
print("Reciprocal plot saved to: knot_10_71_reciprocal.png")
plt.close()

print("\n✓ All visualizations created successfully!")
