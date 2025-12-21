"""
Visualization Utilities for Rational Knot Theory

This module provides visualization tools for knot configurations,
matrices, and reduction processes.
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from typing import List, Optional
from rational_knot_theory import RationalKnot, RationalCrossing


def plot_interlacing_matrix(knot: RationalKnot, title: Optional[str] = None, 
                            save_path: Optional[str] = None):
    """
    Plot the interlacing matrix M(K) as a heatmap.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to visualize
    title : Optional[str]
        Custom title for the plot
    save_path : Optional[str]
        Path to save the figure
    """
    M = knot.get_interlacing_matrix()
    n = knot.n_crossings
    
    if n == 0:
        print("Cannot plot matrix for empty knot")
        return
    
    fig, ax = plt.subplots(figsize=(8, 6))
    
    im = ax.imshow(M, cmap='Blues', interpolation='nearest', vmin=0, vmax=1)
    
    # Set ticks
    ax.set_xticks(range(n))
    ax.set_yticks(range(n))
    ax.set_xticklabels([f"C{i+1}" for i in range(n)])
    ax.set_yticklabels([f"C{i+1}" for i in range(n)])
    
    # Add values to cells
    for i in range(n):
        for j in range(n):
            text = ax.text(j, i, str(M[i, j]),
                          ha="center", va="center", color="black", fontsize=12)
    
    # Labels and title
    ax.set_xlabel("Crossing", fontsize=12)
    ax.set_ylabel("Crossing", fontsize=12)
    
    if title is None:
        title = f"Interlacing Matrix M(K)\nKnot: {knot}"
    ax.set_title(title, fontsize=14, fontweight='bold')
    
    # Colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Interlaced', rotation=270, labelpad=20)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved to {save_path}")
    
    plt.show()


def plot_signed_matrix(knot: RationalKnot, title: Optional[str] = None,
                       save_path: Optional[str] = None):
    """
    Plot the signed matrix S(K) as a heatmap.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to visualize
    title : Optional[str]
        Custom title for the plot
    save_path : Optional[str]
        Path to save the figure
    """
    S = knot.get_signed_matrix()
    n = knot.n_crossings
    
    if n == 0:
        print("Cannot plot matrix for empty knot")
        return
    
    fig, ax = plt.subplots(figsize=(8, 6))
    
    # Use diverging colormap for signed values
    vmax = max(abs(S.min()), abs(S.max()), 1)
    im = ax.imshow(S, cmap='RdBu_r', interpolation='nearest', 
                   vmin=-vmax, vmax=vmax)
    
    # Set ticks
    ax.set_xticks(range(n))
    ax.set_yticks(range(n))
    ax.set_xticklabels([f"C{i+1}" for i in range(n)])
    ax.set_yticklabels([f"C{i+1}" for i in range(n)])
    
    # Add values to cells
    for i in range(n):
        for j in range(n):
            color = "white" if abs(S[i, j]) > vmax/2 else "black"
            text = ax.text(j, i, str(S[i, j]),
                          ha="center", va="center", color=color, fontsize=12)
    
    # Labels and title
    ax.set_xlabel("Crossing", fontsize=12)
    ax.set_ylabel("Crossing", fontsize=12)
    
    if title is None:
        title = f"Signed Matrix S(K)\nKnot: {knot}"
    ax.set_title(title, fontsize=14, fontweight='bold')
    
    # Colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('η·σ_i·σ_j', rotation=270, labelpad=20)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved to {save_path}")
    
    plt.show()


def plot_knot_diagram_simple(knot: RationalKnot, title: Optional[str] = None,
                             save_path: Optional[str] = None):
    """
    Plot a simple diagram showing crossing intervals.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to visualize
    title : Optional[str]
        Custom title for the plot
    save_path : Optional[str]
        Path to save the figure
    """
    n = knot.n_crossings
    
    if n == 0:
        print("Cannot plot empty knot")
        return
    
    fig, ax = plt.subplots(figsize=(12, 6))
    
    # Draw horizontal line representing positions 1 to 2n
    max_pos = 2 * n
    ax.plot([0, max_pos + 1], [0, 0], 'k-', linewidth=2)
    
    # Mark positions
    for i in range(1, max_pos + 1):
        ax.plot(i, 0, 'ko', markersize=8)
        ax.text(i, -0.3, str(i), ha='center', fontsize=10)
    
    # Draw arcs for each crossing
    colors = plt.cm.tab10(np.linspace(0, 1, n))
    
    for i, crossing in enumerate(knot.crossings):
        a, b = crossing.interval
        
        # Draw arc
        center = (a + b) / 2
        radius = (b - a) / 2
        
        # Create arc
        theta = np.linspace(0, np.pi, 100)
        x = center + radius * np.cos(theta)
        y = 0.5 + radius * np.sin(theta) * 0.3
        
        ax.plot(x, y, color=colors[i], linewidth=2, 
               label=f"C{i+1}: {crossing}")
        
        # Mark over/under
        ax.plot(crossing.over, 0, 'o', color=colors[i], 
               markersize=12, markeredgecolor='black', markeredgewidth=2)
        ax.plot(crossing.under, 0, 's', color=colors[i], 
               markersize=10, markeredgecolor='black', markeredgewidth=2)
    
    ax.set_xlim(-0.5, max_pos + 1.5)
    ax.set_ylim(-1, 2)
    ax.set_aspect('equal')
    ax.axis('off')
    
    if title is None:
        title = f"Knot Diagram: {knot}"
    ax.set_title(title, fontsize=14, fontweight='bold', pad=20)
    
    # Legend
    ax.legend(loc='upper right', fontsize=9)
    
    # Add legend for markers
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='gray',
               markersize=10, label='Over position', markeredgecolor='black'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='gray',
               markersize=8, label='Under position', markeredgecolor='black')
    ]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=9)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved to {save_path}")
    
    plt.show()


def export_to_latex(knot: RationalKnot) -> str:
    """
    Export knot configuration to LaTeX format.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to export
    
    Returns
    -------
    str
        LaTeX representation
    """
    if knot.n_crossings == 0:
        return r"$K = \{\}$"
    
    crossings_str = ", ".join([
        f"\\frac{{{c.over}}}{{{c.under}}}"
        for c in knot.crossings
    ])
    
    latex = f"$K = \\{{{crossings_str}\\}}$"
    
    return latex


def print_reduction_steps(knot: RationalKnot):
    """
    Print step-by-step reduction process with detailed information.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to reduce
    """
    from reidemeister_moves import (
        detect_r1_removable, detect_r2_removable,
        apply_r1_removal, apply_r2_removal
    )
    
    print("=" * 70)
    print("  STEP-BY-STEP REDUCTION PROCESS")
    print("=" * 70)
    
    current = knot
    step = 0
    
    print(f"\nInitial knot: {current}")
    print(f"Degree: {current.degree}")
    print(f"R(K) = {current.rational_product()}")
    
    while True:
        print("\n" + "-" * 70)
        
        # Check for R1
        r1_candidates = detect_r1_removable(current)
        
        if r1_candidates:
            step += 1
            idx = min(r1_candidates, key=lambda i: current.crossings[i].a)
            
            print(f"\nStep {step}: R1- removal")
            print(f"  Removing crossing {idx}: {current.crossings[idx]}")
            print(f"  Reason: |o-u| = 1 and no interlacing")
            
            current = apply_r1_removal(current, idx)
            
            print(f"  Result: {current}")
            print(f"  Degree: {current.degree}")
            continue
        
        # Check for R2
        r2_candidates = detect_r2_removable(current)
        
        if r2_candidates:
            step += 1
            pair = min(r2_candidates,
                      key=lambda p: current.crossings[p[0]].a + current.crossings[p[1]].a)
            
            print(f"\nStep {step}: R2- removal")
            print(f"  Removing pair {pair}: {current.crossings[pair[0]]}, {current.crossings[pair[1]]}")
            print(f"  Reason: |o_a-o_b|=1, |u_a-u_b|=1, interlaced only with each other")
            
            current = apply_r2_removal(current, pair)
            
            print(f"  Result: {current}")
            print(f"  Degree: {current.degree}")
            continue
        
        # No more reductions
        break
    
    print("\n" + "=" * 70)
    print("  REDUCTION COMPLETE")
    print("=" * 70)
    print(f"\nFinal irreducible form: {current}")
    print(f"Degree: {current.degree}")
    print(f"R(K) = {current.rational_product()}")
    
    if step == 0:
        print("\nKnot was already irreducible!")


if __name__ == "__main__":
    # Example usage
    from rational_knot_theory import RationalKnot
    
    print("Visualization Examples\n")
    
    # Trefoil
    trefoil = RationalKnot.from_pairs([(1, 4), (5, 2), (3, 6)])
    print("Trefoil knot:")
    print(export_to_latex(trefoil))
    print()
    
    # Uncomment to show plots (requires matplotlib display)
    # plot_interlacing_matrix(trefoil)
    # plot_signed_matrix(trefoil)
    # plot_knot_diagram_simple(trefoil)
