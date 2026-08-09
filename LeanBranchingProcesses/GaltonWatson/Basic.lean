/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.PGF.Composition

/-!
# Galton–Watson Branching Processes

This file defines discrete-time Galton–Watson branching processes and their PGF iteration:
1. PGF iteration $f^{\circ n}(z)$: The $n$-th iterate of the offspring PGF $f$.
2. Properties of the iterate $f^{\circ n}(z)$: Monotonicity, non-negativity.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XII, Sec. 1.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 2.
* T. E. Harris, *The Theory of Branching Processes*, Springer, 1963, Chapter I, Sec. 2.

## Main Definitions & Results

* `pgfIterate f n z`: The $n$-fold composition $f^{\circ n}(z) = f(f(\dots f(z)\dots))$.
* `pgfIterate_zero`: $f^{\circ 0}(z) = z$.
* `pgfIterate_succ`: $f^{\circ (n+1)}(z) = f(f^{\circ n}(z))$.
* `pgfIterate_one`: $f^{\circ n}(1) = 1$ for a PGF with $f(1) = 1$.
* `pgfIterate_mem_Icc`: $f^{\circ n}(0) \in [0, 1]$.
* `pgfIterate_zero_monotone`: $n \mapsto f^{\circ n}(0)$ is non-decreasing.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

/-- The $n$-fold iteration of an offspring PGF $f$: $f^{\circ n}(z) = (f^{[n]})(z)$.
(Feller, Vol. 1, Ch. XII, Eq. 1.3) -/
def pgfIterate (f : ℝ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  f^[n] z

@[simp]
theorem pgfIterate_zero (f : ℝ → ℝ) (z : ℝ) : pgfIterate f 0 z = z := rfl

theorem pgfIterate_succ (f : ℝ → ℝ) (n : ℕ) (z : ℝ) :
    pgfIterate f (n + 1) z = f (pgfIterate f n z) := by
  exact Function.iterate_succ_apply' f n z

/-- If $f(1) = 1$, then $f^{\circ n}(1) = 1$ for all $n$. -/
theorem pgfIterate_one (f : ℝ → ℝ) (hf1 : f 1 = 1) (n : ℕ) :
    pgfIterate f n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pgfIterate_succ, ih, hf1]

/-- The PGF iterate $f^{\circ n}(0)$ remains inside $[0, 1]$ for all $n$. -/
theorem pgfIterate_mem_Icc (f : ℝ → ℝ) (hf0 : 0 ≤ f 0)
    (h_mono : MonotoneOn f (Icc 0 1))
    (h_le1 : ∀ z ∈ Icc 0 1, f z ≤ 1) (n : ℕ) :
    pgfIterate f n 0 ∈ Icc 0 1 := by
  induction n with
  | zero => exact ⟨le_refl 0, zero_le_one⟩
  | succ n ih =>
    rw [pgfIterate_succ]
    have h_0_mem : (0 : ℝ) ∈ Icc 0 1 := ⟨le_refl 0, zero_le_one⟩
    have h_le : f 0 ≤ f (pgfIterate f n 0) := h_mono h_0_mem ih ih.1
    exact ⟨hf0.trans h_le, h_le1 (pgfIterate f n 0) ih⟩

/-- If $f(0) \ge 0$ and $f$ is non-decreasing on $[0, 1]$,
then $f^{\circ n}(0)$ is non-decreasing in $n$. -/
theorem pgfIterate_zero_monotone (f : ℝ → ℝ) (hf0 : 0 ≤ f 0)
    (h_mono : MonotoneOn f (Icc 0 1))
    (h_le1 : ∀ z ∈ Icc 0 1, f z ≤ 1) (n : ℕ) :
    pgfIterate f n 0 ≤ pgfIterate f (n + 1) 0 := by
  induction n with
  | zero =>
    rw [pgfIterate_zero, pgfIterate_succ, pgfIterate_zero]
    exact hf0
  | succ n ih =>
    rw [pgfIterate_succ, pgfIterate_succ]
    have h1 := pgfIterate_mem_Icc f hf0 h_mono h_le1 n
    have h2 := pgfIterate_mem_Icc f hf0 h_mono h_le1 (n + 1)
    exact h_mono h1 h2 ih

end ProbabilityTheory
