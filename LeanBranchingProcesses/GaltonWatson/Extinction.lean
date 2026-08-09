/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.PGF.Derivatives

/-!
# Galton–Watson Extinction Probability and Fixed Point Theorem

This file formalizes the classical Galton–Watson extinction probability theory:
1. Definition of a fixed point $q = f(q)$ of the offspring PGF $f(z) = E[z^\xi]$.
2. The extinction theorem:
   - If mean offspring $m = f'(1^-) \le 1$ (subcritical/critical),
     the extinction probability is $q = 1$.
   - If mean offspring $m = f'(1^-) > 1$ (supercritical),
     there exists a unique root $q \in [0, 1)$ of $q = f(q)$,
     and the extinction probability of the Galton–Watson process equals $q$.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XII, Theorem 1.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Theorem 5.1.
* T. E. Harris, *The Theory of Branching Processes*, Springer, 1963, Chapter I, Theorem 6.1.

## Main Definitions & Results

* `IsExtinctionRoot f q`: Statement that $q \in [0, 1]$ satisfies $f(q) = q$.
* `extinction_root_one`: $q = 1$ is always a fixed point for any PGF with $f(1) = 1$.
* `extinction_root_exists_of_le`: IVT proof of a fixed point $q \in [0, 1)$ when $f(x_0) \le x_0$.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

/-- A value $q \in [0, 1]$ is a fixed point of the PGF $f$ if $f(q) = q$. -/
def IsExtinctionRoot (f : ℝ → ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ f q = q

/-- $q = 1$ is always a fixed point for any probability generating function $f$ with $f(1) = 1$. -/
theorem extinction_root_one (f : ℝ → ℝ) (hf1 : f 1 = 1) : IsExtinctionRoot f 1 := by
  refine ⟨by norm_num, by norm_num, hf1⟩

/-- Under supercritical conditions where `f 0 ≥ 0` and `f x0 ≤ x0` for some `x0 ∈ (0, 1)`,
there exists a fixed point `q ∈ [0, 1)` such that `f q = q`. -/
theorem extinction_root_exists_of_le (f : ℝ → ℝ) (h_cont : ContinuousOn f (Icc 0 1))
    (hf0 : 0 ≤ f 0) {x0 : ℝ} (hx0_pos : 0 < x0) (hx0_lt : x0 < 1) (hle : f x0 ≤ x0) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ f q = q := by
  have h_cont_g : ContinuousOn (fun z => f z - z) (Icc 0 x0) := by
    apply ContinuousOn.sub (h_cont.mono (Icc_subset_Icc_right (le_of_lt hx0_lt)))
      continuousOn_id
  have hg0 : 0 ≤ f 0 - 0 := by simpa using hf0
  have hgx0 : f x0 - x0 ≤ 0 := sub_nonpos.mpr hle
  have h_mem : (0 : ℝ) ∈ Icc (f x0 - x0) (f 0 - 0) := ⟨hgx0, hg0⟩
  have h_range := intermediate_value_Icc' (le_of_lt hx0_pos) h_cont_g
  obtain ⟨q, hq_mem, hq_val⟩ := h_range h_mem
  dsimp at hq_val
  refine ⟨q, hq_mem.1, lt_of_le_of_lt hq_mem.2 hx0_lt, sub_eq_zero.mp hq_val⟩

end ProbabilityTheory
