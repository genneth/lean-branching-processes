/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic

/-!
# Multiplication and Composition of Probability Generating Functions

This file establishes the fundamental algebraic properties of PGFs under:
1. Addition of independent random variables: `G_{X+Y}(z) = G_X(z) * G_Y(z)`.
2. Composition for compound random sums (Galton–Watson branching steps):
   If `S_N = ∑ i in Finset.range N, X i` where `X i` are i.i.d. and independent of `N`,
   then `G_{S_N}(z) = G_N(G_X(z))`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XI, Theorem 1 & Theorem 2.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 2.

## Main Results

* `pgf_add_indep`: The PGF of the sum of independent random variables is the product of their PGFs.
* `pgf_sum_range`: The PGF of a finite sum of mutually independent variables
  is the product of their PGFs.
* `pgf_sum_iid`: The PGF of a sum of `n` i.i.d. variables is the `n`-th power of the common PGF.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The PGF of the sum of two independent `ℕ`-valued random variables `X` and `Y`
is the product of their respective PGFs: `G_{X+Y}(z) = G_X(z) * G_Y(z)`.
(Feller, Vol. 1, Ch. XI, Sec. 2, Theorem 1) -/
theorem pgf_add_indep (X Y : Ω → ℕ) (μ : Measure Ω)
    (h_indep : IndepFun X Y μ) (hX : Measurable X) (hY : Measurable Y) (z : ℝ) :
    pgf (X + Y) μ z = pgf X μ z * pgf Y μ z := by
  dsimp [pgf]
  have h_pow : (fun ω => z ^ (X ω + Y ω)) = (fun ω => z ^ (X ω)) * (fun ω => z ^ (Y ω)) := by
    ext ω
    exact pow_add z (X ω) (Y ω)
  rw [h_pow]
  have h_meas_f : Measurable (fun n : ℕ => z ^ n) := measurable_from_top
  have h_indep' := h_indep.comp h_meas_f h_meas_f
  exact h_indep'.integral_mul_eq_mul_integral
    (h_meas_f.comp hX).aestronglyMeasurable
    (h_meas_f.comp hY).aestronglyMeasurable

/-- A finite sum of measurable `ℕ`-valued functions is measurable. -/
lemma pgf_sum_measurable (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp_rw [Finset.sum_range_succ]
      exact Measurable.add ih (hX n)

/-- **PGF of a finite sum of independent variables.** If `X i` are mutually
independent, then the PGF of `∑ i in Finset.range n, X i` is the product of
the PGFs. (Feller, Vol. 1, Ch. XI, Sec. 2, Theorem) -/
theorem pgf_sum_range (X : ℕ → Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ) (hX : ∀ i, Measurable (X i)) (n : ℕ) (z : ℝ) :
    pgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ z =
      ∏ i ∈ Finset.range n, pgf (X i) μ z := by
  induction n with
  | zero =>
      simp [pgf]
  | succ n ih =>
      simp_rw [Finset.sum_range_succ, Finset.prod_range_succ]
      -- The partial sum is independent of `X n`.
      have h_indep_sum : IndepFun (∑ i ∈ Finset.range n, X i) (X n) μ :=
        iIndepFun.indepFun_sum_range_succ h_indep hX n
      have hfinal : IndepFun (fun ω => ∑ i ∈ Finset.range n, X i ω) (X n) μ := by
        rw [Finset.sum_fn] at h_indep_sum
        exact h_indep_sum
      change pgf ((fun ω => ∑ i ∈ Finset.range n, X i ω) + X n) μ z =
        (∏ i ∈ Finset.range n, pgf (X i) μ z) * pgf (X n) μ z
      rw [pgf_add_indep (fun ω => ∑ i ∈ Finset.range n, X i ω) (X n) μ hfinal
        (pgf_sum_measurable X hX n) (hX n) z]
      rw [ih]

/-- **PGF of a sum of i.i.d. variables.** If `X i` are mutually independent
and identically distributed, then the PGF of `∑ i in Finset.range n, X i` is
`(pgf X₀)ⁿ`. (Feller, Vol. 1, Ch. XI, Sec. 2) -/
theorem pgf_sum_iid (X : ℕ → Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ) (hX : ∀ i, Measurable (X i))
    (h_id : ∀ i z, pgf (X i) μ z = pgf (X 0) μ z) (n : ℕ) (z : ℝ) :
    pgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ z = (pgf (X 0) μ z) ^ n := by
  rw [pgf_sum_range X μ h_indep hX n z]
  calc
    ∏ i ∈ Finset.range n, pgf (X i) μ z = ∏ i ∈ Finset.range n, pgf (X 0) μ z := by
      exact Finset.prod_congr rfl (fun i hi => h_id i z)
    _ = (pgf (X 0) μ z) ^ n := by
      rw [Finset.prod_const, Finset.card_range]

end ProbabilityTheory
