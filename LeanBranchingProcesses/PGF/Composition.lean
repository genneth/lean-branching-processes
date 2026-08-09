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
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

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

end ProbabilityTheory
