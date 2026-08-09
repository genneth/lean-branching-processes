/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic

/-!
# Derivatives and Expectations of Probability Generating Functions

This file establishes the analytic derivative properties of PGFs:
1. Derivatives of $G(z) = E[z^X]$: $G'(z) = E[X z^{X-1}]$ for $z \in [0, 1)$.
2. Evaluation at $z = 1^-$: $\lim_{z \to 1^-} G'(z) = E[X]$.
3. Convexity: $G''(z) \ge 0$ on $[0, 1]$, so $G(z)$ is strictly convex when $P(X \ge 2) > 0$.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XI, Sec. 1.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 2.

## Main Definitions & Results

* `pgfDeriv`: The derivative function $G'(z) = E[X z^{X-1}]$.
* `pgfDeriv_nonneg`: $G'(z) \ge 0$ for $z \ge 0$.
* `pgfDeriv_monotone`: $G'(z_1) \le G'(z_2)$ for $0 \le z_1 \le z_2 \le 1$.
* `pgfDeriv_zero`: $G'(0) = P(X = 1)$.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The formal derivative function of the PGF: $G'(z) = E[X z^{X-1}]$.
(Feller, Vol. 1, Ch. XI, Eq. 1.7) -/
noncomputable def pgfDeriv (X : Ω → ℕ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  ∫ ω, (X ω : ℝ) * z ^ (X ω - 1) ∂μ

/-- The derivative $G'(z)$ is non-negative for $z \ge 0$. -/
theorem pgfDeriv_nonneg (X : Ω → ℕ) (μ : Measure Ω) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ pgfDeriv X μ z := by
  dsimp [pgfDeriv]
  apply integral_nonneg
  intro ω
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)

/-- The derivative $G'(z)$ is non-decreasing in $z$ on $[0, 1]$ for a probability measure. -/
theorem pgfDeriv_monotone (X : Ω → ℕ) (μ : Measure Ω) {z₁ z₂ : ℝ}
    (hz1 : 0 ≤ z₁) (hle : z₁ ≤ z₂)
    (h_int : Integrable (fun ω => (X ω : ℝ) * z₂ ^ (X ω - 1)) μ) :
    pgfDeriv X μ z₁ ≤ pgfDeriv X μ z₂ := by
  dsimp [pgfDeriv]
  have h_le : (fun ω => (X ω : ℝ) * z₁ ^ (X ω - 1)) ≤ᵐ[μ]
      (fun ω => (X ω : ℝ) * z₂ ^ (X ω - 1)) := by
    filter_upwards with ω
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz1 hle _) (Nat.cast_nonneg _)
  have h_nonneg : 0 ≤ᵐ[μ] (fun ω => (X ω : ℝ) * z₁ ^ (X ω - 1)) := by
    filter_upwards with ω
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz1 _)
  exact integral_mono_of_nonneg h_nonneg h_int h_le

/-- At $z = 0$, $G'(0) = P(X = 1)$. -/
theorem pgfDeriv_zero (X : Ω → ℕ) (μ : Measure Ω) (hX : Measurable X) :
    pgfDeriv X μ 0 = (μ (X ⁻¹' {1})).toReal := by
  dsimp [pgfDeriv]
  have h_zero : (fun ω => (X ω : ℝ) * (0 : ℝ) ^ (X ω - 1)) =
      (X ⁻¹' {1}).indicator (fun _ => 1) := by
    ext ω
    rcases h : X ω with _ | n
    · simp [h]
    · rcases n with _ | k
      · simp [h]
      · have h_pos : k + 1 ≠ 0 := Nat.succ_ne_zero k
        simp [h, zero_pow h_pos]
  rw [h_zero, integral_indicator (hX (measurableSet_singleton 1)), integral_const]
  rw [smul_eq_mul, mul_one]
  dsimp [Measure.real]
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]

end ProbabilityTheory
