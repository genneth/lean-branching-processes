/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib

/-!
# Probability Generating Functions (PGFs)

This file defines the probability generating function (PGF) of an `ℕ`-valued random variable
`X : Ω → ℕ` on a measure space `(Ω, μ)`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XI.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I.
* T. E. Harris, *The Theory of Branching Processes*, Springer, 1963.

## Main Definitions

* `ProbabilityTheory.pgf X μ z`: The probability generating function
  `E[z^X] = ∫ ω, z ^ (X ω) ∂μ`.

## Main Results

* `pgf_zero`: `pgf X μ 0 = (μ (X ⁻¹' {0})).toReal`.
* `pgf_one`: `pgf X μ 1 = 1` for a probability measure.
* `pgf_nonneg`: `pgf X μ z ≥ 0` for `z ≥ 0`.
* `pgf_le_one`: `pgf X μ z ≤ 1` for `z ∈ [0, 1]` under a probability measure.
* `pgf_monotone`: `z₁ ≤ z₂ ⇒ pgf X μ z₁ ≤ pgf X μ z₂` for `0 ≤ z₁ ≤ z₂ ≤ 1`.
* `pgf_eq_mgf`: `pgf X μ z = mgf (fun ω => (X ω : ℝ)) μ (Real.log z)` for `z > 0`.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability generating function (PGF) of an `ℕ`-valued random variable `X`
with respect to measure `μ`.
(Feller, Vol. 1, Ch. XI, Eq. 1.1) -/
noncomputable def pgf (X : Ω → ℕ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  ∫ ω, z ^ (X ω) ∂μ

/-- `pgf` evaluated at 0 equals the probability `P(X = 0)`.
(Feller, Vol. 1, Ch. XI, Sec. 1) -/
theorem pgf_zero (X : Ω → ℕ) (μ : Measure Ω) (hX : Measurable X) :
    pgf X μ 0 = (μ (X ⁻¹' {0})).toReal := by
  dsimp [pgf]
  have h_zero : (fun ω => (0 : ℝ) ^ (X ω)) = (X ⁻¹' {0}).indicator (fun _ => 1) := by
    ext ω
    by_cases h : X ω = 0
    · simp [h]
    · simp [h, zero_pow h]
  rw [h_zero, integral_indicator (hX (measurableSet_singleton 0)), integral_const]
  rw [smul_eq_mul, mul_one]
  dsimp [Measure.real]
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- `pgf` evaluated at 1 equals 1 for a probability measure.
(Feller, Vol. 1, Ch. XI, Sec. 1) -/
theorem pgf_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    pgf X μ 1 = 1 := by
  dsimp [pgf]
  simp

/-- `pgf` is non-negative for `z ≥ 0`. -/
theorem pgf_nonneg (X : Ω → ℕ) (μ : Measure Ω) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ pgf X μ z := by
  dsimp [pgf]
  apply integral_nonneg
  intro ω
  exact pow_nonneg hz (X ω)

/-- `pgf` is bounded above by 1 for `z ∈ [0, 1]` under a probability measure. -/
theorem pgf_le_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : pgf X μ z ≤ 1 := by
  dsimp [pgf]
  have h_le : (fun ω => z ^ (X ω)) ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards with ω
    exact pow_le_one₀ hz0 hz1
  have h_int := integral_mono_of_nonneg (ae_of_all μ fun ω => pow_nonneg hz0 (X ω))
      (integrable_const (1 : ℝ)) h_le
  simpa using h_int

/-- `pgf` is non-decreasing in `z` on `[0, 1]` for a probability measure.
(Feller, Vol. 1, Ch. XI, Sec. 1) -/
theorem pgf_monotone (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] {z₁ z₂ : ℝ}
    (hz1 : 0 ≤ z₁) (hle : z₁ ≤ z₂) (hz2 : z₂ ≤ 1) (hX : Measurable X) :
    pgf X μ z₁ ≤ pgf X μ z₂ := by
  dsimp [pgf]
  have h_le : (fun ω => z₁ ^ (X ω)) ≤ᵐ[μ] (fun ω => z₂ ^ (X ω)) := by
    filter_upwards with ω
    exact pow_le_pow_left₀ hz1 hle (X ω)
  have h_int2 : Integrable (fun ω => z₂ ^ (X ω)) μ := by
    apply Integrable.mono (integrable_const (1 : ℝ))
    · exact (measurable_const.pow hX).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (hz1.trans hle), norm_one]
      exact pow_le_one₀ (hz1.trans hle) hz2
  exact integral_mono_of_nonneg (ae_of_all μ fun ω => pow_nonneg hz1 (X ω)) h_int2 h_le

/-- Bridge connecting `pgf` and `mgf`: `pgf X μ z = mgf (fun ω => (X ω : ℝ)) μ (Real.log z)`
for `z > 0`. -/
theorem pgf_eq_mgf (X : Ω → ℕ) (μ : Measure Ω) {z : ℝ} (hz : 0 < z) :
    pgf X μ z = mgf (fun ω => (X ω : ℝ)) μ (Real.log z) := by
  dsimp [pgf, mgf]
  congr 1; ext ω
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hz]

end ProbabilityTheory
