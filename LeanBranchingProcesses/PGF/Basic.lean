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
* `pgf_eq_tsum`: the power-series / PMF expansion
  `pgf X μ z = ∑ₙ P(X = n)·zⁿ` for `0 ≤ z < 1`.
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

/-- **Power-series / PMF expansion.** For `0 ≤ z < 1`, the PGF is the power
series in the probabilities: `pgf X μ z = ∑ₙ P(X = n)·zⁿ`.
(Feller, Vol. 1, Ch. XI, Eq. 1.5) -/
theorem pgf_eq_tsum (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    pgf X μ z = ∑' n : ℕ, (μ (X ⁻¹' {n})).toReal * z ^ n := by
  -- The lintegral is the sum over `n` of the fiber integrals.
  have hlin : (∫⁻ ω, ENNReal.ofReal (z ^ (X ω)) ∂μ) =
      ∑' n, ENNReal.ofReal (z ^ n) * μ (X ⁻¹' {n}) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (z ^ (X ω)) ∂μ)
          = ∫⁻ ω, ∑' n, (X ⁻¹' {n}).indicator (fun _ => ENNReal.ofReal (z ^ n)) ω ∂μ := by
            apply lintegral_congr
            intro ω
            rw [tsum_eq_single (β := ℕ) (L := SummationFilter.unconditional ℕ) (X ω)]
            · simp
            · intro n hn
              by_cases h : X ω = n
              · exact (hn h.symm).elim
              · simp [h]
      _ = ∑' n, ∫⁻ ω, (X ⁻¹' {n}).indicator (fun _ => ENNReal.ofReal (z ^ n)) ω ∂μ := by
            exact MeasureTheory.lintegral_tsum
              (fun n => (Measurable.indicator measurable_const
                (hX (measurableSet_singleton n))).aemeasurable)
      _ = ∑' n, ENNReal.ofReal (z ^ n) * μ (X ⁻¹' {n}) := by
            congr 1
            funext n
            rw [MeasureTheory.lintegral_indicator (hX (measurableSet_singleton n)),
              MeasureTheory.setLIntegral_const]
  -- The integrand is nonnegative and integrable (bounded by 1).
  have hnn : 0 ≤ᵐ[μ] fun ω => z ^ (X ω) := by
    filter_upwards with ω
    exact pow_nonneg hz0 (X ω)
  have hint : Integrable (fun ω => z ^ (X ω)) μ := by
    refine Integrable.mono (integrable_const (1 : ℝ)) ?_ ?_
    · exact (measurable_const.pow hX).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz0 (X ω)), norm_one]
      exact (pow_le_one₀ hz0 (le_of_lt hz1) : z ^ (X ω) ≤ 1)
  -- Left side: the lintegral is `ENNReal.ofReal (pgf X μ z)`.
  have hleft : (∫⁻ ω, ENNReal.ofReal (z ^ (X ω)) ∂μ) = ENNReal.ofReal (pgf X μ z) := by
    dsimp [pgf]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  -- Right side: convert the ENNReal tsum to a real tsum.
  have hright : (∑' n, ENNReal.ofReal (z ^ n) * μ (X ⁻¹' {n})).toReal =
      ∑' n, (μ (X ⁻¹' {n})).toReal * z ^ n := by
    rw [ENNReal.tsum_toReal_eq]
    · congr 1
      funext n
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hz0 n)]
      ring
    · intro n
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
  -- Combine.
  have htoReal := congr_arg ENNReal.toReal hlin
  rw [hleft, hright] at htoReal
  have hpgf_nn : 0 ≤ pgf X μ z := pgf_nonneg X μ hz0
  rwa [ENNReal.toReal_ofReal hpgf_nn] at htoReal

end ProbabilityTheory
