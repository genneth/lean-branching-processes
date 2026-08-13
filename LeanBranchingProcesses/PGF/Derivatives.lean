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
4. Comparison with the identity: $G(z) \ge z$ when $E[X] \le 1$, and $G(z) < z$ on a
   neighbourhood of $1^-$ when $E[X] > 1$.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XI, Sec. 1.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 2.

## Main Definitions & Results

* `pgfDeriv`: The derivative function $G'(z) = E[X z^{X-1}]$.
* `pgfDeriv_nonneg`: $G'(z) \ge 0$ for $z \ge 0$.
* `pgfDeriv_monotone`: $G'(z_1) \le G'(z_2)$ for $0 \le z_1 \le z_2 \le 1$.
* `pgfDeriv_zero`: $G'(0) = P(X = 1)$.
* `pgf_hasDerivAt`: $G$ is differentiable at $z \in (0, 1)$ with derivative $G'(z)$.
* `pgf_continuousOn`: $G$ is continuous on $[0, 1]$.
* `pgf_convexOn`: $G$ is convex on $[0, 1]$.
* `pgfDeriv_tendsto_one`: $\lim_{z \to 1^-} G'(z) = G'(1) = E[X]$.
* `pgf_ge_id_of_deriv_le_one`: if $E[X] \le 1$ then $G(z) \ge z$ on $[0, 1]$.
* `pgf_lt_id_of_deriv_gt_one`: if $E[X] > 1$ then $G(z) < z$ on a left-neighbourhood of $1$.
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

/-- At $z = 1$, the formal derivative equals the mean: $G'(1) = E[X]$.
(Feller, Vol. 1, Ch. XI, Sec. 1, Theorem 2, (1.9)) -/
theorem pgfDeriv_one (X : Ω → ℕ) (μ : Measure Ω) :
    pgfDeriv X μ 1 = ∫ ω, (X ω : ℝ) ∂μ := by
  dsimp [pgfDeriv]
  apply integral_congr_ae
  filter_upwards with ω
  rw [one_pow, mul_one]

/-- The formal $k$-th derivative of the PGF:
$G^{(k)}(z) = E[X(X-1)\cdots(X-k+1)\,z^{X-k}]$.
(Feller, Vol. 1, Ch. XI, Sec. 1, Theorem 3, (1.10)-(1.12)) -/
noncomputable def pgfDerivIter (k : ℕ) (X : Ω → ℕ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  ∫ ω, ((X ω).descFactorial k : ℝ) * z ^ (X ω - k) ∂μ

/-- The formal $k$-th derivative at $z = 1$ is the $k$-th factorial moment:
$G^{(k)}(1) = E[X(X-1)\cdots(X-k+1)]$.
(Feller, Vol. 1, Ch. XI, Sec. 1, Theorem 3) -/
theorem pgfDerivIter_one (k : ℕ) (X : Ω → ℕ) (μ : Measure Ω) :
    pgfDerivIter k X μ 1 = ∫ ω, ((X ω).descFactorial k : ℝ) ∂μ := by
  dsimp [pgfDerivIter]
  apply integral_congr_ae
  filter_upwards with ω
  rw [one_pow, mul_one]

/-- The first formal derivative agrees with `pgfDeriv`. -/
theorem pgfDerivIter_one_eq_pgfDeriv (X : Ω → ℕ) (μ : Measure Ω) (z : ℝ) :
    pgfDerivIter 1 X μ z = pgfDeriv X μ z := by
  dsimp [pgfDerivIter, pgfDeriv]
  apply integral_congr_ae
  filter_upwards with ω
  simp

/-- **Differentiating under the integral.** The PGF is differentiable on
$(0, 1)$ with derivative $G'(z) = E[X z^{X-1}]$, assuming $E[X] < ∞$.
(Feller, Vol. 1, Ch. XI, Sec. 1, Theorem 2, (1.7)) -/
theorem pgf_hasDerivAt (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h_int : Integrable (fun ω => (X ω : ℝ)) μ) :
    HasDerivAt (pgf X μ) (pgfDeriv X μ z) z := by
  have hs : (Ioo 0 1 : Set ℝ) ∈ 𝓝 z := isOpen_Ioo.mem_nhds (by exact ⟨hz0, hz1⟩)
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun ω => x ^ (X ω)) μ := by
    filter_upwards with x
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact ((measurable_from_top : Measurable (fun n : ℕ => x ^ n)).comp hX).aemeasurable
  have hF_meas_z : AEStronglyMeasurable (fun ω => z ^ (X ω)) μ := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact ((measurable_from_top : Measurable (fun n : ℕ => z ^ n)).comp hX).aemeasurable
  have hF_int : Integrable (fun ω => z ^ (X ω)) μ := by
    refine ⟨hF_meas_z, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt hz0) _)]
    exact pow_le_one₀ (le_of_lt hz0) (le_of_lt hz1)
  have hF'_meas : AEStronglyMeasurable (fun ω => (X ω : ℝ) * z ^ (X ω - 1)) μ := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    have h1 : Measurable (fun ω => (X ω : ℝ)) :=
      (measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp hX
    have h2 : Measurable (fun ω => z ^ (X ω - 1)) := by
      exact (measurable_from_top : Measurable (fun n : ℕ => z ^ n)).comp
        ((measurable_from_top : Measurable (fun n : ℕ => n - 1)).comp hX)
    exact (h1.mul h2).aemeasurable
  have h_bound : ∀ᵐ ω ∂μ, ∀ x ∈ Ioo 0 1, ‖(X ω : ℝ) * x ^ (X ω - 1)‖ ≤ (X ω : ℝ) := by
    filter_upwards with ω
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx1 : x ≤ 1 := le_of_lt hx.2
    have hpow1 : x ^ (X ω - 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have hpow_nn : 0 ≤ x ^ (X ω - 1) := pow_nonneg hx0 _
    have hX_nn : 0 ≤ (X ω : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hX_nn, abs_of_nonneg hpow_nn]
    simpa using mul_le_mul_of_nonneg_left hpow1 hX_nn
  have h_diff : ∀ᵐ ω ∂μ, ∀ x ∈ Ioo 0 1,
      HasDerivAt (fun x => x ^ (X ω)) ((X ω : ℝ) * x ^ (X ω - 1)) x := by
    filter_upwards with ω
    intro x hx
    exact hasDerivAt_pow (X ω) x
  rcases (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x ω => x ^ (X ω)) (F' := fun x ω => (X ω : ℝ) * x ^ (X ω - 1))
    (bound := fun ω => (X ω : ℝ)) hs hF_meas hF_int hF'_meas h_bound h_int h_diff) with ⟨_, h⟩
  have hfun : pgf X μ = fun n : ℝ => ∫ (a : Ω), n ^ X a ∂μ := by
    funext n
    rfl
  have hderiv : pgfDeriv X μ z = ∫ (a : Ω), (X a : ℝ) * z ^ (X a - 1) ∂μ := by
    rfl
  rw [hfun, hderiv]
  exact h

/-- The PGF is continuous on the closed interval $[0, 1]$.
(Feller, Vol. 1, Ch. XI, Sec. 1) -/
theorem pgf_continuousOn (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) : ContinuousOn (pgf X μ) (Icc 0 1) := by
  intro z₀ hz₀
  have hF_meas : ∀ᶠ z in 𝓝[Icc 0 1] z₀, AEStronglyMeasurable (fun ω => z ^ (X ω)) μ := by
    filter_upwards with z
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact ((measurable_from_top : Measurable (fun n : ℕ => z ^ n)).comp hX).aemeasurable
  have h_bound : ∀ᶠ z in 𝓝[Icc 0 1] z₀, ∀ᵐ ω ∂μ, ‖z ^ (X ω)‖ ≤ (1 : ℝ) := by
    rw [eventually_iff_exists_mem]
    refine ⟨Icc 0 1, self_mem_nhdsWithin, ?_⟩
    intro z hz
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz.1 _)]
    exact pow_le_one₀ hz.1 hz.2
  have h_lim : ∀ᵐ ω ∂μ, Tendsto (fun z => z ^ (X ω)) (𝓝[Icc 0 1] z₀) (𝓝 (z₀ ^ (X ω))) := by
    filter_upwards with ω
    exact (continuousAt_pow z₀ (X ω)).tendsto.mono_left nhdsWithin_le_nhds
  have h_tendsto := tendsto_integral_filter_of_dominated_convergence
    (F := fun z ω => z ^ (X ω)) (f := fun ω => z₀ ^ (X ω)) (bound := fun _ : Ω => (1 : ℝ))
    (l := 𝓝[Icc 0 1] z₀) hF_meas h_bound (integrable_const (1 : ℝ)) h_lim
  change Tendsto (pgf X μ) (𝓝[Icc 0 1] z₀) (𝓝 (pgf X μ z₀))
  exact h_tendsto

/-- The PGF is convex on $[0, 1]$.
(Feller, Vol. 1, Ch. XI, Sec. 1) -/
theorem pgf_convexOn (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (h_int : Integrable (fun ω => (X ω : ℝ)) μ) :
    ConvexOn ℝ (Icc 0 1) (pgf X μ) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Icc (0 : ℝ) (1 : ℝ)) (pgf_continuousOn X μ hX) ?_ ?_
  · rw [interior_Icc]
    intro z hz
    exact (pgf_hasDerivAt X μ hX hz.1 hz.2 h_int).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro z₁ hz₁ z₂ hz₂ hle
    have hd₁ : deriv (pgf X μ) z₁ = pgfDeriv X μ z₁ :=
      (pgf_hasDerivAt X μ hX hz₁.1 hz₁.2 h_int).deriv
    have hd₂ : deriv (pgf X μ) z₂ = pgfDeriv X μ z₂ :=
      (pgf_hasDerivAt X μ hX hz₂.1 hz₂.2 h_int).deriv
    rw [hd₁, hd₂]
    have h_int₂ : Integrable (fun ω => (X ω : ℝ) * z₂ ^ (X ω - 1)) μ := by
      have h_meas : AEStronglyMeasurable (fun ω => (X ω : ℝ) * z₂ ^ (X ω - 1)) μ := by
        rw [aestronglyMeasurable_iff_aemeasurable]
        have h1 : Measurable (fun ω => (X ω : ℝ)) :=
          (measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp hX
        have h2 : Measurable (fun ω => z₂ ^ (X ω - 1)) :=
          (measurable_from_top : Measurable (fun n : ℕ => z₂ ^ n)).comp
            ((measurable_from_top : Measurable (fun n : ℕ => n - 1)).comp hX)
        exact (h1.mul h2).aemeasurable
      have hb : ∀ᵐ ω ∂μ, ‖(X ω : ℝ) * z₂ ^ (X ω - 1)‖ ≤ ‖(X ω : ℝ)‖ := by
        filter_upwards with ω
        have hz0 : 0 ≤ z₂ := le_of_lt hz₂.1
        have hz1 : z₂ ≤ 1 := le_of_lt hz₂.2
        have hpow1 : z₂ ^ (X ω - 1) ≤ 1 := pow_le_one₀ hz0 hz1
        have hpow_nn : 0 ≤ z₂ ^ (X ω - 1) := pow_nonneg hz0 _
        have hX_nn : 0 ≤ (X ω : ℝ) := Nat.cast_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hX_nn, abs_of_nonneg hpow_nn,
            Real.norm_eq_abs, abs_of_nonneg hX_nn]
        simpa using mul_le_mul_of_nonneg_left hpow1 hX_nn
      exact h_int.mono h_meas hb
    exact pgfDeriv_monotone X μ (le_of_lt hz₁.1) hle h_int₂

/-- The derivative of the PGF is continuous at $z = 1$ from the left:
$\lim_{z \to 1^-} G'(z) = E[X] = G'(1)$.
(Feller, Vol. 1, Ch. XI, Sec. 1, Theorem 2) -/
theorem pgfDeriv_tendsto_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (h_int : Integrable (fun ω => (X ω : ℝ)) μ) :
    Tendsto (fun z => pgfDeriv X μ z) (𝓝[<] 1) (𝓝 (pgfDeriv X μ 1)) := by
  have hz_mem : ∀ᶠ z in 𝓝[<] 1, (0 : ℝ) < z ∧ z < 1 := by
    rw [eventually_iff_exists_mem]
    refine ⟨Ioo 0 1, ?_, ?_⟩
    · rw [mem_nhdsWithin]
      refine ⟨Ioi (0 : ℝ), isOpen_Ioi, (by norm_num : (1 : ℝ) ∈ Ioi (0 : ℝ)), ?_⟩
      intro z hz
      exact ⟨hz.1, hz.2⟩
    · intro z hz
      exact hz
  have hF_meas : ∀ᶠ z in 𝓝[<] 1, AEStronglyMeasurable (fun ω => (X ω : ℝ) * z ^ (X ω - 1)) μ := by
    filter_upwards with z
    rw [aestronglyMeasurable_iff_aemeasurable]
    have h1 : Measurable (fun ω => (X ω : ℝ)) :=
      (measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp hX
    have h2 : Measurable (fun ω => z ^ (X ω - 1)) :=
      (measurable_from_top : Measurable (fun n : ℕ => z ^ n)).comp
        ((measurable_from_top : Measurable (fun n : ℕ => n - 1)).comp hX)
    exact (h1.mul h2).aemeasurable
  have h_bound : ∀ᶠ z in 𝓝[<] 1, ∀ᵐ ω ∂μ, ‖(X ω : ℝ) * z ^ (X ω - 1)‖ ≤ (X ω : ℝ) := by
    filter_upwards [hz_mem] with z hz
    filter_upwards with ω
    have hz0 : 0 ≤ z := le_of_lt hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hpow1 : z ^ (X ω - 1) ≤ 1 := pow_le_one₀ hz0 hz1
    have hpow_nn : 0 ≤ z ^ (X ω - 1) := pow_nonneg hz0 _
    have hX_nn : 0 ≤ (X ω : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hX_nn, abs_of_nonneg hpow_nn]
    simpa using mul_le_mul_of_nonneg_left hpow1 hX_nn
  have h_lim : ∀ᵐ ω ∂μ, Tendsto (fun z => (X ω : ℝ) * z ^ (X ω - 1)) (𝓝[<] 1) (𝓝 ((X ω : ℝ))) := by
    filter_upwards with ω
    have hz : Tendsto (fun z : ℝ => z ^ (X ω - 1)) (𝓝[<] 1) (𝓝 (1 ^ (X ω - 1))) :=
      (continuousAt_pow 1 (X ω - 1)).tendsto.mono_left nhdsWithin_le_nhds
    have hz' : Tendsto (fun z : ℝ => z ^ (X ω - 1)) (𝓝[<] 1) (𝓝 (1 : ℝ)) := by
      simpa using hz
    have hc : Tendsto (fun _ : ℝ => (X ω : ℝ)) (𝓝[<] 1) (𝓝 ((X ω : ℝ))) := tendsto_const_nhds
    simpa [one_pow, mul_one] using hc.mul hz'
  have h_tendsto := tendsto_integral_filter_of_dominated_convergence
    (F := fun z ω => (X ω : ℝ) * z ^ (X ω - 1)) (f := fun ω => (X ω : ℝ))
    (bound := fun ω => (X ω : ℝ)) (l := 𝓝[<] 1) hF_meas h_bound h_int h_lim
  simpa [pgfDeriv, pgfDeriv_one] using h_tendsto

/-- If the mean offspring $m = G'(1) \le 1$, then $G(z) \ge z$ for all $z \in [0, 1]$.
(Feller, Vol. 1, Ch. XII, Sec. 1) -/
theorem pgf_ge_id_of_deriv_le_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (h_int : Integrable (fun ω => (X ω : ℝ)) μ)
    (hm : pgfDeriv X μ 1 ≤ 1) : ∀ z ∈ Icc 0 1, z ≤ pgf X μ z := by
  intro z hz
  have hg_antitone : AntitoneOn (fun t => pgf X μ t - t) (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) (1 : ℝ))
      ((pgf_continuousOn X μ hX).sub continuousOn_id) ?_ ?_
    · rw [interior_Icc]
      intro t ht
      exact ((pgf_hasDerivAt X μ hX ht.1 ht.2 h_int).differentiableAt.sub
        differentiableAt_id).differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have hd : deriv (fun t => pgf X μ t - t) t = pgfDeriv X μ t - 1 := by
        have hf : DifferentiableAt ℝ (pgf X μ) t :=
          (pgf_hasDerivAt X μ hX ht.1 ht.2 h_int).differentiableAt
        change deriv (pgf X μ - id) t = pgfDeriv X μ t - 1
        rw [deriv_sub hf differentiableAt_id]
        rw [(pgf_hasDerivAt X μ hX ht.1 ht.2 h_int).deriv, deriv_id]
      rw [hd]
      have h_int1 : Integrable (fun ω => (X ω : ℝ) * (1 : ℝ) ^ (X ω - 1)) μ := by
        simpa [one_pow] using h_int
      have hmono : pgfDeriv X μ t ≤ pgfDeriv X μ 1 :=
        pgfDeriv_monotone X μ (le_of_lt ht.1) (le_of_lt ht.2) h_int1
      exact sub_nonpos.mpr (le_trans hmono hm)
  have h1_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hz_le_one : z ≤ 1 := hz.2
  have hg : (fun t => pgf X μ t - t) 1 ≤ (fun t => pgf X μ t - t) z :=
    hg_antitone hz h1_mem hz_le_one
  have hg1 : (fun t => pgf X μ t - t) 1 = 0 := by simp [pgf_one X μ]
  have : 0 ≤ pgf X μ z - z := by simpa [hg1] using hg
  exact sub_nonneg.mp this

/-- If the mean offspring $m = G'(1) > 1$, then $G(z) < z$ for all $z$ in a
left-neighbourhood of $1$.
(Feller, Vol. 1, Ch. XII, Sec. 1) -/
theorem pgf_lt_id_of_deriv_gt_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (h_int : Integrable (fun ω => (X ω : ℝ)) μ)
    (hm : 1 < pgfDeriv X μ 1) :
    ∃ z₀ ∈ Ioo 0 1, ∀ z ∈ Ioo z₀ 1, pgf X μ z < z := by
  have h_ev : ∀ᶠ z in 𝓝[<] 1, 1 < pgfDeriv X μ z :=
    (pgfDeriv_tendsto_one X μ hX h_int).eventually (isOpen_Ioi.mem_nhds hm)
  rcases eventually_iff_exists_mem.mp h_ev with ⟨s, hs_mem, hs⟩
  rw [mem_nhdsWithin] at hs_mem
  rcases hs_mem with ⟨u, hu_open, hu_mem, hu_sub⟩
  have hu_nhds : u ∈ 𝓝 1 := hu_open.mem_nhds hu_mem
  rcases (mem_nhds_iff_exists_Ioo_subset.mp hu_nhds) with ⟨l, u', hl, hu_sub'⟩
  let z₀ : ℝ := max l (1 / 2)
  have hz₀_lt : z₀ < 1 := max_lt hl.1 (by norm_num)
  have hz₀_pos : 0 < z₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right l (1 / 2))
  have hz₀_le : l ≤ z₀ := by dsimp [z₀]; exact le_max_left l (1 / 2)
  refine ⟨z₀, ⟨hz₀_pos, hz₀_lt⟩, ?_⟩
  intro z hz
  have hz_s : z ∈ s := by
    apply hu_sub
    constructor
    · apply hu_sub'
      exact ⟨lt_of_le_of_lt hz₀_le hz.1, hz.2.trans hl.2⟩
    · exact hz.2
  have hderiv : 1 < pgfDeriv X μ z := hs z hz_s
  have hg_strict : StrictMonoOn (fun t => pgf X μ t - t) (Icc z₀ 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc z₀ (1 : ℝ)) ?_ ?_
    · exact ((pgf_continuousOn X μ hX).sub continuousOn_id).mono (Icc_subset_Icc_left hz₀_pos.le)
    · intro t ht
      have ht' : t ∈ Ioo z₀ 1 := by simpa [interior_Icc] using ht
      have ht_s : t ∈ s := by
        apply hu_sub
        constructor
        · apply hu_sub'
          exact ⟨lt_of_le_of_lt hz₀_le ht'.1, ht'.2.trans hl.2⟩
        · exact ht'.2
      have hderiv_t : 1 < pgfDeriv X μ t := hs t ht_s
      have ht_pos : 0 < t := lt_trans hz₀_pos ht'.1
      have hd : deriv (fun t => pgf X μ t - t) t = pgfDeriv X μ t - 1 := by
        have hf : DifferentiableAt ℝ (pgf X μ) t :=
          (pgf_hasDerivAt X μ hX ht_pos ht'.2 h_int).differentiableAt
        change deriv (pgf X μ - id) t = pgfDeriv X μ t - 1
        rw [deriv_sub hf differentiableAt_id]
        rw [(pgf_hasDerivAt X μ hX ht_pos ht'.2 h_int).deriv, deriv_id]
      rw [hd]
      exact sub_pos.mpr hderiv_t
  have hz_mem : z ∈ Icc z₀ 1 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have h1_mem : (1 : ℝ) ∈ Icc z₀ 1 := ⟨hz₀_lt.le, le_rfl⟩
  have hg_lt : (fun t => pgf X μ t - t) z < (fun t => pgf X μ t - t) 1 :=
    hg_strict hz_mem h1_mem hz.2
  have hg1 : (fun t => pgf X μ t - t) 1 = 0 := by simp [pgf_one X μ]
  have : pgf X μ z - z < 0 := by simpa [hg1] using hg_lt
  exact sub_lt_zero.mp this

end ProbabilityTheory
