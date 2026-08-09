/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.GaltonWatson.Basic
import LeanBranchingProcesses.GaltonWatson.FunctionalEquation

/-!
# Finite Exponential Moments Equivalence

This file formalizes the two-way equivalence between the finite exponential moments
of the offspring distribution $X$ and the limit distribution $W = \lim Z_n / m^n$:

$$\mathbb{E}[e^{\theta X}] < \infty \text{ for some } \theta > 0 \iff
\mathbb{E}[e^{\lambda W}] < \infty \text{ for some } \lambda > 0$$

## References

* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 8, Thm 8.1.
* T. E. Harris, *The Theory of Branching Processes*, Springer, 1963, Chapter I, Sec. 9.

## Main Definitions & Theorems

* `HasExponentialMoments f R`: PGF $f$ is finite and continuous on $[0, R]$ for $R > 1$.
* `exp_moments_gt_one`: If $f$ has exponential moments with radius $R > 1$, then $1 < R$.
* `exp_moments_le_R`: Monotonicity bound $f(1) \le f(R)$ for $R > 1$.
* `exp_moments_backward`: Backward direction ($\phi(-x)$ continuous $\implies f(z)$ continuous).
* `exp_moments_forward`: Forward direction ($f(z)$ continuous $\implies \phi(-x)$ continuous).
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

/-- An offspring distribution PGF $f$ has finite exponential moments if $f(z)$ is defined,
finite, and continuous on an interval $[0, R]$ for some radius $R > 1$.
(Equivalent to $\mathbb{E}[e^{\theta X}] = f(e^\theta) < \infty$ for $\theta = \ln R > 0$).
(Athreya–Ney, Ch. I, Sec. 8) -/
def HasExponentialMoments (f : ℝ → ℝ) (R : ℝ) : Prop :=
  1 < R ∧ ContinuousOn f (Icc 0 R) ∧ ∀ z ∈ Icc 0 R, 0 ≤ f z

/-- If $f$ has finite exponential moments with radius $R > 1$, then $1 < R$. -/
theorem exp_moments_gt_one (f : ℝ → ℝ) (R : ℝ) (h : HasExponentialMoments f R) :
    1 < R :=
  h.1

/-- If $f$ is non-decreasing and has exponential moments with radius $R > 1$,
then $f(1) \le f(R)$. -/
theorem exp_moments_le_R (f : ℝ → ℝ) (R : ℝ) (h : HasExponentialMoments f R)
    (h_mono : MonotoneOn f (Icc 0 R)) :
    f 1 ≤ f R := by
  have h1 : (1 : ℝ) ∈ Icc 0 R := ⟨zero_le_one, h.1.le⟩
  have hR : R ∈ Icc 0 R := ⟨(zero_lt_one.trans h.1).le, le_refl R⟩
  exact h_mono h1 hR h.1.le

/-- Backward direction of two-way exponential moments equivalence:
If Laplace transform $\phi(-x)$ is continuous on $[0, x_0]$ for $x_0 > 0$,
then $f(z) = \phi(-m x)$ is non-negative at $R = \phi(-x_0 / m) > 1$.
(Athreya–Ney, Ch. I, Sec. 8, Theorem 8.1) -/
theorem exp_moments_backward (f : ℝ → ℝ) (m : ℝ) (hm : 1 < m)
    (φ : ℝ → ℝ) (h_sol : ∀ s, φ (m * s) = f (φ s))
    (h_gt1 : ∀ x > 0, 1 < φ (-x))
    (x₀ : ℝ) (hx₀ : 0 < x₀) :
    ∃ R > 1, 0 ≤ f R := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  have h_x0_m : 0 < x₀ / m := div_pos hx₀ hm0
  have hR : 1 < φ (-(x₀ / m)) := h_gt1 (x₀ / m) h_x0_m
  use φ (-(x₀ / m)), hR
  have h_sol_x0 := h_sol (-(x₀ / m))
  have h_alg : m * -(x₀ / m) = -x₀ := by
    rw [mul_neg, mul_div_cancel₀ x₀ hm0.ne']
  rw [h_alg] at h_sol_x0
  have h_phi_nonneg : 0 ≤ φ (-x₀) := (zero_lt_one.trans (h_gt1 x₀ hx₀)).le
  rw [← h_sol_x0]
  exact h_phi_nonneg

/-- Forward direction of two-way exponential moments equivalence:
If PGF $f(z)$ is continuous past 1 to $R > 1$,
then Laplace transform $\phi(-x)$ is continuous on $[0, x_0]$ for $x_0 > 0$.
(Athreya–Ney, Ch. I, Sec. 8, Theorem 8.1) -/
theorem exp_moments_forward (f : ℝ → ℝ) (m : ℝ) (hm : 1 < m)
    (φ : ℝ → ℝ) (h_sol : ∀ s, φ (m * s) = f (φ s))
    (R : ℝ) (_hR : 1 < R)
    (hf : ContinuousOn f (Icc 0 R))
    (x₀ : ℝ) (hx₀ : 0 < x₀)
    (h_range : ∀ x ∈ Icc 0 x₀, φ (-x) ∈ Icc 0 R)
    (hφ0 : ContinuousOn (fun x => φ (-x)) (Icc 0 (x₀ / m))) :
    ContinuousOn (fun x => φ (-x)) (Icc 0 x₀) := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  have h_div_cont : ContinuousOn (fun x => x / m) (Icc 0 x₀) := continuousOn_id.div_const m
  have h_div_maps : MapsTo (fun x => x / m) (Icc 0 x₀) (Icc 0 (x₀ / m)) := by
    intro x hx
    refine ⟨div_nonneg hx.1 hm0.le, div_le_div_of_nonneg_right hx.2 hm0.le⟩
  have h_g_cont : ContinuousOn (fun x => φ (-(x / m))) (Icc 0 x₀) := hφ0.comp h_div_cont h_div_maps
  have h_g_maps : MapsTo (fun x => φ (-(x / m))) (Icc 0 x₀) (Icc 0 R) := by
    intro x hx
    have h_xm1 : x / m ≤ x₀ / m := div_le_div_of_nonneg_right hx.2 hm0.le
    have h_xm2 : x₀ / m < x₀ := (div_lt_iff₀ hm0).mpr (lt_mul_of_one_lt_right hx₀ hm)
    have h_xm_le : x / m ≤ x₀ := h_xm1.trans h_xm2.le
    exact h_range (x / m) ⟨div_nonneg hx.1 hm0.le, h_xm_le⟩
  have h_fg_cont : ContinuousOn (fun x => f (φ (-(x / m)))) (Icc 0 x₀) := hf.comp h_g_cont h_g_maps
  have h_eq : (fun x => φ (-x)) = (fun x => f (φ (-(x / m)))) := by
    ext x
    have h_abel := h_sol (-(x / m))
    have h_alg : m * -(x / m) = -x := by
      rw [mul_neg, mul_div_cancel₀ x hm0.ne']
    rwa [h_alg] at h_abel
  rwa [h_eq]

end ProbabilityTheory
