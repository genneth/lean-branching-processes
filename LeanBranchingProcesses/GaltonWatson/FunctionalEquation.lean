/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.GaltonWatson.Basic
import LeanBranchingProcesses.GaltonWatson.Extinction

/-!
# Galton–Watson Functional Equation: \phi(m s) = f(\phi(s))

This file formalizes the fundamental functional equation (Abel / Schröder type equation)
satisfied by the Laplace transform $\phi(s) = \mathbb{E}[e^{-s W}]$ of the limiting variable
$W = \lim_{n\to\infty} Z_n / m^n$:
$$\phi(m s) = f(\phi(s)), \quad s \ge 0$$

## References

* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 5.
* T. E. Harris, *The Theory of Branching Processes*, Springer, 1963, Chapter I, Sec. 8.
* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 2,
  Wiley, 1971, Chapter XIII, Sec. 10.

## Main Definitions & Theorems

* `IsAbelSolution f m φ`: Property that $\phi(m s) = f(\phi(s))$ for all $s \ge 0$.
* `abel_solution_one`: The constant function $\phi(s) = 1$ is a solution when $f(1) = 1$.
* `abel_solution_extinction`: The constant function $\phi(s) = q$ is a solution when $f(q) = q$.
* `abel_solution_iterate`: Iterated Abel equation $\phi(m^n s) = f^{\circ n}(\phi(s))$.
* `IsNormalizedAbelSolution φ`: Normalization condition $\lim_{s \to 0^+} (1 - \phi(s)) / s = 1$.
* `normalized_abel_solution_limit_zero`: Proves $\lim_{s \to 0^+} \phi(s) = 1$.
* `tendsto_div_pow_atTop_zero`: Proves $s / m^n \to 0$ as $n \to \infty$ for $m > 1$.
* `pgf_iterate_lipschitz`: Lipschitz bound $|f^{\circ n}(x) - f^{\circ n}(y)| \le m^n |x - y|$.
* `abel_solution_unique`: Uniqueness theorem for normalized solutions when $m > 1$.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

/-- A continuous function $\phi : [0, \infty) \to [0, 1]$ is a solution to the
Galton–Watson functional equation with mean $m > 0$ and offspring PGF $f$ if:
$$\phi(m s) = f(\phi(s)) \quad \text{for all } s \ge 0$$
(Athreya–Ney, Ch. I, Sec. 5, Eq. 5.1) -/
def IsAbelSolution (f : ℝ → ℝ) (m : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ s ≥ 0, φ (m * s) = f (φ s)

/-- The constant function $\phi(s) = 1$ is always a solution to the functional equation
when $f(1) = 1$. -/
theorem abel_solution_one (f : ℝ → ℝ) (m : ℝ) (hf1 : f 1 = 1) :
    IsAbelSolution f m (fun _ => 1) := by
  intro s _
  exact hf1.symm

/-- The constant function $\phi(s) = q$ is a solution to the functional equation
for any extinction root $q$ satisfying $f(q) = q$. -/
theorem abel_solution_extinction (f : ℝ → ℝ) (m : ℝ) (q : ℝ) (hq : f q = q) :
    IsAbelSolution f m (fun _ => q) := by
  intro s _
  exact hq.symm

/-- Iterated Abel equation: If $\phi(m s) = f(\phi(s))$,
then $\phi(m^n s) = f^{\circ n}(\phi(s))$. -/
theorem abel_solution_iterate (f : ℝ → ℝ) (m : ℝ) (φ : ℝ → ℝ)
    (h_sol : IsAbelSolution f m φ) (hm : 0 ≤ m) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    φ (m ^ n * s) = pgfIterate f n (φ s) := by
  revert s hs
  induction n with
  | zero =>
    intro s _
    rw [pow_zero, one_mul, pgfIterate_zero]
  | succ n ih =>
    intro s hs
    have hs' : 0 ≤ m * s := mul_nonneg hm hs
    have h1 : m ^ (n + 1) * s = m ^ n * (m * s) := by ring
    rw [h1, ih (m * s) hs', h_sol s hs, pgfIterate_succ]
    dsimp [pgfIterate]
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

/-- A solution $\phi$ is normalized if its asymptotic derivative at $0^+$ is $-1$:
$$\lim_{s \to 0^+} \frac{1 - \phi(s)}{s} = 1$$ -/
def IsNormalizedAbelSolution (φ : ℝ → ℝ) : Prop :=
  Tendsto (fun s => (1 - φ s) / s) (𝓝[>] 0) (𝓝 1)

/-- Normalized Abel solution limit at $0^+$: $\lim_{s \to 0^+} \phi(s) = 1$. -/
theorem normalized_abel_solution_limit_zero (φ : ℝ → ℝ)
    (h_norm : IsNormalizedAbelSolution φ) :
    Tendsto φ (𝓝[>] 0) (𝓝 1) := by
  have h_lim : Tendsto (fun s => 1 - s * ((1 - φ s) / s)) (𝓝[>] 0) (𝓝 (1 - 0 * 1)) := by
    refine tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds |>.mul h_norm)
  have h_sub : (1 - 0 * (1 : ℝ)) = 1 := by ring
  rw [h_sub] at h_lim
  refine h_lim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs_ne : s ≠ 0 := ne_of_gt hs
  rw [mul_div_cancel₀ _ hs_ne, sub_sub_cancel]

/-- The sequence $s / m^n \to 0$ as $n \to \infty$ for any $m > 1$. -/
theorem tendsto_div_pow_atTop_zero (m : ℝ) (hm : 1 < m) (s : ℝ) :
    Tendsto (fun n : ℕ => s / m ^ n) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n : ℕ => (m⁻¹) ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · positivity
    · exact inv_lt_one_iff₀.mpr (Or.inr hm)
  have h_eq : (fun n : ℕ => s / m ^ n) = (fun n : ℕ => s * (m⁻¹) ^ n) := by
    ext n
    rw [div_eq_mul_inv, inv_pow]
  rw [h_eq]
  have h_mul := h_geom.const_mul s
  simpa using h_mul

/-- Lipschitz property of PGF iterates under slope bound $m$:
$$|f^{\circ n}(x) - f^{\circ n}(y)| \le m^n |x - y|$$ -/
theorem pgf_iterate_lipschitz (f : ℝ → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (h_lip : ∀ x y, |f x - f y| ≤ m * |x - y|) (n : ℕ) (x y : ℝ) :
    |pgfIterate f n x - pgfIterate f n y| ≤ m ^ n * |x - y| := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul, pgfIterate_zero, pgfIterate_zero]
  | succ n ih =>
    rw [pgfIterate_succ, pgfIterate_succ, pow_succ', mul_assoc]
    dsimp [pgfIterate]
    have h1 : |f (f^[n] x) - f (f^[n] y)| ≤ m * |f^[n] x - f^[n] y| := h_lip (f^[n] x) (f^[n] y)
    have h2 : m * |f^[n] x - f^[n] y| ≤ m * (m ^ n * |x - y|) := mul_le_mul_of_nonneg_left ih hm
    linarith

/-- Uniqueness of normalized Abel solutions on $(0, \infty)$:
If $\phi_1$ and $\phi_2$ are two normalized solutions to $\phi(m s) = f(\phi(s))$
for supercritical $m > 1$, and $f$ is Lipschitz with constant $m$, then $\phi_1(s) = \phi_2(s)$
for all $s > 0$.
(Athreya–Ney, Ch. I, Sec. 5, Theorem 5.1) -/
theorem abel_solution_unique (f : ℝ → ℝ) (m : ℝ) (hm : 1 < m)
    (h_lip : ∀ x y, |f x - f y| ≤ m * |x - y|)
    (φ₁ φ₂ : ℝ → ℝ)
    (h_sol1 : IsAbelSolution f m φ₁)
    (h_sol2 : IsAbelSolution f m φ₂)
    (h_norm1 : IsNormalizedAbelSolution φ₁)
    (h_norm2 : IsNormalizedAbelSolution φ₂) :
    ∀ s > 0, φ₁ s = φ₂ s := by
  intro s hs_gt
  have hs : 0 ≤ s := hs_gt.le
  have hm_nonneg : 0 ≤ m := (zero_lt_one.trans hm).le
  have hm_ne_zero : m ≠ 0 := (zero_lt_one.trans hm).ne'
  have h_lim_diff : Tendsto (fun n : ℕ => s * |((1 - φ₂ (s / m ^ n)) / (s / m ^ n)) -
      ((1 - φ₁ (s / m ^ n)) / (s / m ^ n))|) atTop (𝓝 (s * |1 - 1|)) := by
    have h_seq : Tendsto (fun n : ℕ => s / m ^ n) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_div_pow_atTop_zero m hm s, ?_⟩
      filter_upwards with n
      exact div_pos hs_gt (pow_pos (zero_lt_one.trans hm) n)
    have h_lim1 := h_norm1.comp h_seq
    have h_lim2 := h_norm2.comp h_seq
    have h_sub := h_lim2.sub h_lim1
    have h_abs := h_sub.abs
    exact h_abs.const_mul s
  have h_lim_zero : s * |(1 : ℝ) - 1| = 0 := by ring
  rw [h_lim_zero] at h_lim_diff
  have h_bound_seq : ∀ n : ℕ, |φ₁ s - φ₂ s| ≤ s * |((1 - φ₂ (s / m ^ n)) / (s / m ^ n)) -
      ((1 - φ₁ (s / m ^ n)) / (s / m ^ n))| := by
    intro n
    have hs_pow_nonneg : 0 ≤ s / m ^ n := div_nonneg hs (pow_nonneg hm_nonneg n)
    have hs_pow_pos : 0 < s / m ^ n := div_pos hs_gt (pow_pos (zero_lt_one.trans hm) n)
    have h_pow_ne : m ^ n ≠ 0 := pow_ne_zero n hm_ne_zero
    have h_eq : m ^ n * (s / m ^ n) = s := mul_div_cancel₀ s h_pow_ne
    have h_iter1 : φ₁ s = pgfIterate f n (φ₁ (s / m ^ n)) := by
      have h_eq2 : φ₁ s = φ₁ (m ^ n * (s / m ^ n)) := by rw [h_eq]
      rw [h_eq2]
      exact abel_solution_iterate f m φ₁ h_sol1 hm_nonneg n (s / m ^ n) hs_pow_nonneg
    have h_iter2 : φ₂ s = pgfIterate f n (φ₂ (s / m ^ n)) := by
      have h_eq2 : φ₂ s = φ₂ (m ^ n * (s / m ^ n)) := by rw [h_eq]
      rw [h_eq2]
      exact abel_solution_iterate f m φ₂ h_sol2 hm_nonneg n (s / m ^ n) hs_pow_nonneg
    rw [h_iter1, h_iter2]
    have h_lip_iter := pgf_iterate_lipschitz f m hm_nonneg h_lip n (φ₁ (s / m ^ n)) (φ₂ (s / m ^ n))
    have h_alg : m ^ n * |φ₁ (s / m ^ n) - φ₂ (s / m ^ n)| =
        s * |((1 - φ₂ (s / m ^ n)) / (s / m ^ n)) - ((1 - φ₁ (s / m ^ n)) / (s / m ^ n))| := by
      rw [← sub_div, abs_div, abs_of_pos hs_pow_pos]
      have h_num : |1 - φ₂ (s / m ^ n) - (1 - φ₁ (s / m ^ n))| =
          |φ₁ (s / m ^ n) - φ₂ (s / m ^ n)| := by
        congr 1
        ring
      rw [h_num]
      field_simp
    linarith [h_lip_iter, h_alg]
  have h_le_zero : |φ₁ s - φ₂ s| ≤ 0 :=
    ge_of_tendsto h_lim_diff (Eventually.of_forall h_bound_seq)
  have h_abs_zero : |φ₁ s - φ₂ s| = 0 := le_antisymm h_le_zero (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp h_abs_zero)

end ProbabilityTheory
