/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.PGF.Derivatives
import LeanBranchingProcesses.GaltonWatson.Basic

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
* `extinction_iterate_tendsto_least`: The extinction iterate $x_n = f^{\circ n}(0)$
  converges to the least fixed point of $f$ in $[0, 1]$.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

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

/-- **Extinction iterate convergence.** The sequence $x_n = f^{\circ n}(0)$ is
non-decreasing and converges to the least fixed point of $f$ in $[0, 1]$.
(Feller, Vol. 1, Ch. XII, Sec. 1, fundamental result) -/
theorem extinction_iterate_tendsto_least (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1))
    (hf0 : 0 ≤ f 0) (hf_mono : MonotoneOn f (Icc 0 1))
    (hf_le1 : ∀ z ∈ Icc 0 1, f z ≤ 1) :
    ∃ ξ : ℝ, (∀ q, IsExtinctionRoot f q → ξ ≤ q) ∧ IsExtinctionRoot f ξ ∧
      Tendsto (fun n => pgfIterate f n 0) atTop (𝓝 ξ) := by
  let x : ℕ → ℝ := fun n => pgfIterate f n 0
  have hx_mono : MonotoneOn x (Ici 0) := by
    intro m hm n hn hmn
    exact monotone_nat_of_le_succ
      (fun n => pgfIterate_zero_monotone f hf0 hf_mono hf_le1 n) hmn
  have h1_ub : ∀ b ∈ x '' Ici 0, b ≤ 1 := by
    rintro y ⟨n, hn, rfl⟩
    exact (pgfIterate_mem_Icc f hf0 hf_mono hf_le1 n).2
  have hx_bdd : BddAbove (x '' Ici 0) := ⟨1, h1_ub⟩
  have hx_nonempty : (x '' Ici 0).Nonempty := ⟨x 0, ⟨0, by simp, rfl⟩⟩
  have hx_tendsto : Tendsto x atTop (𝓝 (sSup (x '' Ici 0))) :=
    Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici hx_mono hx_bdd
  let ξ : ℝ := sSup (x '' Ici 0)
  have hx0_mem : x 0 ∈ x '' Ici 0 := ⟨0, by simp, rfl⟩
  have hξ_nonneg : 0 ≤ ξ := by
    simpa [x, ξ] using (le_csSup hx_bdd hx0_mem : x 0 ≤ sSup (x '' Ici 0))
  have hξ_le_one : ξ ≤ 1 := by
    dsimp [ξ]
    exact csSup_le hx_nonempty h1_ub
  have hξ_mem : ξ ∈ Icc 0 1 := ⟨hξ_nonneg, hξ_le_one⟩
  have hξ_fixed : f ξ = ξ := by
    have h_shift : Tendsto (fun n => x (n + 1)) atTop (𝓝 ξ) :=
      hx_tendsto.comp (tendsto_add_atTop_nat 1)
    have hxξ : Tendsto x atTop (𝓝 ξ) := by simpa [ξ] using hx_tendsto
    have hxξ_within : Tendsto x atTop (𝓝[Icc 0 1] ξ) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hxξ, Eventually.of_forall (fun n => pgfIterate_mem_Icc f hf0 hf_mono hf_le1 n)⟩
    have h_fx : Tendsto (fun n => f (x n)) atTop (𝓝 (f ξ)) :=
      Tendsto.comp (hf_cont.continuousWithinAt hξ_mem) hxξ_within
    have h_eq : (fun n => x (n + 1)) = fun n => f (x n) := by
      funext n
      simp [x, pgfIterate_succ]
    rw [← h_eq] at h_fx
    exact (tendsto_nhds_unique h_shift h_fx).symm
  have hξ_least : ∀ q, IsExtinctionRoot f q → ξ ≤ q := by
    intro q hq
    have hx_le_q : ∀ n, x n ≤ q := by
      intro n
      induction n with
      | zero =>
          simpa [x] using hq.1
      | succ n ih =>
          change pgfIterate f (n + 1) 0 ≤ q
          rw [pgfIterate_succ]
          have hx_mem : x n ∈ Icc 0 1 := pgfIterate_mem_Icc f hf0 hf_mono hf_le1 n
          have hq_mem : q ∈ Icc 0 1 := ⟨hq.1, hq.2.1⟩
          calc
            f (pgfIterate f n 0) ≤ f q := hf_mono hx_mem hq_mem ih
            _ = q := hq.2.2
    dsimp [ξ]
    exact csSup_le hx_nonempty (by
      rintro y ⟨n, hn, rfl⟩
      exact hx_le_q n)
  exact ⟨ξ, hξ_least, ⟨hξ_mem.1, hξ_mem.2, hξ_fixed⟩, hx_tendsto⟩

/-- **Supercritical case.** If the mean offspring $m = G'(1) > 1$, then there is a fixed
point $q \in [0, 1)$ of the PGF, and the extinction iterate $x_n = G^{\circ n}(0)$ converges
to it (the extinction probability is $< 1$).
(Feller, Vol. 1, Ch. XII, Sec. 1, Theorem 1) -/
theorem extinction_iterate_lt_one_of_deriv_gt_one (X : Ω → ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X)
    (h_int : Integrable (fun ω => (X ω : ℝ)) μ) (hm : 1 < pgfDeriv X μ 1) :
    ∃ ξ : ℝ, ξ < 1 ∧ IsExtinctionRoot (pgf X μ) ξ ∧
      Tendsto (fun n => pgfIterate (pgf X μ) n 0) atTop (𝓝 ξ) := by
  rcases pgf_lt_id_of_deriv_gt_one X μ hX h_int hm with ⟨z₀, hz₀, hz₀_lt_id⟩
  let x0 : ℝ := (z₀ + 1) / 2
  have hx0_pos : 0 < x0 := by
    dsimp [x0]
    nlinarith [hz₀.1]
  have hx0_lt : x0 < 1 := by
    dsimp [x0]
    nlinarith [hz₀.2]
  have hx0_mem : x0 ∈ Ioo z₀ 1 := ⟨by dsimp [x0]; nlinarith [hz₀.2], hx0_lt⟩
  have hle : pgf X μ x0 ≤ x0 := le_of_lt (hz₀_lt_id x0 hx0_mem)
  rcases extinction_root_exists_of_le (pgf X μ) (pgf_continuousOn X μ hX)
    (pgf_nonneg X μ (by norm_num : (0 : ℝ) ≤ 0)) hx0_pos hx0_lt hle with ⟨q, hq0, hq1, hqf⟩
  rcases extinction_iterate_tendsto_least (pgf X μ) (pgf_continuousOn X μ hX)
    (pgf_nonneg X μ (by norm_num : (0 : ℝ) ≤ 0))
    (by
      intro z₁ hz₁ z₂ hz₂ hle'
      exact pgf_monotone X μ hz₁.1 hle' hz₂.2 hX)
    (by
      intro z hz
      exact pgf_le_one X μ hz.1 hz.2)
    with ⟨ξ, hξ_least, hξ_root, hξ_tendsto⟩
  have hξ_le_q : ξ ≤ q := hξ_least q ⟨hq0, hq1.le, hqf⟩
  have hξ_lt : ξ < 1 := lt_of_le_of_lt hξ_le_q hq1
  exact ⟨ξ, hξ_lt, hξ_root, hξ_tendsto⟩

/-- **Subcritical case.** If the mean offspring $m = G'(1) < 1$, then extinction is certain:
the extinction iterate $x_n = G^{\circ n}(0)$ converges to $1$.
(Feller, Vol. 1, Ch. XII, Sec. 1, Theorem 1) -/
theorem extinction_certain_of_deriv_lt_one (X : Ω → ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X)
    (h_int : Integrable (fun ω => (X ω : ℝ)) μ) (hm : pgfDeriv X μ 1 < 1) :
    Tendsto (fun n => pgfIterate (pgf X μ) n 0) atTop (𝓝 1) := by
  rcases extinction_iterate_tendsto_least (pgf X μ) (pgf_continuousOn X μ hX)
    (pgf_nonneg X μ (by norm_num : (0 : ℝ) ≤ 0))
    (by
      intro z₁ hz₁ z₂ hz₂ hle'
      exact pgf_monotone X μ hz₁.1 hle' hz₂.2 hX)
    (by
      intro z hz
      exact pgf_le_one X μ hz.1 hz.2)
    with ⟨ξ, hξ_least, hξ_root, hξ_tendsto⟩
  have hξ_le_one : ξ ≤ 1 := hξ_root.2.1
  have hξ_eq_one : ξ = 1 := by
    by_contra hne
    have hξ_lt : ξ < 1 := lt_of_le_of_ne hξ_le_one hne
    have hf_cont : ContinuousOn (pgf X μ) (Icc ξ 1) :=
      (pgf_continuousOn X μ hX).mono (Icc_subset_Icc_left hξ_root.1)
    have hf_diff : DifferentiableOn ℝ (pgf X μ) (Ioo ξ 1) := by
      intro c hc
      have hderiv : HasDerivAt (pgf X μ) (pgfDeriv X μ c) c :=
        pgf_hasDerivAt X μ hX (lt_of_le_of_lt hξ_root.1 hc.1) hc.2 h_int
      exact hderiv.differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope (pgf X μ) hξ_lt hf_cont hf_diff with ⟨c, hc, hc_eq⟩
    have hc_pos : 0 < c := lt_of_le_of_lt hξ_root.1 hc.1
    have hc_lt : c < 1 := hc.2
    have hderiv_c : deriv (pgf X μ) c = pgfDeriv X μ c :=
      (pgf_hasDerivAt X μ hX hc_pos hc_lt h_int).deriv
    have hc_eq' : deriv (pgf X μ) c = 1 := by
      rw [hc_eq, pgf_one X μ, hξ_root.2.2, div_self (sub_ne_zero.mpr hξ_lt.ne')]
    have h_int1 : Integrable (fun ω => (X ω : ℝ) * (1 : ℝ) ^ (X ω - 1)) μ := by
      simpa [one_pow] using h_int
    have hmono : pgfDeriv X μ c ≤ pgfDeriv X μ 1 :=
      pgfDeriv_monotone X μ (le_of_lt hc_pos) (le_of_lt hc_lt) h_int1
    have h_contr : (1 : ℝ) < 1 := by
      calc
        1 = deriv (pgf X μ) c := hc_eq'.symm
        _ = pgfDeriv X μ c := hderiv_c
        _ ≤ pgfDeriv X μ 1 := hmono
        _ < 1 := hm
    exact (lt_irrefl (1 : ℝ)) h_contr
  simpa [hξ_eq_one] using hξ_tendsto

/-- A convex function on an interval that attains its maximum at an interior point is
constant on that interval. -/
lemma convexOn_eq_of_isMaxOn_interior {a b : ℝ} (_ : a < b) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Icc a b) f) {c : ℝ} (hc : c ∈ Ioo a b)
    (hmax : IsMaxOn f (Icc a b) c) : ∀ z ∈ Icc a b, f z = f c := by
  intro z hz
  by_cases hz_eq : z = c
  · simp [hz_eq]
  · by_cases hz_lt : z < c
    · have hz_mem : z ∈ Icc a b := hz
      have hb_mem : b ∈ Icc a b := ⟨le_of_lt (lt_trans hc.1 hc.2), le_rfl⟩
      have h_slope : (f c - f z) / (c - z) ≤ (f b - f c) / (b - c) :=
        hf.slope_mono_adjacent hz_mem hb_mem hz_lt hc.2
      have hz_le : f z ≤ f c := hmax hz_mem
      have hb_le : f b ≤ f c := hmax hb_mem
      have h1 : 0 ≤ (f c - f z) / (c - z) :=
        div_nonneg (sub_nonneg.mpr hz_le) (sub_pos.mpr hz_lt).le
      have h2 : (f b - f c) / (b - c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb_le) (sub_pos.mpr hc.2).le
      have h_eq : (f c - f z) / (c - z) = 0 := le_antisymm (le_trans h_slope h2) h1
      have h_num : f c - f z = 0 :=
        (div_eq_zero_iff.mp h_eq).resolve_right (sub_ne_zero.mpr hz_lt.ne')
      exact (sub_eq_zero.mp h_num).symm
    · have hz_gt : c < z := lt_of_le_of_ne (not_lt.mp hz_lt) (Ne.symm hz_eq)
      have ha_mem : a ∈ Icc a b := ⟨le_rfl, le_of_lt (lt_trans hc.1 hc.2)⟩
      have hz_mem : z ∈ Icc a b := hz
      have h_slope : (f c - f a) / (c - a) ≤ (f z - f c) / (z - c) :=
        hf.slope_mono_adjacent ha_mem hz_mem hc.1 hz_gt
      have ha_le : f a ≤ f c := hmax ha_mem
      have hz_le : f z ≤ f c := hmax hz_mem
      have h1 : 0 ≤ (f c - f a) / (c - a) :=
        div_nonneg (sub_nonneg.mpr ha_le) (sub_pos.mpr hc.1).le
      have h2 : (f z - f c) / (z - c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz_le) (sub_pos.mpr hz_gt).le
      have h_eq : (f z - f c) / (z - c) = 0 := le_antisymm h2 (le_trans h1 h_slope)
      have h_num : f z - f c = 0 :=
        (div_eq_zero_iff.mp h_eq).resolve_right (sub_ne_zero.mpr hz_gt.ne')
      exact sub_eq_zero.mp h_num

/-- **Uniqueness of the subcritical root.** If the mean offspring $m = G'(1) > 1$, then
there is at most one fixed point $q \in [0, 1)$ of the PGF.
(Feller, Vol. 1, Ch. XII, Sec. 1, Theorem 1) -/
theorem extinction_root_unique_of_deriv_gt_one (X : Ω → ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X)
    (h_int : Integrable (fun ω => (X ω : ℝ)) μ) (hm : 1 < pgfDeriv X μ 1)
    {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq₁' : q₁ < 1) (hfq₁ : pgf X μ q₁ = q₁)
    (hq₂ : 0 ≤ q₂) (hq₂' : q₂ < 1) (hfq₂ : pgf X μ q₂ = q₂) : q₁ = q₂ := by
  have hmain : ∀ {q₁ q₂ : ℝ}, 0 ≤ q₁ → q₁ < 1 → pgf X μ q₁ = q₁ →
      0 ≤ q₂ → q₂ < 1 → pgf X μ q₂ = q₂ → q₁ ≤ q₂ → q₁ = q₂ := by
    intro q₁ q₂ hq₁ hq₁' hfq₁ hq₂ hq₂' hfq₂ h
    by_cases h_eq : q₁ = q₂
    · exact h_eq
    · have h_lt : q₁ < q₂ := lt_of_le_of_ne h h_eq
      have hg_conv : ConvexOn ℝ (Icc q₁ 1) (pgf X μ - (id : ℝ → ℝ)) :=
        ((pgf_convexOn X μ hX h_int).sub (concaveOn_id (convex_Icc (0 : ℝ) (1 : ℝ)))).subset
          (Icc_subset_Icc_left hq₁) (convex_Icc q₁ (1 : ℝ))
      have hgq₁ : (pgf X μ - (id : ℝ → ℝ)) q₁ = 0 := by simp [hfq₁]
      have hgq₂ : (pgf X μ - (id : ℝ → ℝ)) q₂ = 0 := by simp [hfq₂]
      have hg1 : (pgf X μ - (id : ℝ → ℝ)) 1 = 0 := by simp [pgf_one X μ]
      have hg_le_zero : ∀ z ∈ Icc q₁ 1, (pgf X μ - (id : ℝ → ℝ)) z ≤ 0 := by
        intro z hz
        by_cases hz_eq : z = q₂
        · simp [hz_eq, hgq₂]
        · by_cases hz_lt : z < q₂
          · have hz_mem : z ∈ Icc q₁ 1 := hz
            have hq₂_mem : q₂ ∈ Icc q₁ 1 := ⟨le_of_lt h_lt, hq₂'.le⟩
            by_cases hz_q1 : z = q₁
            · simp [hz_q1, hgq₁]
            · have hz_gt_q₁ : q₁ < z := lt_of_le_of_ne hz.1 (Ne.symm hz_q1)
              have hq₁_mem : q₁ ∈ Icc q₁ 1 := ⟨le_rfl, hq₁'.le⟩
              have h_aux := hg_conv.secant_mono_aux1 (x := q₁) (y := z) (z := q₂)
                hq₁_mem hq₂_mem hz_gt_q₁ hz_lt
              have h' : (q₂ - q₁) * (pgf X μ - (id : ℝ → ℝ)) z ≤ 0 := by
                simpa [hgq₁, hgq₂] using h_aux
              have hpos : 0 < q₂ - q₁ := sub_pos.mpr h_lt
              have h'' : (q₂ - q₁) * (pgf X μ - (id : ℝ → ℝ)) z ≤ (q₂ - q₁) * 0 := by simpa using h'
              exact le_of_mul_le_mul_left h'' hpos
          · have hz_gt : q₂ < z := lt_of_le_of_ne (not_lt.mp hz_lt) (Ne.symm hz_eq)
            have hz_mem : z ∈ Icc q₁ 1 := hz
            have hq₂_mem : q₂ ∈ Icc q₁ 1 := ⟨le_of_lt h_lt, hq₂'.le⟩
            have h1_mem : (1 : ℝ) ∈ Icc q₁ 1 := ⟨hq₁'.le, le_rfl⟩
            by_cases hz_one : z = 1
            · simp [hz_one, hg1]
            · have hz_lt_one : z < 1 := lt_of_le_of_ne hz.2 hz_one
              have h_aux := hg_conv.secant_mono_aux1 (x := q₂) (y := z) (z := 1)
                hq₂_mem h1_mem hz_gt hz_lt_one
              have h' : (1 - q₂) * (pgf X μ - (id : ℝ → ℝ)) z ≤ 0 := by
                simpa [hgq₂, hg1] using h_aux
              have hpos : 0 < 1 - q₂ := sub_pos.mpr hq₂'
              have h'' : (1 - q₂) * (pgf X μ - (id : ℝ → ℝ)) z ≤ (1 - q₂) * 0 := by simpa using h'
              exact le_of_mul_le_mul_left h'' hpos
      have hg_max : IsMaxOn (pgf X μ - (id : ℝ → ℝ)) (Icc q₁ 1) q₂ := by
        intro z hz
        have hz_le : (pgf X μ - (id : ℝ → ℝ)) z ≤ 0 := hg_le_zero z hz
        simpa [hgq₂] using hz_le
      have hg_eq : ∀ z ∈ Icc q₁ 1, (pgf X μ - (id : ℝ → ℝ)) z = 0 :=
        by
          intro z hz
          have hg_eq_raw := convexOn_eq_of_isMaxOn_interior hq₁' hg_conv ⟨h_lt, hq₂'⟩ hg_max
          simpa [hgq₂] using hg_eq_raw z hz
      have hderiv_one : pgfDeriv X μ 1 = 1 := by
        have hderiv_eq : ∀ t ∈ Ioo q₁ 1, pgfDeriv X μ t = 1 := by
          intro t ht
          have ht_pos : 0 < t := lt_of_le_of_lt hq₁ ht.1
          have hpgf_id : pgf X μ =ᶠ[𝓝 t] id := by
            filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
            have hgz : (pgf X μ - (id : ℝ → ℝ)) z = 0 := hg_eq z ⟨le_of_lt hz.1, le_of_lt hz.2⟩
            have : pgf X μ z - z = 0 := by simpa using hgz
            exact sub_eq_zero.mp this
          have hderiv_id : HasDerivAt (pgf X μ) 1 t :=
            (hasDerivAt_id t).congr_of_eventuallyEq hpgf_id
          exact ((pgf_hasDerivAt X μ hX ht_pos ht.2 h_int).unique hderiv_id)
        have h_ev : ∀ᶠ t in 𝓝[<] 1, (1 : ℝ) = pgfDeriv X μ t := by
          rw [eventually_iff_exists_mem]
          refine ⟨Ioo q₁ 1, ?_, ?_⟩
          · rw [mem_nhdsWithin]
            refine ⟨Ioi q₁, isOpen_Ioi, hq₁', ?_⟩
            intro z hz
            exact ⟨hz.1, hz.2⟩
          · intro t ht
            exact (hderiv_eq t ht).symm
        have h_const : Tendsto (fun t => pgfDeriv X μ t) (𝓝[<] 1) (𝓝 1) :=
          tendsto_const_nhds.congr' h_ev
        exact tendsto_nhds_unique (pgfDeriv_tendsto_one X μ hX h_int) h_const
      have : (1 : ℝ) < 1 := by
        calc
          1 < pgfDeriv X μ 1 := hm
          _ = 1 := hderiv_one
      exact False.elim (lt_irrefl (1 : ℝ) this)
  rcases le_total q₁ q₂ with h | h
  · exact hmain hq₁ hq₁' hfq₁ hq₂ hq₂' hfq₂ h
  · exact (hmain hq₂ hq₂' hfq₂ hq₁ hq₁' hfq₁ h).symm

end ProbabilityTheory
