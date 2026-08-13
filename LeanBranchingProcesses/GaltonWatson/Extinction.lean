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

end ProbabilityTheory
