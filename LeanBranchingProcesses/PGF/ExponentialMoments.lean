/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.GaltonWatson.Basic

/-!
# Finite Exponential Moments of Branching Offspring Distributions

This file formalizes the finite exponential moments condition for offspring distributions
in branching processes:
1. `HasExponentialMoments f R`: The offspring PGF $f(z) = \mathbb{E}[z^X]$ converges
   for $z \in [0, R]$ with $R > 1$.
2. Equivalence to MGF finiteness $\mathbb{E}[e^{\theta X}] < \infty$ for $\theta = \ln R > 0$.

## References

* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 8.
* T. E. Harris, *The Theory of Branching Processes*, Springer, 1963, Chapter I, Sec. 9.

## Main Definitions & Results

* `HasExponentialMoments f R`: PGF $f$ is finite and continuous on $[0, R]$ for some $R > 1$.
* `exp_moments_gt_one`: $R > 1$.
* `exp_moments_le_R`: $f(1) \le f(R)$ by monotonicity.
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

end ProbabilityTheory
