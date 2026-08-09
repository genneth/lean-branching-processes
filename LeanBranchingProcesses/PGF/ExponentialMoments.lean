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
* `exp_moments_iff_mgf_finite`: Two-way equivalence between offspring PGF radius $R > 1$
  and limit Laplace transform analytical extension $\phi(-x) < \infty$.
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

/-- **Two-Way Equivalence for Exponential Moments**:
The offspring PGF $f(z)$ extends past $z=1$ to $R > 1$ (i.e. $X$ has finite exponential
moments) if and only if the Abel solution Laplace transform $\phi(-x) = \mathbb{E}[e^{x W}]$
extends past $x=0$ to $x_0 > 0$.

- Forward ($\implies$): $f(R) < \infty \implies \mathbb{E}[e^{\lambda W}] < \infty$.
- Backward ($\impliedby$): By $\phi(-m x) = f(\phi(-x))$, if $\phi(-x_0) < \infty$,
  then $f(z) < \infty$ at $z = \phi(-x_0 / m) > 1$.
(Athreya–Ney, Ch. I, Sec. 8, Theorem 8.1) -/
theorem exp_moments_iff_mgf_finite (f : ℝ → ℝ) (m : ℝ) (hm : 1 < m)
    (φ : ℝ → ℝ) (h_sol : IsAbelSolution f m φ) :
    (∃ R > 1, ContinuousOn f (Icc 0 R)) ↔
    (∃ x₀ > 0, ContinuousOn (fun x => φ (-x)) (Icc 0 x₀)) := sorry

end ProbabilityTheory
