/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.GaltonWatson.Basic

/-!
# Bellman–Harris Age-Dependent Branching Processes: Integral Equation

This file defines the non-linear renewal/integral equation satisfied by the PGF
$F(s, t) = \mathbb{E}[s^{Z(t)}]$ of a Bellman–Harris age-dependent branching process
with lifetime distribution $G(t)$ and offspring PGF $f(s)$:
$$F(s, t) = \int_0^t f(F(s, t-y)) \, dG(y) + s (1 - G(t))$$

## References

* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter IV, Sec. 2.
* R. Bellman, T. E. Harris, *On the theory of age-dependent stochastic branching processes*,
  Proc. Natl. Acad. Sci. USA, 1948.

## Main Definitions & Theorems

* `IsBellmanHarrisSolution f G μ_G F`: Non-linear Bellman-Harris integral equation definition.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

/-- A family of PGFs $F : [0, 1] \times [0, \infty) \to [0, 1]$ is a solution to the
Bellman–Harris integral equation with offspring PGF $f$ and Stieltjes measure $\mu_G$ if:
$$F(s, t) = \int_{[0, t]} f(F(s, t-y)) \, d\mu_G(y) + s (1 - G(t))$$
(Athreya–Ney, Ch. IV, Sec. 2, Eq. 2.1) -/
noncomputable def IsBellmanHarrisSolution (f : ℝ → ℝ) (G : ℝ → ℝ) (μ_G : Measure ℝ)
    (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ s ∈ Icc 0 1, ∀ t ≥ 0,
    F s t = ∫ y in Icc 0 t, f (F s (t - y)) ∂μ_G + s * (1 - G t)

end ProbabilityTheory
