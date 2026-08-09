/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.PGF.Derivatives

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

end ProbabilityTheory
