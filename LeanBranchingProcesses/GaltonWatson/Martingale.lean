/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib
import LeanBranchingProcesses.PGF.Basic
import LeanBranchingProcesses.GaltonWatson.Basic

/-!
# Galton–Watson Normalized Martingale W_n = Z_n / m^n

This file defines the normalized Galton–Watson sequence $W_n = Z_n / m^n$ and establishes
its basic non-negativity and scaling properties.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1,
  Wiley, 1968, Chapter XII.
* K. B. Athreya, P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I, Sec. 2.

## Main Definitions & Theorems

* `normalizedPopulation Z m n`: The normalized population $W_n = Z_n / m^n$.
* `normalizedPopulation_zero`: $W_0 = Z_0$.
* `normalizedPopulation_nonneg`: $W_n \ge 0$ when $Z_n \ge 0$ and $m > 0$.
-/

set_option linter.unusedVariables true
set_option linter.missingDocs true

open MeasureTheory Filter Topology Set

namespace ProbabilityTheory

/-- The normalized population ratio $W_n = Z_n / m^n$ for a Galton–Watson process
with mean offspring $m > 0$. (Athreya–Ney, Ch. I, Sec. 2) -/
noncomputable def normalizedPopulation (Z : ℕ → ℝ) (m : ℝ) (n : ℕ) : ℝ :=
  Z n / (m ^ n)

@[simp]
theorem normalizedPopulation_zero (Z : ℕ → ℝ) (m : ℝ) :
    normalizedPopulation Z m 0 = Z 0 := by
  dsimp [normalizedPopulation]
  ring

/-- The normalized population ratio $W_n$ is non-negative when $Z_n \ge 0$ and $m > 0$. -/
theorem normalizedPopulation_nonneg (Z : ℕ → ℝ) (m : ℝ) (hm : 0 < m)
    (hZ : ∀ n, 0 ≤ Z n) (n : ℕ) :
    0 ≤ normalizedPopulation Z m n := by
  dsimp [normalizedPopulation]
  exact div_nonneg (hZ n) (pow_nonneg hm.le n)

end ProbabilityTheory
