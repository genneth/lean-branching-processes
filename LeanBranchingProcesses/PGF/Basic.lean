/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import Mathlib

/-!
# Probability Generating Functions (PGFs)

This file defines the probability generating function (PGF) of an `ℕ`-valued random variable
on a measure space `(Ω, μ)`.

## Main Definitions

* `ProbabilityTheory.pgf X μ z`: The probability generating function `E[z^X] = ∫ ω, z ^ (X ω) ∂μ`.

## Implementation Notes

The PGF is defined for real `z ∈ [0, 1]` via Bochner integration.
-/

open MeasureTheory Filter Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability generating function (PGF) of an `ℕ`-valued random variable `X`
with respect to measure `μ`. -/
noncomputable def pgf (X : Ω → ℕ) (μ : Measure Ω) (z : ℝ) : ℝ :=
  ∫ ω, z ^ (X ω) ∂μ

/-- `pgf` evaluated at 1 equals the total measure `μ (Set.univ)`. -/
theorem pgf_one (X : Ω → ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    pgf X μ 1 = 1 := by
  dsimp [pgf]
  simp

end ProbabilityTheory
