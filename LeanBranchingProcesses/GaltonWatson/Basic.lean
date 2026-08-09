/-
Copyright (c) 2026 Gen Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gen Zhang
-/
import LeanBranchingProcesses.PGF.Basic

/-!
# Galton–Watson Branching Processes

This file defines discrete-time Galton–Watson branching processes.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- Scaffold for Galton–Watson process definition. -/
structure GaltonWatsonProcess (Ω : Type*) [MeasurableSpace Ω] where
  offspringDist : Measure ℕ

end ProbabilityTheory
