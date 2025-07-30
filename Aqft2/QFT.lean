/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Aqft2.Basic
import Aqft2.OS_Axioms
import Aqft2.FunctionalAnalysis
import Aqft2.EuclideanS
import Aqft2.DiscreteSymmetry
import Aqft2.SCV
import Aqft2.PositiveTimeTestFunction

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Complex.Basic

/-!
# Quantum Field Theory Structure

This file defines the main `QFT` class that encapsulates a quantum field theory
satisfying the Osterwalder-Schrader axioms.

## Main definitions

* `QFT`: Main class encompassing a quantum field theory with all OS axioms

## References

* Glimm and Jaffe, "Quantum Physics: A Functional Integral Point of View"
* Osterwalder and Schrader, "Axioms for Euclidean Green's Functions"
-/

open MeasureTheory NNReal ENNReal Complex Filter Topology
open TopologicalSpace Measure SCV QFT
open scoped MeasureTheory Complex BigOperators Topology

noncomputable section

/-- The main structure for a quantum field theory satisfying OS axioms. -/
class QFT where
  field_measure : ProbabilityMeasure FieldSpace
  /-- OS0: Analyticity -/
  os0_analyticity : ∀ (n : ℕ) (J : Fin n → TestFunctionℂ),
    GJAxiom_OS0 n J field_measure
  /-- OS1: Regularity -/
  os1_regularity : GJAxiom_OS1 field_measure
  /-- OS2: Euclidean invariance -/
  os2_euclidean_invariance : GJAxiom_OS2 field_measure
  /-- OS3: Reflection positivity -/
  os3_reflection_positivity : GJAxiom_OS3 field_measure
  /-- OS4: Ergodicity (time translation invariance) -/
  os4_ergodicity : GJAxiom_OS4 field_measure

end
