/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

General facts about functions of several complex variables.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.NormedSpace.Extend

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Aqft2.Basic

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

namespace SCV

noncomputable section
open scoped MeasureTheory Complex BigOperators

abbrev ℂn (n : ℕ) := Fin n → ℂ

def Entire {n : ℕ} (f : ℂn n → ℂ) : Prop :=
  AnalyticOn ℂ f Set.univ          --  ⇔  ∀ z, HolomorphicAt ℂ f z

variable (x : ℂ) (f : TestFunctionℂ)

#check x • f        -- Lean should report:  `x • f : TestFunctionℂ`

variable {n : ℕ}
variable (z : ℂn n)               -- coefficients
variable (J : Fin n → TestFunctionℂ)   -- test functions

/-- **Linear combination operator**
    `weightedSumCLM J` takes a coefficient vector `z : ℂⁿ` and returns the test
    function `∑ i, z i • J i`.  Being linear and the domain finite-dimensional,
    it is automatically continuous, so we package it as a `ContinuousLinearMap`. -/

noncomputable
def weightedSumCLM : ℂn n →L[ℂ] TestFunctionℂ := by
  let L : ℂn n →ₗ[ℂ] TestFunctionℂ :=
    { toFun      := fun z ↦ (Finset.univ).sum (fun i ↦ z i • J i),
      map_add'   := by
        intro z₁ z₂
        simp [add_smul, Finset.sum_add_distrib],
      map_smul' := by
        intro c z
        simp [smul_smul, Finset.smul_sum]
    }
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  exact { toLinearMap := L, cont := hcont }
