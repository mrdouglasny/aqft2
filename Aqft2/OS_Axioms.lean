/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace

import Mathlib.Topology.Algebra.Module.LinearMapPiProd

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real

import Aqft2.FunctionalAnalysis
import Aqft2.Basic
import Aqft2.EuclideanS
import Aqft2.DiscreteSymmetry
import Aqft2.SCV
import Aqft2.PositiveTimeTestFunction

/- These are the O-S axioms in the form given in Glimm and Jaffe, Quantum Physics, pp. 89-90 -/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure SCV QFT

noncomputable section
open scoped MeasureTheory Complex BigOperators SchwartzMap

variable (n : ℕ)
variable (J : Fin n → TestFunctionℂ)   -- test functions
variable (z : ℂn n)               -- coefficients
variable (dμ : ProbabilityMeasure FieldSpace)

abbrev weightedSum (z : ℂn n) : TestFunctionℂ := weightedSumCLM (n := n) (J := J) z

#check (weightedSum n J z)

/-- OS0 Analyticity -/

def trial (z : ℂn n) : ℂ := generatingFunctionalℂ dμ (weightedSum n J z)

axiom GJAxiom_OS0 : Entire (trial n J dμ)

/-- The constant‐field bilinear map `B(a)(b) = a * b`. -/
abbrev V := ℂ
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))

variable (f_positive : PositiveTimeTestFunction)

def starred_f' : TestFunctionℂ := star f_positive.val

def S (f : TestFunction) : ℂ := generatingFunctional dμ f

/-- OS3 Reflection Positivity -/

axiom GJAxiom_OS3 : ∀ (F : PositiveTimeTestFunction),
  0 ≤ (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).re ∧
      (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).im = 0
