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
import Mathlib.Algebra.Star.Basic
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

import Mathlib.LinearAlgebra.TensorAlgebra.Basic

import Aqft2.FunctionalAnalysis
import Aqft2.Basic
import Aqft2.EuclideanS
import Aqft2.DiscreteSymmetry
import Aqft2.SCV

/- These are the O-S axioms in the form given in Glimm and Jaffe, Quantum Physics, pp. 89-90 -/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure SCV QFT

noncomputable section
open scoped MeasureTheory Complex BigOperators

/- OS0 Analyticity -/

variable (n : ℕ)
variable (J : Fin n → TestFunctionℂ)   -- test functions
variable (z : ℂn n)               -- coefficients
variable (dμ : ProbabilityMeasure FieldSpace)

#check weightedSumCLM (n := n) (J := J) z

abbrev weightedSum (z : ℂn n) : TestFunctionℂ := weightedSumCLM (n := n) (J := J) z

#check (weightedSum n J z)

def trial (z : ℂn n) : ℂ := generatingFunctionalℂ dμ (weightedSum n J z)

axiom GJAxiom_OS0 : Entire (trial n J dμ)

/-- OS3 Reflection Positivity -/

def HasPositiveTime (x : SpaceTime) : Prop := getTimeComponent x > 0
def positiveTimeSet : Set SpaceTime := {x | HasPositiveTime x}

open Function

-- Ensure this set is actually open.
lemma is_open_positiveTimeSet : IsOpen positiveTimeSet :=
  isOpen_lt continuous_const (continuous_apply (0 : Fin STDimension))

def PositiveTimeTestFunctions.submodule : Submodule ℂ TestFunctionℂ where
  carrier := { f :  TestFunctionℂ | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    suffices h : tsupport (0 : TestFunctionℂ) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem'  := fun hf hg => (tsupport_add).trans (Set.union_subset hf hg)
  smul_mem' := fun c f hf => by
    refine (tsupport_smul_subset_right (fun _ : SpaceTime => c) f).trans hf

abbrev PositiveTimeTestFunction : Type := PositiveTimeTestFunctions.submodule
instance : AddCommMonoid PositiveTimeTestFunction := by infer_instance
instance : AddCommGroup PositiveTimeTestFunction := by infer_instance

def EuclideanAlgebra : Type :=
  TensorAlgebra ℂ PositiveTimeTestFunction

variable (f : TestFunctionℂ)

-- Helper lemma: starRingEnd ℂ commutes through derivatives and preserves norms
lemma starRingEnd_iteratedFDeriv_norm_eq (g : TestFunctionℂ) (n : ℕ) (x : SpaceTime) :
  ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (g x)) x‖ = ‖iteratedFDeriv ℝ n g x‖ := by
  -- This is a fundamental property: since starRingEnd ℂ = Complex.conjLIE is a
  -- ℝ-linear isometric equivalence ℂ → ℂ, it commutes through derivatives and preserves norms.
  -- The proof follows from LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
  -- but requires careful handling of the ℝ vs ℂ field structures.
  sorry

-- Define a helper function for the star operation
noncomputable def starTestFunction (f : TestFunctionℂ) : TestFunctionℂ :=
  -- Apply time reflection then complex conjugation pointwise
  let f_reflected := compTimeReflection f
  -- Apply complex conjugation to each value
  ⟨fun x => starRingEnd ℂ (f_reflected x),
   -- Smoothness: starRingEnd is smooth and compTimeReflection gives smooth functions
   by
     -- Apply the continuous linear map contDiff lemma
     apply ContDiff.comp
     · -- starRingEnd ℂ is smooth
       exact ContinuousLinearMap.contDiff (Complex.conjLIE.toContinuousLinearMap)
     · -- f_reflected is smooth
       exact f_reflected.smooth ⊤,
   -- Decay
   fun k n => by
     -- Use the bound from f_reflected and the fact that starRingEnd is an isometry
     obtain ⟨C, hC⟩ := f_reflected.decay' k n
     use C
     intro x
     -- Since starRingEnd ℂ is complex conjugation, which is an isometry,
     -- it preserves the norms of derivatives. This follows from standard properties
     -- of linear isometries and the chain rule for derivatives.
     have : ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖ = ‖iteratedFDeriv ℝ n f_reflected x‖ :=
       starRingEnd_iteratedFDeriv_norm_eq f_reflected n x
     rw [this]
     exact hC x⟩

noncomputable instance : Star TestFunctionℂ where
  star f := starTestFunction f

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped SchwartzMap

/-- The constant‐field bilinear map `B(a)(b) = a * b`. -/
abbrev V := ℂ
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))

variable (f_positive : PositiveTimeTestFunction)

def starred_f' : TestFunctionℂ := star f_positive.val

#check star (f_positive : TestFunctionℂ)

def S (f : TestFunction) : ℂ := generatingFunctional dμ f

variable (f : TestFunction)
#check generatingFunctional dμ f

axiom GJAxiom_OS3 : ∀ (F : PositiveTimeTestFunction),
  0 ≤ (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).re ∧
      (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).im = 0
