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
import Mathlib.Analysis.InnerProductSpace.PiL2
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

--import Aqft2.Euclidean
import Aqft2.Basic
import Aqft2.SCV

/- These are the O-S axioms in the form given in Glimm and Jaffe, Quantum Physics, pp. 89-90 -/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure SCV

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

--def PositiveTimeTestFunction : Type :=
--  { f : TestFunctionℂ // tsupport f ⊆ positiveTimeSet }

def timeReflection (x : SpaceTime) : SpaceTime := update x 0 (-(x 0))

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

#check EuclideanAlgebra

-- we took out the complex conjugation
noncomputable instance : Star TestFunctionℂ where
  star f := {
    toFun := fun x ↦ (f (timeReflection x)), -- `star` on ℂ is complex conjugation
    -- Proofs that the result is still a Schwartz function would follow
    smooth' := by sorry,
    decay' := by sorry
  }

/- it seems that mathlib does not implement multiplication of Schwarz functions
 -/
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def schwartzMul
    (f g : TestFunctionℂ) : TestFunctionℂ :=
by
  refine
    { toFun   := fun x => f x * g x
      smooth' := (f.smooth').mul g.smooth'     -- `ContDiff.mul`
      decay'  := (f.decay').mul g.decay' }     -- `SchwartzWith.mul`


-- This should provide the HMul instance needed for your axiom.
example (f g : TestFunctionℂ) : TestFunctionℂ := schwartzMul f g

variable (f_positive : PositiveTimeTestFunction)

def starred_f' : TestFunctionℂ := star f_positive.val

#check star (f_positive : TestFunctionℂ)

def S (f : TestFunction) : ℂ := generatingFunctional dμ f

variable (f : TestFunction)
#check generatingFunctional dμ f

axiom GJAxiom_OS3 : ∀ (F : PositiveTimeTestFunction),
  0 ≤ (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).re ∧
      (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).im = 0
