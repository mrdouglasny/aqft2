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
#check f.smooth'

noncomputable def compTimeReflection : TestFunctionℂ →L[ℝ] TestFunctionℂ := by
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
    use 1; use 1; simp; intro x
    have hh := ContinuousLinearMap.le_opNorm timeReflectionCLM x
    have hhh := 0 < ‖timeReflectionCLM‖
    sorry
  exact SchwartzMap.compCLM (𝕜 := ℝ) (hg := timeReflectionCLM.hasTemperateGrowth) (hg_upper := hg_upper)

#check compTimeReflection

noncomputable instance : Star TestFunctionℂ where
  star f := {
    toFun := fun x ↦ star (f (timeReflection x)),
    smooth' := by
      exact Complex.conjLIE.toContinuousLinearMap.contDiff.comp (f.smooth'.comp timeReflectionCLM.contDiff)
    decay' := by
      intro k n
      -- Get the decay bound for f
      rcases f.decay' k n with ⟨C, hf⟩
      use C
      intro x
      simp only [star]

      -- Key fact: timeReflection is a linear isometry
      have h_iso : ∀ y : SpaceTime, ‖timeReflection y‖ = ‖y‖ := by
        intro y
        have h := LinearIsometryEquiv.norm_map (timeReflectionLE : SpaceTime ≃ₗᵢ[ℝ] SpaceTime)
        exact h y

      -- The complex conjugate doesn't change norms
      have h_conj_norm : ∀ z : ℂ, ‖star z‖ = ‖z‖ := by
        intro z
        exact Complex.norm_conj z

      -- Now we can chain our inequalities
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ star (f (timeReflection x))) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (star ∘ f ∘ timeReflection) x‖ := by
          rfl
        _ = ‖timeReflection (timeReflection x)‖ ^ k * ‖iteratedFDeriv ℝ n (star ∘ f ∘ timeReflection) x‖ := by
          rw [h_iso (timeReflection x)]
        _ = ‖timeReflection x‖ ^ k * ‖iteratedFDeriv ℝ n f (timeReflection x)‖ := by
          sorry  -- Need lemma about derivatives of composed functions
        _ ≤ C := by
          exact hf (timeReflection x)
  }

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped SchwartzMap

/-- The constant‐field bilinear map `B(a)(b) = a * b`. -/
abbrev V := ℂ
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/- for some reason the version in FunctionalAnalysis doesn't elaborate -/
lemma SchwartzMap.hasTemperateGrowth'
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : 𝓢(SpaceTime, V)) :
    Function.HasTemperateGrowth (⇑g) := by
  refine ⟨g.smooth', ?_⟩
  intro n
  -- take k = 0 in the decay estimate
  rcases g.decay' 0 n with ⟨C, hC⟩
  refine ⟨0, C, ?_⟩
  intro x
  have : ‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    simpa using hC x
  simpa using this


/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (g.hasTemperateGrowth'))

variable (f_positive : PositiveTimeTestFunction)

def starred_f' : TestFunctionℂ := star f_positive.val

#check star (f_positive : TestFunctionℂ)

def S (f : TestFunction) : ℂ := generatingFunctional dμ f

variable (f : TestFunction)
#check generatingFunctional dμ f

axiom GJAxiom_OS3 : ∀ (F : PositiveTimeTestFunction),
  0 ≤ (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).re ∧
      (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).im = 0
