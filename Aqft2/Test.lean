/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

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

import Aqft2.Basic

/- These are the O-S axioms in the form given in Glimm and Jaffe, Quantum Physics, pp. 89-90 -/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open scoped MeasureTheory Complex BigOperators
--open scoped RealInnerProductSpace

/- OS0 Analyticity -/

abbrev ℂn (n : ℕ) := Fin n → ℂ
-- EuclideanSpace ℂ (Fin n)

variable (n : ℕ)
def foo := (∑ n_1, fun x : ℂn n => x n_1 ^ 2)
def bar := (fun x : ℂn n ↦ ∑ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ 2)
#check foo
#check bar



--example test : foo = bar

def Entire {n : ℕ} (f : ℂn n → ℂ) : Prop :=
  AnalyticOn ℂ f Set.univ          --  ⇔  ∀ z, HolomorphicAt ℂ f z

def gaussian1 (z : ℂ) : ℂ := Complex.exp (-(z ^ 2))

lemma h_exp_arg : AnalyticOn ℂ (fun z : ℂ ↦ -(z ^ 2)) Set.univ :=
  ((analyticOn_id (𝕜 := ℂ) (E := ℂ) (s := Set.univ)).pow 2).neg

/-- The Gaussian is analytic on all of ℂ – i.e. *entire*. -/
lemma gaussian1_entire : AnalyticOn ℂ gaussian1 Set.univ := by
 simpa [gaussian1] using
  ((analyticOn_id (𝕜 := ℂ) (E := ℂ) (s := Set.univ)).pow 2).neg.cexp

def gaussian (x : ℂn n) : ℂ := Complex.exp (-∑ i, (x i)^2)

lemma sumSquares_analytic {n : ℕ} :
    AnalyticOn ℂ (fun x : ℂn n ↦ ∑ i, (x i) ^ 2) Set.univ := by
  /- 1.  Each coordinate projection is analytic-on-a-neighbourhood. -/
  have h_coord (i : Fin n) :
      AnalyticOnNhd ℂ (fun x : ℂn n ↦ x i) Set.univ :=
      (ContinuousLinearMap.proj i : ℂn n →L[ℂ] ℂ).analyticOnNhd _

  /- 2.  Square it (`(hf).pow 2`) – still `AnalyticOnNhd`. -/
  have h_sq (i : Fin n) :
      AnalyticOnNhd ℂ (fun x : ℂn n ↦ (x i) ^ 2) Set.univ :=
      (h_coord i).pow 2

  have h_sum_aux :
      AnalyticOnNhd ℂ
        (fun x : ℂn n ↦ ∑ i ∈ (Finset.univ : Finset (Fin n)), (x i) ^ 2)
        Set.univ := by
          have foo := Finset.analyticOnNhd_sum
             (N := (Finset.univ : Finset (Fin n)))
              (f := fun i ↦ fun x : ℂn n ↦ (x i) ^ 2)
             (λ i _hi ↦ h_sq i)
          simpa using sorry

  simpa [Finset.sum_apply] using h_sum_aux.analyticOn

variable (x : ℂ) (f : TestFunctionℂ)

#check x • f        -- Lean should report:  `x • f : TestFunctionℂ`

variable {n : ℕ}
variable (z : ℂn n)               -- coefficients
variable (J : Fin n → TestFunctionℂ)   -- test functions

variable {f : ℂn n → ℂ}

#check AnalyticOn ℂ f Set.univ  -- joint analyticity in all n coordinates

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

abbrev weightedSum (z : ℂn n) : TestFunctionℂ := weightedSumCLM J z

variable (dμ : ProbabilityMeasure FieldSpace)

#check (generatingFunctional dμ (weightedSum J z))

/-- GJ Axiom OS0. -/

lemma GJAxiom_OS0 : AnalyticOn ℂ (generatingFunctional (weightedSum J))  Set.univ := by
  sorry

/-- **Entire‐ness**: the map `z ↦ ∑ zᵢ • Jᵢ` is analytic on all of ℂⁿ. -/
lemma weightedSum_analytic :
    AnalyticOn ℂ (generatingFunctional (weightedSum J)) Set.univ :=
      (weightedSumCLM J).analyticOn _
