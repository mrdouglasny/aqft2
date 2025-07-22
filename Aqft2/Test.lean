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

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real

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

/-- GJ Axiom OS0. -/

axiom GJAxiom_OS0 : Entire (trial n J dμ)

/- tests of ability to prove functions are analytic -/

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
