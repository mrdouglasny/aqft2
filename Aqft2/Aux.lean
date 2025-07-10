/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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


noncomputable section
open scoped MeasureTheory Complex

/- complexified version -/

def phi (J : TestFunctionℂ) : ComplexFieldSpace →L[ℂ] ℂ :=
  innerSL ℂ (E := ComplexFieldSpace) (J.toLp (p := 2) (μ := μ))

def lifttoℂ : FieldSpace →L[ℝ] ComplexFieldSpace := sorry

def pairingCLMℂ (J : TestFunctionℂ) : ComplexFieldSpace →L[ℂ] ℂ :=
  (innerSL ℂ (E := ComplexFieldSpace))
    (J.toLp (p := 2) (μ := μ))

def charFunDualℝ (J : Lp ℝ 2 μ) : (Lp ℝ 2 μ) →L[ℝ] ℝ :=
  innerSL ℝ (E := Lp ℝ 2 μ) J

def ofRealCLM : ℝ →L[ℝ] ℂ :=
{ toLinearMap :=
    { toFun       := fun t ↦ (t : ℂ),
      map_add'    := by simp,
      map_smul' := by simp }
  }

def charFunDual_fromReal (J : Lp ℝ 2 μ) :
    (Lp ℝ 2 μ) →L[ℝ] ℂ :=
  ofRealCLM.comp (charFunDualℝ J)

def charFunDual_fromReal' (J : Lp ℝ 2 μ) : (Lp ℝ 2 μ) →L[ℝ] ℂ :=
  (charFunDualℝ J).extendTo𝕜 ℂ

def generatingFunctionalℂ (J : TestFunctionℂ) : ℂ :=
  charFunDual dμ (pairingCLMℂ J)

/- Local functionals on fields -/
def polyObservable (p : Polynomial ℝ) (φ : FieldSpace) : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ

/- stuff -/
def realToComplexCLM : (Lp ℝ 2 μ) →L[ℝ] Lp ℂ 2 μ :=
  (fun f ↦ f.map _ (fun x ↦ (algebraMap ℝ ℂ (f x))).measurable
                (by simpa using f.mem_ℒp_complex_iff.1 f.mem_ℒp))
  |>.mkContinuousOfExistsBound 1 (by
        refine ⟨1, ?_⟩; intros f; simp)  -- any linear map on a finite-dim space is bounded

#check Lp.realToComplex (μ := μ)  --  Lp ℝ μ p ≃ₗᵵ[ℝ] Lp ℂ μ p

def realToComplexCLM : Lp ℝ (p := 2) μ →L[ℂ] Lp ℂ (p := 2) μ :=
  ((Lp.realToComplex μ).restrict_scalars ℂ).toContinuousLinearMap

noncomputable
def charFunDual_fromReal (J : Lp ℝ μ 2) : (Lp ℂ μ 2) →L[ℂ] ℂ :=
  charFunDualℂ (μ := μ) (realToComplexCLM J)
