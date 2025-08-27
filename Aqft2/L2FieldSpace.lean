/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Data.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

open Real Complex

noncomputable section

-- First define the basic space-time setup
variable (d : ℕ) [NeZero d]

-- d-dimensional Euclidean space (space-time)
abbrev SpaceTime := (Fin d → ℝ)
instance : MeasurableSpace SpaceTime := Pi.measureSpace 
instance : BorelSpace SpaceTime := Pi.borelSpace
variable (μ : MeasureTheory.Measure SpaceTime)

-- Test functions (Schwartz space)
abbrev TestFunction := SchwartzMap SpaceTime ℝ
abbrev TestFunction𝕜 : Type := SchwartzMap SpaceTime 𝕜
abbrev TestFunctionℂ := TestFunction𝕜 (𝕜 := ℂ)

/- Space of fields -/

abbrev FieldSpace := Lp ℝ 2 μ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

abbrev FieldSpace𝕜 (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 2 μ
instance : MeasurableSpace (FieldSpace𝕜 ℂ) := borel _
instance : BorelSpace (FieldSpace𝕜 ℂ) := ⟨rfl⟩

example : SeminormedAddCommGroup (FieldSpace𝕜 ℂ) := by infer_instance
example : InnerProductSpace ℂ (FieldSpace𝕜 ℂ) := by infer_instance
example : BorelSpace (FieldSpace) := by infer_instance
example : BorelSpace (FieldSpace𝕜 ℂ) := by infer_instance

variable (x : SpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

--variable (dμ' : Measure (FieldSpace𝕜 ℂ))

/- Generating functional of correlation functions -/

def pairingCLM' (J : TestFunction𝕜 (𝕜 := ℂ)) : (FieldSpace𝕜 ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (E := FieldSpace𝕜 ℂ))
    (J.toLp (p := 2) (μ := μ))

def pairingCLM (J : TestFunction) : FieldSpace →L[ℝ] ℝ :=
  (innerSL ℝ (E := FieldSpace))
    (J.toLp (p := 2) (μ := μ))

def generatingFunctional (J : TestFunction) : ℂ :=
  charFunDual dμ (pairingCLM J)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E]

def MeasureTheory.charFunC
  (μ : Measure E) : (E →L[ℂ] ℂ) → ℂ :=
  fun L => ∫ x, cexp (I * L x) ∂μ

variable (J : TestFunctionℂ)

def generatingFunctionalℂ (dμ : ProbabilityMeasure FieldSpace) (J : TestFunctionℂ) : ℂ :=
  charFunC (liftMeasure_real_to_complex dμ) (pairingCLM' J)

#check generatingFunctionalℂ dμ J

/-- The constant‐field bilinear map `B(a)(b) = a * b`. -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))

end