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
open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open MeasureTheory Complex

variable {𝕜 : Type} [RCLike 𝕜]

def STDimension := 4
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume    -- Lebesgue, just named “μ”
variable [SigmaFinite μ]

/- Euclidean symmetries of spacetime -/


/- Distributions and test functions -/

abbrev TestFunction : Type := SchwartzMap RSpaceTime ℝ
abbrev TestFunction𝕜 : Type := SchwartzMap RSpaceTime 𝕜

/- Space of fields -/

abbrev FieldSpace := Lp ℝ 2 μ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

abbrev FieldSpace𝕜 (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 2 μ
instance : MeasurableSpace (FieldSpace𝕜 ℂ) := borel _
instance : BorelSpace (FieldSpace𝕜 ℂ) := ⟨rfl⟩

#check FieldSpace
#check Module ℂ (FieldSpace𝕜 ℂ)
#check Lp ℂ 2 μ
example : SeminormedAddCommGroup (FieldSpace) := by infer_instance
example : SeminormedAddCommGroup (Lp ℂ 2 μ) := by infer_instance
example : SeminormedAddCommGroup (FieldSpace𝕜 ℂ) := by infer_instance
example : InnerProductSpace ℂ (FieldSpace𝕜 ℂ) := by infer_instance
example : BorelSpace (FieldSpace) := by infer_instance
example : BorelSpace (FieldSpace𝕜 ℂ) := by infer_instance

variable (x : RSpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

variable (dμ' : Measure (FieldSpace𝕜 ℂ))

/- Generating functional of correlation functions -/

def pairingCLM' (J : TestFunction𝕜 (𝕜 := ℂ)) : (FieldSpace𝕜 ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (E := FieldSpace𝕜 ℂ))
    (J.toLp (p := 2) (μ := μ))

def pairingCLM (J : TestFunction) : FieldSpace →L[ℝ] ℝ :=
  (innerSL ℝ (E := FieldSpace))
    (J.toLp (p := 2) (μ := μ))

def generatingFunctional (J : TestFunction) : ℂ :=
  charFunDual dμ (pairingCLM J)

def MeasureTheory.charFunC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E]
    (μ : Measure E) : (E →L[ℂ] ℂ) → ℂ :=
  fun L => ∫ x, cexp (I * L x) ∂μ

def generatingFunctionalℂ (J : TestFunction𝕜 (𝕜 := ℂ)) : ℂ :=
  charFunC dμ' (pairingCLM' J)
