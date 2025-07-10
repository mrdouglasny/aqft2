/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section
open scoped MeasureTheory

def STDimension := 4
abbrev RSpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev μ : Measure RSpaceTime := volume    -- Lebesgue, just named “μ”

/- Distributions and test functions -/

abbrev TestFunction : Type := SchwartzMap RSpaceTime ℝ
abbrev TestFunctionℂ : Type := SchwartzMap RSpaceTime ℂ

/- Space of fields -/

abbrev FieldSpace := Lp (p := 2) (μ := μ) ℝ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

abbrev ComplexFieldSpace := Lp (p := 2) (μ := μ) ℂ
instance : MeasurableSpace ComplexFieldSpace := borel _
instance : BorelSpace    ComplexFieldSpace := ⟨rfl⟩

variable (x : RSpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

variable (dμ' : ProbabilityMeasure ComplexFieldSpace)

/- Generating functional of correlation functions -/

def pairingCLM (J : TestFunction) : FieldSpace →L[ℝ] ℝ :=
  (innerSL ℝ (E := FieldSpace))
    (J.toLp (p := 2) (μ := μ))

def generatingFunctional (J : TestFunction) : ℂ :=
  charFunDual dμ (pairingCLM J)

def pairingCLMℂ (J : TestFunctionℂ) : ComplexFieldSpace →L[ℂ] ℂ :=
  (innerSL ℂ (E := ComplexFieldSpace))
    (J.toLp (p := 2) (μ := μ))

def generatingFunctionalℂ (J : TestFunctionℂ) : ℂ :=
  charFunDual dμ (pairingCLMℂ J)

/- Local functionals on fields -/
def polyObservable (p : Polynomial ℝ) (φ : FieldSpace) : ℝ :=
  ∫ x, p.eval ((φ : RSpaceTime →ₘ[μ] ℝ) x) ∂μ
