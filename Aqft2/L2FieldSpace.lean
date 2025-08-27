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
variable (μ : MeasureTheory.Measure SpaceTime) [SigmaFinite μ]

-- Test functions (Schwartz space)
abbrev TestFunction := SchwartzMap SpaceTime ℝ
abbrev TestFunction𝕜 {𝕜 : Type*} [RCLike 𝕜] : Type := SchwartzMap SpaceTime 𝕜
abbrev TestFunctionℂ := TestFunction𝕜 (𝕜 := ℂ)

/- Space of fields -/

abbrev FieldSpace := Lp ℝ 2 μ
instance : MeasurableSpace FieldSpace := borel _
instance : BorelSpace    FieldSpace := ⟨rfl⟩

abbrev FieldSpace𝕜 {𝕜 : Type*} [RCLike 𝕜] := Lp 𝕜 2 μ
instance {𝕜 : Type*} [RCLike 𝕜] : MeasurableSpace (FieldSpace𝕜 (𝕜 := 𝕜)) := borel _
instance {𝕜 : Type*} [RCLike 𝕜] : BorelSpace (FieldSpace𝕜 (𝕜 := 𝕜)) := ⟨rfl⟩

example : SeminormedAddCommGroup (FieldSpace𝕜 (𝕜 := ℂ)) := by infer_instance
example : InnerProductSpace ℂ (FieldSpace𝕜 (𝕜 := ℂ)) := by infer_instance
example : BorelSpace (FieldSpace) := by infer_instance
example : BorelSpace (FieldSpace𝕜 (𝕜 := ℂ)) := by infer_instance

variable (x : SpaceTime) (φ : FieldSpace)

/- Probability distribution over fields -/

variable (dμ : ProbabilityMeasure FieldSpace)

--variable (dμ' : Measure (FieldSpace𝕜 ℂ))

/- Generating functional of correlation functions -/

def pairingCLM' (J : TestFunction𝕜 (𝕜 := ℂ)) : (FieldSpace𝕜 (𝕜 := ℂ)) →L[ℂ] ℂ :=
  (innerSL ℂ (E := FieldSpace𝕜 (𝕜 := ℂ)))
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

/-! ## L2 Bilinear Form for Complex Analyticity

The key insight for complex analyticity (OS0) is to use symmetric bilinear forms
instead of sesquilinear inner products:

- Inner product: ⟪f,g⟫ = ∫ conj(f(x)) * g(x) dμ(x)
- Conjugation breaks complex analyticity!
- Scaling: ⟪z•f, g⟫ = conj(z) * ⟪f,g⟫ (anti-linear)

- Bilinear form: B(f,g) = ∫ f(x) * g(x) dμ(x)
- Preserves complex analyticity: polynomial in z gives entire functions

This approach enables the proof of OS0 analyticity for Gaussian Free Fields.
-/

/-- The L2 bilinear form: ∫ f(x) * g(x) dμ(x)
    This is the correct bilinear form for complex analyticity on L2 spaces.
    Unlike the sesquilinear inner product ⟪f,g⟫ = ∫ conj(f(x)) * g(x) dμ(x),
    this bilinear form has no conjugation: B(z•f, g) = z * B(f, g). -/
def L2BilinearForm (f g : FieldSpace𝕜 (𝕜 := ℂ)) : ℂ :=
  ∫ x, f x * g x ∂μ

/-- L2BilinearForm is symmetric -/
lemma L2BilinearForm_symm (f g : FieldSpace𝕜 (𝕜 := ℂ)) :
  L2BilinearForm f g = L2BilinearForm g f := by
  unfold L2BilinearForm
  congr 1
  ext x
  ring

/-- L2BilinearForm is homogeneous in the first argument (key for analyticity!)
    This is the crucial property: B(z•f, g) = z * B(f, g) with NO conjugation -/
lemma L2BilinearForm_smul_left (c : ℂ) (f g : FieldSpace𝕜 (𝕜 := ℂ)) :
  L2BilinearForm (c • f) g = c * L2BilinearForm f g := by
  unfold L2BilinearForm
  -- This should follow from (c • f) x = c * f x and linearity of integration
  -- The key insight: no conjugation appears!
  sorry -- Technical integration details with L2 coercions

/-- L2BilinearForm is homogeneous in the second argument -/
lemma L2BilinearForm_smul_right (c : ℂ) (f g : FieldSpace𝕜 (𝕜 := ℂ)) :
  L2BilinearForm f (c • g) = c * L2BilinearForm f g := by
  unfold L2BilinearForm
  sorry -- Similar to smul_left

/-- L2BilinearForm is additive -/
lemma L2BilinearForm_add_left (f₁ f₂ g : FieldSpace𝕜 (𝕜 := ℂ)) :
  L2BilinearForm (f₁ + f₂) g = L2BilinearForm f₁ g + L2BilinearForm f₂ g := by
  unfold L2BilinearForm
  sorry -- Follows from linearity of integration

/-- The key property: L2BilinearForm expands bilinearly for linear combinations.
    This is what preserves complex analyticity! -/
lemma L2BilinearForm_linear_combination (n : ℕ) (z : Fin n → ℂ) (J : Fin n → FieldSpace𝕜 (𝕜 := ℂ)) :
  L2BilinearForm (∑ i, z i • J i) (∑ j, z j • J j) =
  ∑ i, ∑ j, z i * z j * L2BilinearForm (J i) (J j) := by
  -- This is the crucial expansion that shows the quadratic form is polynomial in z
  -- No conjugation means z i * z j (not z i * conj(z j))
  sorry -- Follows from bilinearity and distributivity of sums

/-- The constant‐field bilinear map `B(a)(b) = a * b`. -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  sorry -- SchwartzMap multiplication needs proper setup

end
