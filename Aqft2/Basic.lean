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
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.NormedSpace.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Algebra.Module.WeakDual

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Basic

-- Import our functional analysis utilities
import Aqft2.FunctionalAnalysis

-- Euclidean geometry definitions are now in Aqft2.Euclidean
-- but we define basic spacetime here to avoid circular imports
abbrev STDimension := 4
abbrev STvector : Type := (Fin STDimension) → ℝ
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)

noncomputable instance : InnerProductSpace ℝ SpaceTime := by infer_instance

abbrev getTimeComponent (x : SpaceTime) : ℝ :=
 x ⟨0, by simp +arith⟩

/-- Time reflection operator: (t, x) ↦ (-t, x) -/
def timeReflection (x : SpaceTime) : SpaceTime :=
  fun i => if i = 0 then -x i else x i

/-- Action of time reflection on test functions: (Rf)(x) = f(R⁻¹x) = f(timeReflection x) -/
def reflectTestFunction (f : TestFunction) : TestFunction :=
  sorry -- f.comp timeReflection -- Need proper composition for SchwartzMap

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure

-- Also open FunLike for SchwartzMap function application
open DFunLike (coe)

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]

abbrev μ : Measure SpaceTime := volume    -- Lebesgue, just named “μ”
variable [SigmaFinite μ]

/- Distributions and test functions -/

abbrev TestFunction : Type := SchwartzMap SpaceTime ℝ
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

/-! ## L2 Bilinear Form for Complex Analyticity

The key insight for complex analyticity (OS0) is to use symmetric bilinear forms
instead of sesquilinear inner products for the quadratic terms in generating functionals.

**Mathematical reason**:
- Sesquilinear inner products: ⟪·,·⟫_ℂ are conjugate-linear in the first argument
- This introduces conjugation: ⟪z•f, g⟫ = conj(z) * ⟪f, g⟫
- Conjugation breaks complex analyticity!

**Solution**:
- Symmetric bilinear forms: B : F →L[ℂ] F →L[ℂ] ℂ are linear in both arguments
- No conjugation: B(z•f, g) = z * B(f, g)
- Preserves complex analyticity: polynomial in z gives entire functions

This approach enables the proof of OS0 analyticity for Gaussian Free Fields.
-/

/-- The L2 bilinear form: ∫ f(x) * g(x) dμ(x)
    This is the correct bilinear form for complex analyticity on L2 spaces.
    Unlike the sesquilinear inner product ⟪f,g⟫ = ∫ conj(f(x)) * g(x) dμ(x),
    this bilinear form has no conjugation: B(z•f, g) = z * B(f, g). -/
def L2BilinearForm (f g : FieldSpace𝕜 ℂ) : ℂ :=
  ∫ x, f x * g x ∂μ

omit [SigmaFinite μ] in
/-- L2BilinearForm is symmetric -/
lemma L2BilinearForm_symm (f g : FieldSpace𝕜 ℂ) :
  L2BilinearForm f g = L2BilinearForm g f := by
  unfold L2BilinearForm
  congr 1
  ext x
  ring

/-- L2BilinearForm is homogeneous in the first argument (key for analyticity!)
    This is the crucial property: B(z•f, g) = z * B(f, g) with NO conjugation -/
lemma L2BilinearForm_smul_left (c : ℂ) (f g : FieldSpace𝕜 ℂ) :
  L2BilinearForm (c • f) g = c * L2BilinearForm f g := by
  unfold L2BilinearForm
  -- This should follow from (c • f) x = c * f x and linearity of integration
  -- The key insight: no conjugation appears!
  sorry -- Technical integration details with L2 coercions

/-- L2BilinearForm is homogeneous in the second argument -/
lemma L2BilinearForm_smul_right (c : ℂ) (f g : FieldSpace𝕜 ℂ) :
  L2BilinearForm f (c • g) = c * L2BilinearForm f g := by
  unfold L2BilinearForm
  sorry -- Similar to smul_left

/-- L2BilinearForm is additive -/
lemma L2BilinearForm_add_left (f₁ f₂ g : FieldSpace𝕜 ℂ) :
  L2BilinearForm (f₁ + f₂) g = L2BilinearForm f₁ g + L2BilinearForm f₂ g := by
  unfold L2BilinearForm
  sorry -- Follows from linearity of integration

/-- The key property: L2BilinearForm expands bilinearly for linear combinations.
    This is what preserves complex analyticity! -/
lemma L2BilinearForm_linear_combination (n : ℕ) (z : Fin n → ℂ) (J : Fin n → FieldSpace𝕜 ℂ) :
  L2BilinearForm (∑ i, z i • J i) (∑ j, z j • J j) =
  ∑ i, ∑ j, z i * z j * L2BilinearForm (J i) (J j) := by
  -- This is the crucial expansion that shows the quadratic form is polynomial in z
  -- No conjugation means z i * z j (not z i * conj(z j))
  sorry -- Follows from bilinearity and distributivity of sums

/-! ## Glimm-Jaffe Distribution Framework

The proper mathematical foundation for quantum field theory uses
tempered distributions as field configurations, following Glimm and Jaffe.
This section adds the distribution-theoretic definitions alongside
the existing L2 framework for comparison and gradual transition.
-/

/-- Field configurations as tempered distributions (dual to Schwartz space).
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L2 functions.

    Using WeakDual gives the correct weak-* topology on the dual space. -/
abbrev FieldConfiguration := WeakDual ℝ (SchwartzMap SpaceTime ℝ)

/-- Complex-valued field configurations for the generating functional -/
abbrev FieldConfigurationℂ := WeakDual ℂ (SchwartzMap SpaceTime ℂ)

-- Measurable space instances for distribution spaces
-- WeakDual already has the correct weak-* topology, we use the Borel σ-algebra
instance : MeasurableSpace FieldConfiguration := borel _
instance : MeasurableSpace FieldConfigurationℂ := borel _

/-- The fundamental pairing between a field configuration (distribution) and a test function.
    This is ⟨ω, f⟩ in the Glimm-Jaffe notation.

    Note: FieldConfiguration = WeakDual ℝ (SchwartzMap SpaceTime ℝ) has the correct
    weak-* topology, making evaluation maps x ↦ ω(x) continuous for each test function x. -/
def distributionPairing (ω : FieldConfiguration) (f : TestFunction) : ℝ := ω f

/-- Complex version of the pairing -/
def distributionPairingℂ (ω : FieldConfigurationℂ) (f : TestFunctionℂ) : ℂ := ω f

/-- The covariance in the Glimm-Jaffe framework: C(φ,ψ) = ∫ ⟨ω,φ⟩⟨ω,ψ⟩ dμ(ω)
    where the integral is over field configurations ω, not spacetime points. -/
def GJCovariance (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ ψ : TestFunction) : ℝ :=
  ∫ ω, (distributionPairing ω φ) * (distributionPairing ω ψ) ∂dμ_config.toMeasure

/-- Complex version for the generating functional -/
def GJCovarianceℂ (dμ_config : ProbabilityMeasure FieldConfigurationℂ)
  (φ ψ : TestFunctionℂ) : ℂ :=
  ∫ ω, (distributionPairingℂ ω φ) * (distributionPairingℂ ω ψ) ∂dμ_config.toMeasure

/-! ## Glimm-Jaffe Generating Functional

The generating functional in the distribution framework:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
where the integral is over field configurations ω (distributions).
-/

/-- The Glimm-Jaffe generating functional: Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
    This is the fundamental object in constructive QFT. -/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunction) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure

/-- Helper lemma: The real part of a complex test function is a real test function -/
lemma complex_testfunction_re (f : TestFunctionℂ) : ∃ (g : TestFunction), ∀ x, g x = (f x).re :=
  sorry -- This should follow from SchwartzMap.compCLM with Complex.reCLM

/-- Helper lemma: The imaginary part of a complex test function is a real test function -/
lemma complex_testfunction_im (f : TestFunctionℂ) : ∃ (g : TestFunction), ∀ x, g x = (f x).im :=
  sorry -- This should follow from SchwartzMap.compCLM with Complex.imCLM

/-- Complex version of the pairing: real field configuration with complex test function
    We extend the pairing by treating the complex test function as f(x) = f_re(x) + i*f_im(x)
    and defining ⟨ω, f⟩ = ⟨ω, f_re⟩ + i*⟨ω, f_im⟩ -/
def distributionPairingℂ_real (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  -- Extract real and imaginary parts using the helper lemmas
  let f_re := (complex_testfunction_re f).choose
  let f_im := (complex_testfunction_im f).choose
  -- Pair with the real field configuration and combine
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)/-- Complex version of the generating functional -/

def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunctionℂ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure

/-- The mean field in the Glimm-Jaffe framework -/
def GJMean (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ : TestFunction) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure

/-- For a centered measure (zero mean), we can define the Gaussian generating functional
    This assumes the measure has zero mean - we'll add the constraint later -/
def GJGaussianGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunctionℂ) : ℂ :=
  -- For Gaussian measures, Z[J] = exp(-½⟨J, CJ⟩) where C is the covariance
  -- We need to define the complex covariance properly
  sorry -- Complex.exp (-(1/2 : ℂ) * GJCovarianceℂ dμ_config J J)

-- Test the new definitions work correctly
variable (dμ_config : ProbabilityMeasure FieldConfiguration)
variable (dμ_configℂ : ProbabilityMeasure FieldConfigurationℂ)

#check GJGeneratingFunctional dμ_config
#check GJGeneratingFunctionalℂ dμ_config
#check GJCovariance dμ_config
#check GJGaussianGeneratingFunctional dμ_config

end
