/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## AQFT Basic Framework

This file provides the foundational definitions for the Glimm-Jaffe approach to Algebraic Quantum Field Theory,
implementing field configurations as tempered distributions and the associated generating functionals.

### Key Definitions & Framework:

**Spacetime Structure:**
- `STDimension`: Spacetime dimension (4D)
- `STvector`: 4-vector type as Fin 4 → ℝ
- `SpaceTime`: Euclidean 4-space using EuclideanSpace
- `getTimeComponent`: Extracts time coordinate (t = x₄)
- `μ`: Standard Lebesgue measure on spacetime

**Test Function Spaces:**
- `TestFunction`: Real-valued Schwartz functions on spacetime
- `TestFunction𝕜`: Generic Schwartz functions over field 𝕜
- `TestFunctionℂ`: Complex-valued Schwartz functions
- `schwartzMul`: Multiplication operation on complex test functions
- `schwartz_comp_clm`: Composition with continuous linear maps (extends Schwartz regularity)

**Field Configurations as Distributions:**
- `FieldConfiguration`: Tempered distributions (WeakDual of Schwartz space)
- Proper weak-* topology for measure theory
- Measurable space structure via Borel σ-algebra

**Distribution Pairings:**
- `distributionPairing`: Real pairing ⟨ω, f⟩ between distributions and test functions
- `complex_testfunction_decompose`: Efficient real/imaginary decomposition for complex test functions
- `distributionPairingℂ_real`: Complex pairing ⟨ω, f⟩ = ⟨ω, Re f⟩ + i⟨ω, Im f⟩

**Glimm-Jaffe Generating Functionals:**
- `GJGeneratingFunctional`: Real generating functional Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
- `GJGeneratingFunctionalℂ`: Complex generating functional for analyticity
- `GJMean`: Mean field ⟨φ⟩ = ∫ ⟨ω, φ⟩ dμ(ω)

**Mathematical Foundation:**
This implements the distribution-based approach where:
1. Field configurations ω are tempered distributions, not L² functions
2. Generating functionals are defined via complex exponential integrals
3. All correlation functions emerge from functional derivatives
4. Complex analyticity (OS0) is naturally incorporated
5. Measure theory is well-defined on the weak-* topology

**Connection to Other Modules:**
- Schwinger functions and correlations → `Aqft2.Schwinger`
- Osterwalder-Schrader axioms → `Aqft2.OS_Axioms`
- Gaussian measures and Minlos theorem → `Aqft2.Minlos`, `Aqft2.GFFconstruct`
- Euclidean group actions → `Aqft2.Euclidean`

This provides the mathematical foundation for constructive quantum field theory
using the Osterwalder-Schrader framework.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.NormedSpace.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
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

example : AddCommGroup TestFunctionℂ := by infer_instance
example : Module ℂ TestFunctionℂ := by infer_instance

/- Space-time and test function setup -/

variable (x : SpaceTime)

/- Probability distribution over field configurations (distributions) -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))



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

-- Measurable space instance for distribution spaces
-- WeakDual already has the correct weak-* topology, we use the Borel σ-algebra
instance : MeasurableSpace FieldConfiguration := borel _

/-- The fundamental pairing between a field configuration (distribution) and a test function.
    This is ⟨ω, f⟩ in the Glimm-Jaffe notation.

    Note: FieldConfiguration = WeakDual ℝ (SchwartzMap SpaceTime ℝ) has the correct
    weak-* topology, making evaluation maps x ↦ ω(x) continuous for each test function x. -/
def distributionPairing (ω : FieldConfiguration) (f : TestFunction) : ℝ := ω f

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

/-- Helper function to create a Schwartz map from a complex test function by applying a continuous linear map.
    This factors out the common pattern for extracting real/imaginary parts. -/
private def schwartz_comp_clm (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) : TestFunction :=
  SchwartzMap.mk (fun x => L (f x)) (by
    -- L is a continuous linear map, hence smooth
    exact ContDiff.comp L.contDiff f.smooth'
  ) (by
    -- Polynomial growth: since |L(z)| ≤ ||L|| * |z|, derivatives are controlled
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C * (‖L‖ : ℝ)
    intro x
    -- |x|^k * |∂^n(L ∘ f)(x)| ≤ ||L|| * |x|^k * |∂^n f(x)| ≤ ||L|| * C
    sorry -- Technical: derivatives of L ∘ f are controlled by ||L|| * derivatives of f
  )

/-- Decompose a complex test function into its real and imaginary parts as real test functions.
    This is more efficient than separate extraction functions. -/
def complex_testfunction_decompose (f : TestFunctionℂ) : TestFunction × TestFunction :=
  (schwartz_comp_clm f Complex.reCLM, schwartz_comp_clm f Complex.imCLM)

/-- Complex version of the pairing: real field configuration with complex test function
    We extend the pairing by treating the complex test function as f(x) = f_re(x) + i*f_im(x)
    and defining ⟨ω, f⟩ = ⟨ω, f_re⟩ + i*⟨ω, f_im⟩ -/
def distributionPairingℂ_real (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  -- Extract real and imaginary parts using our efficient decomposition
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  -- Pair with the real field configuration and combine
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

/-- Complex version of the generating functional -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunctionℂ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure

/-- The mean field in the Glimm-Jaffe framework -/
def GJMean (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ : TestFunction) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure

-- Test the new definitions work correctly
variable (dμ_config : ProbabilityMeasure FieldConfiguration)

#check GJGeneratingFunctional dμ_config
#check GJGeneratingFunctionalℂ dμ_config

end
