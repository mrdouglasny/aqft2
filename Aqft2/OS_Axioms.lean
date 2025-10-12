/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Osterwalder-Schrader Axioms

The four OS axioms characterizing Euclidean field theories that admit analytic
continuation to relativistic QFTs:

- **OS-0**: `OS0_Analyticity` - Complex analyticity of generating functionals
- **OS-1**: `OS1_Regularity` - Exponential bounds and temperedness
- **OS-2**: `OS2_EuclideanInvariance` - Euclidean group invariance
- **OS-3**: `OS3_ReflectionPositivity` - Reflection positivity (multiple formulations)
- **OS-4**: `OS4_Ergodicity` - Ergodicity and clustering properties

Following Glimm-Jaffe formulation using probability measures on field configurations.
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Group.Support
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
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

import Aqft2.Basic
import Aqft2.Schwinger
import Aqft2.FunctionalAnalysis
import Aqft2.Euclidean
import Aqft2.DiscreteSymmetry
import Aqft2.SCV
import Aqft2.PositiveTimeTestFunction_real
import Aqft2.ComplexTestFunction
import Aqft2.OS4

/- These are the O-S axioms in the form given in Glimm and Jaffe, Quantum Physics, pp. 89-90 -/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure SCV QFT

-- Open DFunLike for SchwartzMap function application (from Basic.lean)
open DFunLike (coe)

-- Auxiliary alias for the real time-reflection linear map coming from `DiscreteSymmetry`.
@[simp] private noncomputable def compTimeReflectionReal_map : TestFunction →L[ℝ] TestFunction :=
  by
    classical
    have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x : SpaceTime, ‖x‖ ≤ C * (1 + ‖QFT.timeReflectionCLM x‖) ^ k := by
      refine ⟨1, 1, ?_⟩
      intro x
      have h_iso : ‖QFT.timeReflectionCLM x‖ = ‖x‖ := by
        have h_norm_preserved : ‖QFT.timeReflection x‖ = ‖x‖ :=
          LinearIsometryEquiv.norm_map QFT.timeReflectionLE x
        simpa [QFT.timeReflectionCLM] using h_norm_preserved
      have h_bound : ‖x‖ ≤ 1 * (1 + ‖QFT.timeReflectionCLM x‖) := by
        have h0 : ‖x‖ ≤ ‖x‖ + 1 := le_add_of_nonneg_right (show 0 ≤ (1 : ℝ) by exact zero_le_one)
        have h₁ : ‖x‖ ≤ 1 + ‖QFT.timeReflectionCLM x‖ := by
          calc
            ‖x‖ ≤ ‖x‖ + 1 := h0
            _ = 1 + ‖x‖ := by ring
            _ = 1 + ‖QFT.timeReflectionCLM x‖ := by simp [h_iso]
        calc
          ‖x‖ ≤ 1 + ‖QFT.timeReflectionCLM x‖ := h₁
          _ = 1 * (1 + ‖QFT.timeReflectionCLM x‖) := by simp
      simpa [pow_one] using h_bound
    exact SchwartzMap.compCLM (𝕜 := ℝ)
      (hg := QFT.timeReflectionCLM.hasTemperateGrowth)
      (hg_upper := hg_upper)

-- TODO: Fix import issue with Basic.lean definitions
-- The FieldConfiguration and GJ* definitions should be accessible but aren't currently

noncomputable section
open scoped MeasureTheory Complex BigOperators SchwartzMap

/-! ## Glimm-Jaffe Distribution-Based OS Axioms

The OS axioms (Osterwalder-Schrader) characterize Euclidean field theories that
admit analytic continuation to relativistic QFTs.
-/

/-- OS0 (Analyticity): The generating functional is analytic in the test functions. -/
def OS0_Analyticity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (J : Fin n → TestFunctionℂ),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) Set.univ

/-- Two-point correlation function using the proper Schwinger framework.
    For translation-invariant measures, this represents ⟨φ(x)φ(0)⟩.
    Uses the two-point Schwinger distribution with Dirac deltas. -/
def SchwingerTwoPointFunction (dμ_config : ProbabilityMeasure FieldConfiguration) (x : SpaceTime) : ℝ :=
  SchwingerFunction₂ dμ_config (DiracDelta x) (DiracDelta 0)

/-- Two-point function integrability condition for p = 2 -/
def TwoPointIntegrable (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  Integrable (fun x => (SchwingerTwoPointFunction dμ_config x)^2) volume

/-- OS1 (Regularity): The complex generating functional satisfies exponential bounds. -/
def OS1_Regularity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : TestFunctionℂ),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + (∫ x, ‖f x‖^p ∂volume)^(1/p)))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)

/-- OS2 (Euclidean Invariance): The measure is invariant under Euclidean transformations. -/
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (g : QFT.E) (f : TestFunctionℂ),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (QFT.euclidean_action g f)



/-- Real formulation of OS3 reflection positivity using the real-valued positive time
    subspace and the real generating functional. This version avoids explicit complex
    coefficients and conjugation, aligning more closely with the new real-valued
    `PositiveTimeTestFunction` infrastructure. -/
def OS3_ReflectionPositivity_real (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ),
    let reflection_matrix := fun i j : Fin n =>
      GJGeneratingFunctional dμ_config
        ((f i).val - compTimeReflectionReal_map ((f j).val))
    0 ≤ ∑ i, ∑ j, c i * c j * (reflection_matrix i j).re

/-- OS3 Reflection Invariance: The generating functional is invariant under time reflection.

    For reflection-positive measures, the generating functional should be invariant
    under time reflection: Z[Θf] = Z[f]. This ensures the consistency of the theory
    under the reflection operation. -/
def OS3_ReflectionInvariance (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f : TestFunctionℂ),
    -- The generating functional is exactly invariant under time reflection
    GJGeneratingFunctionalℂ dμ_config (QFT.compTimeReflection f) =
    GJGeneratingFunctionalℂ dμ_config f

/-- OS4 (Ergodicity): The measure is invariant and ergodic under an appropriate flow.

    In the distribution framework, ergodicity is formulated as:
    1. The measure is invariant under some flow on field configurations
    2. The flow action is ergodic (irreducible - no non-trivial invariant sets)
    3. This ensures clustering properties: separated regions become uncorrelated

    The flow typically represents spatial translations or other symmetry operations
    that preserve the physical properties of the field theory.
-/
def OS4_Ergodicity (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∃ (φ : QFT.Flow FieldConfiguration),
    QFT.invariant_under (dμ_config : Measure FieldConfiguration) φ ∧
    QFT.ergodic_action (dμ_config : Measure FieldConfiguration) φ

/-- OS4 Alternative: Clustering via correlation decay.

    This is an alternative formulation that directly expresses the clustering property:
    correlations between well-separated regions decay to zero. This is equivalent
    to ergodicity for translation-invariant measures.
-/
def OS4_Clustering (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f g : TestFunctionℂ) (ε : ℝ), ε > 0 → ∃ (R : ℝ), R > 0 ∧ ∀ (sep : ℝ),
    sep > R →
    ‖GJGeneratingFunctionalℂ dμ_config (schwartzMul f (translate_test_function_complex sep g)) -
     GJGeneratingFunctionalℂ dμ_config f * GJGeneratingFunctionalℂ dμ_config g‖ < ε
  where
    /-- Placeholder: spatial translation acting on complex test functions.
        The full construction should compose `f` with the spatial translation map.
        For now we keep the identity map so the definition typechecks and downstream
        development can proceed. -/
  translate_test_function_complex (_sep : ℝ) (f : TestFunctionℂ) : TestFunctionℂ := f

/-! ## Matrix Formulation of OS3

The matrix formulation is the most reliable form following Glimm-Jaffe directly.
It avoids the complications of the standard formulation and provides a clear
computational framework for verifying reflection positivity.
-/

/-- Reflection invariance implies certain properties for the standard OS3 formulation.
    If Z[Θf] = Z[f], then the generating functional is stable under time reflection,
    which is a natural consistency condition for reflection-positive theories. -/
theorem reflection_invariance_supports_OS3 (dμ_config : ProbabilityMeasure FieldConfiguration) :
  OS3_ReflectionInvariance dμ_config →
  ∀ (F : PositiveTimeTestFunction),
    let F_complex := toComplex F.val  -- Convert to complex
    GJGeneratingFunctionalℂ dμ_config (QFT.compTimeReflection F_complex) =
    GJGeneratingFunctionalℂ dμ_config F_complex := by
  intro h_invariance F
  -- Direct application of reflection invariance
  exact h_invariance (toComplex F.val)
