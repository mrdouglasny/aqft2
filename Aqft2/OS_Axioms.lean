/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.Exponential
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
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real

import Aqft2.FunctionalAnalysis
import Aqft2.Basic
import Aqft2.Euclidean
import Aqft2.DiscreteSymmetry
import Aqft2.SCV
import Aqft2.PositiveTimeTestFunction

/- These are the O-S axioms in the form given in Glimm and Jaffe, Quantum Physics, pp. 89-90 -/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure SCV QFT

noncomputable section
open scoped MeasureTheory Complex BigOperators SchwartzMap

def S (dμ : ProbabilityMeasure FieldSpace) (f : TestFunction) : ℂ := generatingFunctional dμ f

-- OS0: The analyticity axiom - the generating functional is entire in complex linear combinations
def OS0_Analyticity (dμ : ProbabilityMeasure FieldSpace) : Prop :=
  ∀ (n : ℕ) (J : Fin n → TestFunctionℂ), Entire (fun z : ℂn n =>
    generatingFunctionalℂ dμ (weightedSumCLM (n := n) (J := J) z))

-- OS1: The regularity bound on the generating functional
def OS1_bound (dμ : ProbabilityMeasure FieldSpace) (f : TestFunction) (p : ℝ) (c : ℝ) : Prop :=
  ‖generatingFunctional dμ f‖ ≤ Real.exp (c * (∫ x, ‖f x‖ ∂μ + (∫ x, ‖f x‖^p ∂μ)^(1/p)))

-- OS1: Additional condition when p = 2 for two-point function integrability
def OS1_two_point_condition (_ : ProbabilityMeasure FieldSpace) : Prop :=
  -- Placeholder for two-point function integrability condition
  -- TODO: Implement proper two-point function integrability
  True

-- OS1: The regularity axiom
def OS1_Regularity (dμ : ProbabilityMeasure FieldSpace) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : TestFunction), OS1_bound dμ f p c) ∧
    (p = 2 → OS1_two_point_condition dμ)

-- OS2: Euclidean invariance axiom
def OS2_EuclideanInvariance (dμ : ProbabilityMeasure FieldSpace) : Prop :=
  ∀ (g : QFT.E) (f : TestFunctionℂ),
    generatingFunctionalℂ dμ f = generatingFunctionalℂ dμ (QFT.euclidean_action g f)

-- OS3 Reflection Positivity

def OS3_ReflectionPositivity (dμ : ProbabilityMeasure FieldSpace) : Prop :=
  ∀ (F : PositiveTimeTestFunction),
    0 ≤ (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).re ∧
        (generatingFunctionalℂ dμ (schwartzMul (star F.val) F.val)).im = 0

-- OS4: The ergodicity axiom
def OS4_Ergodicity (_ : ProbabilityMeasure FieldSpace) : Prop :=
  -- This axiom states that time averages of dynamical quantities converge to
  -- their ensemble averages (given by the generating functional).
  --
  -- The CORRECT formulation should involve:
  -- - Left side: Time average of some DYNAMICAL quantity (not involving dμ)
  --   Examples might include:
  --   * lim_{T→∞} (1/T) ∫₀ᵀ ⟨φ(t·e₀), f⟩ dt  (field expectation)
  --   * lim_{T→∞} (1/T) ∫₀ᵀ F[T_t φ] dt  (some functional of translated fields)
  -- - Right side: Ensemble average = generating functional with respect to dμ
  --
  -- The key insight is that the left side should involve the DYNAMICS of the field
  -- (time evolution, field correlations, etc.) while the right side involves the
  -- STATISTICS (probability measure dμ).
  --
  -- This captures the fundamental principle: Dynamical averages = Statistical averages
  --
  -- However, the exact form of the dynamical quantity on the left depends on
  -- the specific formulation of the field theory and requires a proper dynamical
  -- framework which we haven't established yet.
  --
  -- TODO: Replace with correct formulation once we have:
  -- 1. A proper dynamical system on field space (Hamiltonian, time evolution, etc.)
  -- 2. Field observables/functionals that don't depend on the measure dμ
  -- 3. The correct mathematical machinery for field dynamics and time evolution
  -- 4. Clarification from the literature on the exact form of OS4
  True  -- Placeholder for now
