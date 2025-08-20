
/-© 2025 Math definitions which arguably should be in mathlib
 -/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions

import Mathlib.Topology.Algebra.Module.LinearMapPiProd

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure

noncomputable section

/-! ## Analyticity of finite sums -/

/-- Double finite sums of analytic functions are analytic.
    This is a key lemma for proving analyticity of quadratic forms in complex variables. -/
lemma analyticOn_double_sum {n : ℕ} {f : Fin n → Fin n → (Fin n → ℂ) → ℂ} {s : Set (Fin n → ℂ)}
  (h : ∀ i j, AnalyticOn ℂ (f i j) s) :
  AnalyticOn ℂ (fun x => ∑ i, ∑ j, f i j x) s := by
  -- Use the fact that finite sums of analytic functions are analytic
  have h_outer : ∀ i, AnalyticOn ℂ (fun x => ∑ j, f i j x) s := by
    intro i
    have h_eq : (fun x => ∑ j, f i j x) = ∑ j, f i j := by
      funext x
      simp only [Finset.sum_apply]
    rw [h_eq]
    exact Finset.analyticOn_sum (Finset.univ) (fun j _ => h i j)
  have h_main_eq : (fun x => ∑ i, ∑ j, f i j x) = ∑ i, (fun x => ∑ j, f i j x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [h_main_eq]
  exact Finset.analyticOn_sum (Finset.univ) (fun i _ => h_outer i)

/-! ## Schwartz function properties -/

/- Multiplication of Schwarz functions
 -/

open scoped SchwartzMap

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- General version that works for any normed space over ℝ
lemma SchwartzMap.hasTemperateGrowth_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : 𝓢(E, V)) :
    Function.HasTemperateGrowth (⇑g) := by
  refine ⟨g.smooth', ?_⟩
  intro n
  -- take k = 0 in the decay estimate
  rcases g.decay' 0 n with ⟨C, hC⟩
  refine ⟨0, C, ?_⟩
  intro x
  have : ‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    simpa using hC x
  simpa using this

-- Original version for ℂ-normed spaces (kept for compatibility)
lemma SchwartzMap.hasTemperateGrowth
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : 𝓢(E, V)) :
    Function.HasTemperateGrowth (⇑g) := by
  refine ⟨g.smooth', ?_⟩
  intro n
  -- take k = 0 in the decay estimate
  rcases g.decay' 0 n with ⟨C, hC⟩
  refine ⟨0, C, ?_⟩
  intro x
  have : ‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    simpa using hC x
  simpa using this

/- Measure lifting from real to complex Lp spaces -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

-- Add measurable space instances for Lp spaces
instance [MeasurableSpace α] (μ : Measure α) : MeasurableSpace (Lp ℝ 2 μ) := borel _
instance [MeasurableSpace α] (μ : Measure α) : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
instance [MeasurableSpace α] (μ : Measure α) : MeasurableSpace (Lp ℂ 2 μ) := borel _
instance [MeasurableSpace α] (μ : Measure α) : BorelSpace (Lp ℂ 2 μ) := ⟨rfl⟩

-- Check if Complex.ofRealCLM is an isometry
lemma Complex.ofRealCLM_isometry : Isometry (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) := by
  -- Complex.ofRealCLM is defined as ofRealLI.toContinuousLinearMap,
  -- where ofRealLI is a linear isometry
  have h : (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) = Complex.ofRealLI.toContinuousLinearMap := rfl
  rw [h]
  -- The coercion to function is the same for both
  convert Complex.ofRealLI.isometry

-- Use this to prove our specific case
lemma Complex.ofRealCLM_continuous_compLp {α : Type*} [MeasurableSpace α] {μ : Measure α} :
  Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) := by
  -- The function φ ↦ L.compLp φ is the application of the continuous linear map
  -- ContinuousLinearMap.compLpL p μ L, which is continuous
  exact (ContinuousLinearMap.compLpL 2 μ Complex.ofRealCLM).continuous

/--
Compose an Lp function with a continuous linear map.
This should be the canonical way to lift real Lp functions to complex Lp functions.
-/
noncomputable def composed_function {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ): Lp ℂ 2 μ :=
  A.compLp f

-- Check that we get the expected norm bound
example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ) : ‖A.compLp f‖ ≤ ‖A‖ * ‖f‖ :=
  ContinuousLinearMap.norm_compLp_le A f

/--
Embedding from real Lp functions to complex Lp functions using the canonical embedding ℝ → ℂ.
-/
noncomputable def embedding_real_to_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (φ : Lp ℝ 2 μ) : Lp ℂ 2 μ :=
  composed_function φ (Complex.ofRealCLM)

section LiftMeasure
  variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

  /--
  Lifts a probability measure from the space of real Lp functions to the space of
  complex Lp functions, with support on the real subspace.
  -/
  noncomputable def liftMeasure_real_to_complex
      (dμ_real : ProbabilityMeasure (Lp ℝ 2 μ)) :
      ProbabilityMeasure (Lp ℂ 2 μ) :=
    let dμ_complex_measure : Measure (Lp ℂ 2 μ) :=
      Measure.map embedding_real_to_complex dμ_real
    have h_ae : AEMeasurable embedding_real_to_complex dμ_real := by
      apply Continuous.aemeasurable
      unfold embedding_real_to_complex composed_function
      have : Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) :=
        Complex.ofRealCLM_continuous_compLp
      exact this
    have h_is_prob := isProbabilityMeasure_map h_ae
    ⟨dμ_complex_measure, h_is_prob⟩

end LiftMeasure
