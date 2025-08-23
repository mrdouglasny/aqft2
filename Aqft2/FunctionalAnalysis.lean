
/-© 2025 Math definitions which arguably should be in mathlib
 -/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
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
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open scoped FourierTransform

noncomputable section

/-! ## Sphere Volume Formulas -/

/-- Volume of the unit sphere S^{d-1} in d-dimensional space.
    We use the standard formula: vol(S^{d-1}) = 2π^{d/2} / Γ(d/2)

    This is mathematically equivalent to the Mathlib ball volume formulas:
    - Volume of unit ball B^d = π^{d/2} / Γ(d/2 + 1)
    - Volume of unit sphere S^{d-1} = d * Volume(unit ball) = 2π^{d/2} / Γ(d/2)

    We provide explicit values for commonly used dimensions d=1,2,3,4,
    and use the exact Gamma function formula for general d.
-/
def unitSphereVolume (d : ℕ) : ℝ :=
  match d with
  | 1 => 2  -- S⁰ = {-1, 1}
  | 2 => 2 * Real.pi  -- S¹ = circle
  | 3 => 4 * Real.pi  -- S² = sphere
  | 4 => 2 * Real.pi^2  -- S³ = 3-sphere
  | _ => 2 * Real.pi^((d : ℝ)/2) / Real.Gamma ((d : ℝ)/2)  -- General formula

/-- The unit sphere volume matches the standard mathematical formula -/
theorem unitSphereVolume_eq_formula (d : ℕ) :
  unitSphereVolume d = 2 * Real.pi^((d : ℝ)/2) / Real.Gamma ((d : ℝ)/2) := by
  -- This can be proven using the ball volume formulas from Mathlib:
  -- InnerProductSpace.volume_ball shows volume(ball) = r^d * (√π)^d / Γ(d/2 + 1)
  -- The sphere surface area is then vol(S^{d-1}) = d * vol(unit ball) = 2π^{d/2} / Γ(d/2)
  -- For explicit cases d=1,2,3,4, we can use:
  -- Real.Gamma_one_half_eq, Real.Gamma_one, Real.Gamma_nat_add_half, etc.
  sorry

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

/-! ## Plancherel theorem for ℝᵈ -/

open MeasureTheory.Measure

variable {d : ℕ} [NeZero d]

-- Add inner product space structure
variable [Fintype (Fin d)]

/-- The Plancherel theorem in one dimension: The Fourier transform preserves the L² norm.

    For f : ℝ → ℂ integrable and in L², the Fourier transform 𝓕 f satisfies:
    ‖𝓕 f‖₂ = ‖f‖₂

    This uses Mathlib's eLpNorm which is the essential L^p norm. -/

-- this one is thanks to PhysLean
theorem plancherel_theorem_1d {f : ℝ → ℂ} (hf : Integrable f volume) (hf_mem : MemLp f 2) :
  eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  sorry

/-- The Plancherel theorem for ℝᵈ: generalization to d dimensions.

    For f : EuclideanSpace ℝ (Fin d) → ℂ integrable and in L², the Fourier transform preserves
    the L² norm. -/
theorem plancherel_theorem_d {f : EuclideanSpace ℝ (Fin d) → ℂ}
  (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin d))))
  (hf_mem : MemLp f 2) :
  eLpNorm (𝓕 f) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) =
  eLpNorm f 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  -- This is the d-dimensional generalization of the Plancherel theorem
  -- The proof would use the tensor product structure and iterate the 1D result
  sorry

/-- The Plancherel theorem implies the Fourier transform extends to an isometry on L² -/
theorem fourier_transform_isometry_on_L2 :
  ∃ (ℱ_L2 : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
    ∀ (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))), ‖ℱ_L2 f‖ = ‖f‖ := by
  -- This asserts the existence of the L² Fourier transform as a linear isometry
  -- The construction would use the Plancherel theorem and a completion argument
  sorry

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

/-! ## Plancherel theorem for ℝᵈ -/

open MeasureTheory.Measure

variable {d : ℕ} [NeZero d]

-- Add inner product space structure
variable [Fintype (Fin d)]

/-- The Plancherel theorem in one dimension: The Fourier transform preserves the L² norm.

    For f : ℝ → ℂ integrable and in L², the Fourier transform 𝓕 f satisfies:
    ‖𝓕 f‖₂ = ‖f‖₂

    This uses Mathlib's eLpNorm which is the essential L^p norm. -/

-- this one is thanks to PhysLean
theorem plancherel_theorem_1d' {f : ℝ → ℂ} (hf : Integrable f volume) (hf_mem : MemLp f 2) :
  eLpNorm (Real.fourierIntegral f) 2 volume = eLpNorm f 2 volume := by
  sorry

/-- The Plancherel theorem for ℝᵈ: generalization to d dimensions.

    For f : EuclideanSpace ℝ (Fin d) → ℂ integrable and in L², the Fourier transform preserves
    the L² norm. -/
theorem plancherel_theorem_d' {f : EuclideanSpace ℝ (Fin d) → ℂ}
  (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin d))))
  (hf_mem : MemLp f 2) :
  eLpNorm (Real.fourierIntegral f) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) =
  eLpNorm f 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  -- This is the d-dimensional generalization of the Plancherel theorem
  -- The proof would use the tensor product structure and iterate the 1D result
  sorry

/-- The Plancherel theorem implies the Fourier transform extends to an isometry on L² -/
theorem fourier_transform_isometry_on_L2' :
  ∃ (ℱ_L2 : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
    ∀ (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))), ‖ℱ_L2 f‖ = ‖f‖ := by
  -- This asserts the existence of the L² Fourier transform as a linear isometry
  -- The construction would use the Plancherel theorem and a completion argument
  sorry

/-! ## Fourier Transform as Linear Isometry on L² Spaces

The key challenge in defining the Fourier transform on L² spaces is that the Fourier integral
∫ f(x) e^(-2πi⟨x,ξ⟩) dx may not converge for arbitrary f ∈ L²(ℝᵈ).

**Construction Strategy (following the Schwartz space approach):**
1. **Dense Core**: Use Schwartz functions 𝒮(ℝᵈ) as the dense subset where Fourier integrals converge
2. **Schwartz Fourier**: Apply the Fourier transform on Schwartz space (unitary)
3. **Embedding to L²**: Embed Schwartz functions into L² space
4. **Plancherel on Core**: Show ‖ℱf‖₂ = ‖f‖₂ for f ∈ 𝒮(ℝᵈ)
5. **Extension**: Use the universal property of L² to extend to all of L²

This construction gives a unitary operator ℱ : L²(ℝᵈ) ≃ₗᵢ[ℂ] L²(ℝᵈ).
-/

variable {d : ℕ} [NeZero d] [Fintype (Fin d)]

-- Type abbreviations for clarity
abbrev EuclideanRd (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev SchwartzRd (d : ℕ) := SchwartzMap (EuclideanRd d) ℂ
abbrev L2Complex (d : ℕ) := Lp ℂ 2 (volume : Measure (EuclideanRd d))

/-! ### Core construction components (using Mathlib APIs) -/

/-- The Fourier transform on Schwartz space using Mathlib's fourierTransformCLE.
    This is a continuous linear equivalence ℂ-linear isomorphism on Schwartz functions.
    ✅ IMPLEMENTED: Uses SchwartzMap.fourierTransformCLE from Mathlib -/
noncomputable def fourierTransformSchwartz (d : ℕ) : SchwartzRd d ≃L[ℂ] SchwartzRd d :=
  -- This works directly since Mathlib infers the required NormedSpace ℂ structure
  SchwartzMap.fourierTransformCLE ℂ

/-- Embedding Schwartz functions into L² space using Mathlib's toLpCLM.
    This is a continuous linear map from Schwartz space to L²(ℝᵈ, ℂ).
    ✅ IMPLEMENTED: Uses SchwartzMap.toLpCLM from Mathlib -/
noncomputable def schwartzToL2 (d : ℕ) : SchwartzRd d →L[ℂ] L2Complex d :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanRd d))

/-! ### Mathematical properties for the construction -/

/-- Plancherel theorem on the Schwartz core -/
lemma plancherel_on_schwartz (d : ℕ) (f : SchwartzRd d) :
  ‖schwartzToL2 d (fourierTransformSchwartz d f)‖ = ‖schwartzToL2 d f‖ := by
  -- This follows from the fact that fourierTransformSchwartz is an isometry on Schwartz space
  -- The key insight is that both schwartzToL2 (fourier f) and schwartzToL2 f have the same L² norm
  -- because the Fourier transform preserves the L² norm of Schwartz functions

  -- We use the fact that SchwartzMap.fourierTransformCLE is isometric
  -- This is a consequence of the Plancherel theorem for Schwartz functions
  sorry -- TODO: This requires the Plancherel theorem for Schwartz functions from Mathlib

/-! ### Mathematical properties for the construction -/

/-- Injectivity: Schwartz functions that are zero a.e. are zero everywhere -/
lemma schwartzToL2_injective (d : ℕ) :
  Function.Injective (schwartzToL2 d) := by
  -- Since Schwartz functions are continuous, if they are zero a.e., they are zero
  sorry

/-- Density: Schwartz functions are dense in L² -/
lemma schwartzToL2_denseRange (d : ℕ) :
  DenseRange (schwartzToL2 d) := by
  -- This is a standard result: 𝒮(ℝᵈ) ⊆ L²(ℝᵈ) and 𝒮 is dense in L²
  sorry

/-- Well-definedness on the range: equal L² functions have equal Fourier transforms -/
lemma fourierTransform_welldefined_on_range (d : ℕ) {f g : SchwartzRd d}
    (h : schwartzToL2 d f = schwartzToL2 d g) :
    schwartzToL2 d (fourierTransformSchwartz d f) = schwartzToL2 d (fourierTransformSchwartz d g) := by
  -- Using injectivity of schwartzToL2, h implies f = g
  have f_eq_g : f = g := schwartzToL2_injective d h
  rw [f_eq_g]

/-! ### The main construction -/

/-- The dense subspace of L² consisting of Schwartz functions -/
def SchwartzSubspace (d : ℕ) : Submodule ℂ (L2Complex d) := LinearMap.range (schwartzToL2 d)

/-- The Fourier transform on the dense Schwartz subspace as a linear isometry -/
noncomputable def fourierTransformOnSchwartz (d : ℕ) : SchwartzSubspace d →ₗᵢ[ℂ] L2Complex d := by
  -- This constructs the isometry on the range of schwartzToL2
  -- Each element ψ ∈ SchwartzSubspace has form ψ = schwartzToL2 f for some f ∈ Schwartz
  -- We define the map as ψ ↦ schwartzToL2 (fourierTransformSchwartz f)
  classical
  -- The detailed construction uses classical choice and the well-definedness lemma
  exact sorry

/-- The extended Fourier transform to all of L² using the extension theorem -/
noncomputable def fourierTransformL2 : L2Complex d ≃ₗᵢ[ℂ] L2Complex d := by
  -- This follows the construction pattern from tests/plancherel.lean:
  -- 1. Define Fourier on Schwartz space (dense subset)
  -- 2. Show it's well-defined and isometric on the dense subset
  -- 3. Extend to all of L² using density and completeness
  -- 4. Construct the inverse similarly
  -- 5. Show the extended maps are inverses

  -- The concrete implementation would use:
  -- - SchwartzMap.fourierTransformCLE for Schwartz-level Fourier transform
  -- - SchwartzMap.toLpCLM for embedding Schwartz into L²
  -- - LinearIsometry.extend for the extension step
  -- - Density of Schwartz functions in L²
  -- - Plancherel theorem on Schwartz functions

  exact sorry -- TODO: Implement using the pattern from tests/plancherel.lean

/-- The forward Fourier transform as a continuous linear map -/
noncomputable def fourierTransformCLM : L2Complex d →L[ℂ] L2Complex d :=
  fourierTransformL2.toLinearIsometry.toContinuousLinearMap

/-- The inverse Fourier transform as a continuous linear map -/
noncomputable def inverseFourierTransformCLM : L2Complex d →L[ℂ] L2Complex d :=
  fourierTransformL2.symm.toLinearIsometry.toContinuousLinearMap

/-- The Fourier transform preserves L² norms -/
theorem fourierTransform_norm_preserving (f : L2Complex d) :
  ‖fourierTransformCLM f‖ = ‖f‖ :=
  fourierTransformL2.norm_map f

/-- The Fourier transform is invertible -/
theorem fourierTransform_left_inv (f : L2Complex d) :
  inverseFourierTransformCLM (fourierTransformCLM f) = f :=
  fourierTransformL2.left_inv f

theorem fourierTransform_right_inv (f : L2Complex d) :
  fourierTransformCLM (inverseFourierTransformCLM f) = f :=
  fourierTransformL2.right_inv f

/-- The Fourier transform is linear -/
theorem fourierTransform_linear (a b : ℂ) (f g : L2Complex d) :
  fourierTransformCLM (a • f + b • g) = a • fourierTransformCLM f + b • fourierTransformCLM g := by
  rw [map_add, map_smul, map_smul]

/-! ## Construction Details and Implementation Notes

The construction of `fourierTransformL2` follows the standard functional analysis approach:

### Dense Subset Strategy
We use Schwartz functions as our dense subset because:
- The Fourier integral ∫ f(x) e^(-2πi⟨x,ξ⟩) dx converges absolutely
- These functions are dense in L²(ℝᵈ)
- The Plancherel theorem applies directly

### Extension Technique
The key insight is that if T : D → H is a linear map from a dense subset D ⊆ H₁
to a complete space H₂, and ‖Tx‖ ≤ C‖x‖ for all x ∈ D, then T extends uniquely
to a bounded linear map T̃ : H₁ → H₂ with ‖T̃‖ ≤ C.

For the Fourier transform:
- D = 𝒮(ℝᵈ) (Schwartz functions)
- H₁ = H₂ = L²(ℝᵈ)
- ‖Tf‖₂ = ‖f‖₂ (Plancherel), so C = 1

### Implementation Roadmap
1. **Immediate**: Fill in the `sorry` proofs for density and extension
2. **Next**: Connect with pointwise fourierIntegral for explicit computations
3. **Future**: Add convolution theorems, derivative properties, etc.

This provides the mathematical foundation for the Fourier isometry used in
the QFT Hilbert space framework.
-/
