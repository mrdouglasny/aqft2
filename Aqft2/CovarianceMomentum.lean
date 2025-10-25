/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

# Momentum Space Propagator for Gaussian Free Field

This file implements the momentum space free propagator 1/(‖k‖²+m²) and its properties.
This is the foundation for the free covariance function in position space, which is computed
via Fourier transform.

## Main Definitions

- `freePropagatorMomentum`: Momentum space propagator 1/(‖k‖²+m²)
- `freeCovariance`: Position space covariance via Fourier transform
- `freeCovarianceKernel`: Alternative name for compatibility
- `propagatorMultiplication`: Linear operator for multiplication by propagator

## Key Results

- `freePropagator_even`: Propagator is an even function
- `freeCovariance_symmetric`: Covariance is symmetric C(x,y) = C(y,x)
- `freePropagator_smooth`, `freePropagator_complex_smooth`: Smoothness results
- `freePropagator_temperate_growth`: Temperate growth for Schwartz space theory
- `schwartz_mul_by_temperate`: Multiplication preserves Schwartz space
- `freePropagator_pos`, `freePropagator_bounded`: Propagator is positive and bounded
- `propagatorMultiplication_positive`: Propagator multiplication is a positive operator
- `propagatorMultiplication_bounded_schwartz`: L²-boundedness on Schwartz functions
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- Import our basic definitions
import Aqft2.Basic
import Aqft2.QFTHilbertSpace
import Aqft2.Euclidean
import Aqft2.DiscreteSymmetry
import Aqft2.Schwinger
import Aqft2.FunctionalAnalysis

open MeasureTheory Complex Real Filter
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

noncomputable section
/-! ### Small helper lemmas for integration and complex algebra -/

/-- Helper theorem: conjugate times itself equals `normSq` as a complex number. -/
theorem conj_mul_self_normSq (z : ℂ) :
  (starRingEnd ℂ z) * z = (Complex.normSq z : ℂ) := by
  -- Direct calculation: conj(a + bi) * (a + bi) = a² + b²
  cases' z with a b
  -- Manual calculation
  -- starRingEnd ℂ on {re := a, im := b} gives {re := a, im := -b}
  have h1 : starRingEnd ℂ { re := a, im := b } = { re := a, im := -b } := by rfl
  rw [h1]
  -- Now calculate {re := a, im := -b} * {re := a, im := b}
  -- Use the fact that for complex numbers, equality holds if real and imaginary parts match
  apply Complex.ext
  · -- Real parts: a*a + (-b)*b = a² + b² = Complex.normSq { re := a, im := b }
    simp only [Complex.mul_re, Complex.ofReal_re]
    -- Expand Complex.normSq application
    simp only [Complex.normSq_apply]
    ring
  · -- Imaginary parts: a*b + (-b)*a = 0
    simp only [Complex.mul_im, Complex.ofReal_im]
    ring

/-- Helper theorem: integral of a real-valued function, coerced to ℂ, equals `ofReal` of the real integral. -/
theorem integral_ofReal_eq {α} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
  (hf : Integrable h μ) :
  ∫ x, (h x : ℂ) ∂μ = Complex.ofReal (∫ x, h x ∂μ) := by
  -- Use the fact that continuous linear maps commute with integrals
  exact (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integral_comp_comm hf

/-- Helper theorem: nonnegativity of the real integral of a pointwise nonnegative, integrable function. -/
theorem real_integral_nonneg_of_nonneg
  {α} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
  (hf : Integrable h μ) (hpos : ∀ x, 0 ≤ h x) :
  0 ≤ ∫ x, h x ∂μ := by
  -- The integrability ensures the integral is well-defined
  have := hf  -- Acknowledge we need integrability for the integral to exist
  exact MeasureTheory.integral_nonneg hpos

/-- Helper lemma: Schwartz functions are L²-integrable. -/
lemma schwartz_L2_integrable (f : TestFunctionℂ) :
  Integrable (fun k => ‖f k‖^2) volume := by
  -- Using Mathlib's `SchwartzMap.memLp` we know any Schwartz function lies in every `L^p` space.
  have hf_memLp : MemLp f 2 volume :=
    f.memLp 2 volume
  have hf_meas : AEStronglyMeasurable f volume := hf_memLp.1
  -- Translate the `L^2` membership into integrability of the squared norm.
  simpa using (memLp_two_iff_integrable_sq_norm hf_meas).1 hf_memLp

/-- Helper theorem: Integrability is preserved by multiplying a real integrand with a real constant. -/
theorem integral_const_mul {α} [MeasurableSpace α] (μ : Measure α) (c : ℝ)
  (f : α → ℝ) (hf : Integrable f μ) :
  Integrable (fun x => c * f x) μ := by
  exact MeasureTheory.Integrable.const_mul hf c

/-- Helper theorem: Integral of a real constant multiple pulls out of the integral. -/
theorem integral_const_mul_eq {α} [MeasurableSpace α] (μ : Measure α) (c : ℝ)
  (f : α → ℝ) (hf : Integrable f μ) :
  ∫ x, c * f x ∂ μ = c * ∫ x, f x ∂ μ := by
  -- The integrability assumption ensures both integrals are well-defined
  have := hf  -- Acknowledge we need integrability for the integral to be well-defined
  exact MeasureTheory.integral_const_mul c f

/-- Helper theorem: Monotonicity of the real integral for pointwise ≤ between nonnegative functions,
    assuming the larger one is integrable. -/
theorem real_integral_mono_of_le
  {α} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
  (hg : Integrable g μ) (hf_nonneg : ∀ x, 0 ≤ f x) (hle : ∀ x, f x ≤ g x) :
  ∫ x, f x ∂ μ ≤ ∫ x, g x ∂ μ := by
  exact MeasureTheory.integral_mono_of_nonneg (ae_of_all _ hf_nonneg) hg (ae_of_all _ hle)

/-! ## Free Covariance in Euclidean QFT

The free covariance is the fundamental two-point correlation function for the Gaussian Free Field.
In Euclidean spacetime, it is given by the Fourier transform:

C(x,y) = ∫ (d^d k)/(2π)^d * 1/(k² + m²) * exp(-i k·(x-y))

where:
- m > 0 is the mass parameter
- k² = k·k is the Euclidean norm squared (using inner product ⟨k,k⟩)
- d is the spacetime dimension

This defines a positive definite bilinear form, which is essential for reflection positivity.

Key point: In Lean, we can use ⟨x, y⟩ for the inner product and ‖x‖ for the norm.
-/

variable {m : ℝ} [Fact (0 < m)]

/-- The free propagator in momentum space: 1/(k² + m²)
    This is the Fourier transform of the free covariance -/
def freePropagatorMomentum (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / (‖k‖^2 + m^2)

/-- The free propagator is an even function: it depends only on ‖k‖. -/
lemma freePropagator_even (m : ℝ) (k : SpaceTime) :
    freePropagatorMomentum m (-k) = freePropagatorMomentum m k := by
  unfold freePropagatorMomentum
  simp only [norm_neg]

/-- The free covariance kernel in position space.
    This is the Fourier transform of the momentum space propagator:

    C(x,y) = ∫ \frac{d^d k}{(2π)^d}\; \frac{e^{-i k·(x-y)}}{‖k‖² + m²}.

    We realise this as the real part of a complex Fourier integral with the
    standard 2π-normalisation. -/
noncomputable def freeCovariance (m : ℝ) (x y : SpaceTime) : ℝ :=
  let normalisation : ℝ := (2 * Real.pi) ^ STDimension
  let phase : SpaceTime → ℂ := fun k =>
    Complex.exp (-Complex.I * Complex.ofReal (⟪k, x - y⟫_ℝ))
  let amplitude : SpaceTime → ℂ := fun k =>
    Complex.ofReal (freePropagatorMomentum m k / normalisation)
  (∫ k : SpaceTime, amplitude k * phase k).re

/-- The free covariance kernel (alternative name for compatibility) -/
noncomputable def freeCovarianceKernel (m : ℝ) (z : SpaceTime) : ℝ :=
  freeCovariance m 0 z

/-- Negation as a linear isometry equivalence on SpaceTime. -/
def negSpaceTime : SpaceTime ≃ₗᵢ[ℝ] SpaceTime where
  toLinearEquiv := LinearEquiv.neg ℝ
  norm_map' := norm_neg

/-- Helper lemma: Integral with change of variables k ↦ -k for SpaceTime.
    This uses that linear isometries preserve measure on finite-dimensional inner product spaces. -/
theorem integral_comp_neg_spacetime {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : SpaceTime → E) : ∫ k, f (-k) = ∫ k, f k := by
  have h := (LinearIsometryEquiv.measurePreserving negSpaceTime).integral_comp
    negSpaceTime.toHomeomorph.measurableEmbedding f
  simpa using h

/-- Position-space free covariance is symmetric: `C(x,y) = C(y,x)`. -/
lemma freeCovariance_symmetric (m : ℝ) (x y : SpaceTime) :
    freeCovariance m x y = freeCovariance m y x := by
  -- Symmetry follows from:
  -- 1. The propagator is even: freePropagator_even shows freePropagatorMomentum m (-k) = freePropagatorMomentum m k
  -- 2. Change of variables k ↦ -k in the integral (using measure-preserving properties)
  -- 3. Using exp(-i k·(x-y)) with k ↦ -k gives exp(-i (-k)·(x-y)) = exp(i k·(x-y)) = exp(-i k·(y-x))
  unfold freeCovariance
  simp only [inner_sub_right]
  congr 1
  -- Need to show: ∫ k, f(k) * exp(-i(⟪k,x⟫ - ⟪k,y⟫)) = ∫ k, f(k) * exp(-i(⟪k,y⟫ - ⟪k,x⟫))
  -- Key insight: ⟪k,x⟫ - ⟪k,y⟫ = -(⟪k,y⟫ - ⟪k,x⟫), so the exponents differ by sign
  -- We use change of variables k ↦ -k and freePropagator_even: f(-k) = f(k)

  -- First, simplify using that ⟪k,y⟫ - ⟪k,x⟫ = -(⟪k,x⟫ - ⟪k,y⟫)
  have h_neg : ∀ k, (⟪k, y⟫_ℝ - ⟪k, x⟫_ℝ : ℂ) = -(⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ) := by
    intro k
    simp [neg_sub]

  -- Rewrite the RHS: exp(-i·(⟪k,y⟫ - ⟪k,x⟫)) = exp(i·(⟪k,x⟫ - ⟪k,y⟫))
  have h_exp_rhs : ∀ k, cexp (-I * ↑(⟪k, y⟫_ℝ - ⟪k, x⟫_ℝ)) = cexp (I * ↑(⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ)) := by
    intro k
    congr 1
    push_cast
    ring

  simp_rw [h_exp_rhs]

  -- Now need: ∫ k, f(k) * exp(-i·α) = ∫ k, f(k) * exp(i·α)
  -- Strategy: Show that substituting k ↦ -k on the RHS gives the LHS
  -- This uses: f(-k) = f(k) and ⟪-k, x-y⟫ = -⟪k, x-y⟫

  -- Key observation: exp(i·⟪-k, x-y⟫) = exp(-i·⟪k, x-y⟫)
  have h_inner_neg : ∀ k, (⟪-k, x⟫_ℝ - ⟪-k, y⟫_ℝ : ℂ) = -(⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ) := by
    intro k
    simp [inner_neg_left]
    ring

  -- The integrand on RHS with k ↦ -k equals the integrand on LHS
  have h_integrand_eq : ∀ k,
      (freePropagatorMomentum m (-k) / (2 * π) ^ STDimension : ℂ) * cexp (I * ↑(⟪-k, x⟫_ℝ - ⟪-k, y⟫_ℝ)) =
      (freePropagatorMomentum m k / (2 * π) ^ STDimension : ℂ) * cexp (-I * ↑(⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ)) := by
    intro k
    simp only [freePropagator_even]
    congr 1
    congr 1
    simp only [inner_neg_left]
    push_cast
    ring

  -- Apply change of variables k ↦ -k to the RHS using integral_comp_neg_euclidean
  -- RHS = ∫ k, f(k) * exp(i·α)
  -- After substitution k ↦ -k: RHS = ∫ k, f(-k) * exp(i·α(-k))
  -- By h_integrand_eq: f(-k) * exp(i·α(-k)) = f(k) * exp(-i·α)
  -- So RHS = ∫ k, f(k) * exp(-i·α) = LHS

  conv_rhs => rw [← integral_comp_neg_spacetime]
  -- Both sides are now of the form: ∫ k, (integrand at k)
  -- We need to show the integrands are equal
  congr 1
  funext k
  -- Normalize the casts on both sides
  push_cast
  -- Now use h_integrand_eq, pushing casts there too
  convert (h_integrand_eq k).symm using 2 <;> push_cast <;> rfl

/-- The position-space free covariance is real-valued after ℂ coercion. -/
@[simp] lemma freeCovariance_star (m : ℝ) (x y : SpaceTime) :
  star (freeCovariance m x y : ℂ) = (freeCovariance m x y : ℂ) := by
  simp

/-- Hermiticity of the complex-lifted position-space kernel. -/
@[simp] lemma freeCovariance_hermitian (m : ℝ) (x y : SpaceTime) :
  (freeCovariance m x y : ℂ) = star (freeCovariance m y x : ℂ) := by
  -- symmetry plus real-valuedness
  simp [freeCovariance_symmetric m x y]

/-- The free propagator function is smooth (infinitely differentiable). -/
lemma freePropagator_smooth (m : ℝ) [Fact (0 < m)] :
  ContDiff ℝ (⊤ : ℕ∞) (fun k => freePropagatorMomentum m k) := by
  -- The function k ↦ 1/(‖k‖² + m²) is smooth as a composition of smooth functions
  unfold freePropagatorMomentum
  apply ContDiff.div
  · -- The numerator 1 is smooth (constant)
    exact contDiff_const
  · -- The denominator ‖k‖² + m² is smooth
    apply ContDiff.add
    · exact contDiff_norm_sq ℝ
    · exact contDiff_const
  · -- The denominator is never zero
    intro k
    apply ne_of_gt
    apply add_pos_of_nonneg_of_pos
    · exact sq_nonneg ‖k‖
    · exact pow_pos (Fact.out : 0 < m) 2

/-- The complex-valued free propagator function is smooth. -/
lemma freePropagator_complex_smooth (m : ℝ) [Fact (0 < m)] :
  ContDiff ℝ (⊤ : ℕ∞) (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) := by
  have : (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) =
         (fun x : ℝ => (x : ℂ)) ∘ (fun k => freePropagatorMomentum m k) := rfl
  rw [this]
  apply ContDiff.comp
  · exact ofRealCLM.contDiff
  · exact freePropagator_smooth m

/-- Helper axiom: Derivatives of the free propagator have polynomial growth bounds.
   -/
axiom iteratedFDeriv_freePropagator_polynomial_bound (m : ℝ) (hm : 0 < m) (n : ℕ) :
  ∀ k : SpaceTime,
    ‖iteratedFDeriv ℝ n (fun k => (freePropagatorMomentum m k : ℂ)) k‖ ≤
      (n + 1).factorial / m^(n + 2)

/-- The propagator multiplier has temperate growth as a scalar function.
    This follows from the fact that it's bounded and smooth. -/
theorem freePropagator_temperate_growth (m : ℝ) [Fact (0 < m)] :
  Function.HasTemperateGrowth (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) := by
  constructor
  · -- Smoothness follows from our helper lemma
    exact freePropagator_complex_smooth m
  · -- Polynomial bounds on derivatives
    intro n
    -- The axiom gives us a constant bound (n+1)!/m^(n+2) (independent of k)
    -- For HasTemperateGrowth, we use polynomial degree 0 (constant bound)
    use 0, (n + 1).factorial / m^(n + 2)
    intro k
    simp only [pow_zero, mul_one]
    have hm : 0 < m := Fact.out
    exact iteratedFDeriv_freePropagator_polynomial_bound m hm n k

/-- Multiplication by a temperate scalar function preserves Schwartz space.
    This follows from SchwartzMap.bilinLeftCLM in Mathlib. -/
theorem schwartz_mul_by_temperate
  (a : SpaceTime → ℂ) (ha : Function.HasTemperateGrowth a) :
  ∃ (T : TestFunctionℂ →L[ℂ] TestFunctionℂ), ∀ f k, T f k = a k * f k := by
  -- Use the swap of multiplication to get a k * f k instead of f k * a k
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := (ContinuousLinearMap.mul ℂ ℂ).flip
  let T := SchwartzMap.bilinLeftCLM B ha
  use T
  intro f k
  -- T f k = B (f k) (a k) = (flip mul) (f k) (a k) = a k * f k
  rfl

/-- The free propagator is positive -/
lemma freePropagator_pos {m : ℝ} [Fact (0 < m)] (k : SpaceTime) : 0 < freePropagatorMomentum m k := by
  unfold freePropagatorMomentum
  apply div_pos
  · norm_num
  · apply add_pos_of_nonneg_of_pos
    · exact sq_nonneg ‖k‖
    · exact pow_pos (Fact.out : 0 < m) 2

/-- The free propagator is bounded above by 1/m² -/
lemma freePropagator_bounded {m : ℝ} [Fact (0 < m)] (k : SpaceTime) :
  freePropagatorMomentum m k ≤ 1 / m^2 := by
  unfold freePropagatorMomentum
  -- Since ‖k‖² ≥ 0, we have ‖k‖² + m² ≥ m², so 1/(‖k‖² + m²) ≤ 1/m²
  apply div_le_div_of_nonneg_left
  · norm_num
  · exact pow_pos (Fact.out : 0 < m) 2
  · apply le_add_of_nonneg_left
    exact sq_nonneg ‖k‖

/-- The free propagator is continuous -/
lemma freePropagator_continuous {m : ℝ} [Fact (0 < m)] :
  Continuous (freePropagatorMomentum m) := by
  -- This follows from continuity of the norm function and division
  -- since the denominator ‖k‖² + m² is never zero
  unfold freePropagatorMomentum
  apply Continuous.div
  · exact continuous_const
  · apply Continuous.add
    · exact continuous_norm.pow 2
    · exact continuous_const
  · intro k
    apply ne_of_gt
    apply add_pos_of_nonneg_of_pos
    · exact sq_nonneg ‖k‖
    · exact pow_pos (Fact.out : 0 < m) 2


-- Note: The propagator is not globally L¹ in d ≥ 2, but it is integrable on every closed ball.

-- (Integrability facts for the propagator on bounded sets can be added here if/when needed.)


/-- For large momentum, the free propagator behaves like 1/‖k‖² -/
lemma freePropagator_asymptotic {m : ℝ} [Fact (0 < m)] (k : SpaceTime) (hk : ‖k‖ ≥ m) :
  freePropagatorMomentum m k ≤ 1 / ‖k‖^2 := by
  unfold freePropagatorMomentum
  -- For ‖k‖ ≥ m, we have ‖k‖² + m² ≥ ‖k‖², so 1/(‖k‖² + m²) ≤ 1/‖k‖²
  apply div_le_div_of_nonneg_left
  · norm_num
  · have h_pos : 0 < ‖k‖ := lt_of_lt_of_le (Fact.out : 0 < m) hk
    exact pow_pos h_pos 2
  · apply le_add_of_nonneg_right
    exact sq_nonneg m

/-! ## Linear Operators via Propagator Multiplication -/

/-- Multiplication by the free propagator as a linear map on functions -/
def propagatorMultiplication (m : ℝ) : (SpaceTime → ℂ) →ₗ[ℂ] (SpaceTime → ℂ) := {
  toFun := fun f k => (freePropagatorMomentum m k : ℂ) * f k
  map_add' := fun f g => by ext k; simp [mul_add]
  map_smul' := fun c f => by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
}

/-- The propagator multiplication is a positive operator:
    For any function f, the L² inner product ⟨f, Pf⟩ ≥ 0 where P is propagator multiplication -/
theorem propagatorMultiplication_positive {m : ℝ} [Fact (0 < m)]
    (f : SpaceTime → ℂ)
    (hf : Integrable (fun k => freePropagatorMomentum m k * Complex.normSq (f k)) volume) :
  0 ≤ (∫ k, (starRingEnd ℂ (f k)) * (propagatorMultiplication m f k) ∂volume).re := by
  -- This expands to ∫ |f(k)|² * (1/(k²+m²)) dk ≥ 0
  -- which is positive since both |f(k)|² ≥ 0 and 1/(k²+m²) > 0
  -- Define the real nonnegative integrand h
  set h : SpaceTime → ℝ := fun k => freePropagatorMomentum m k * Complex.normSq (f k)
  -- Rewrite the complex integrand as (h k : ℂ)
  have h_point (k : SpaceTime) :
      (starRingEnd ℂ (f k)) * (propagatorMultiplication m f k)
        = (h k : ℂ) := by
    -- Algebraic rearrangement and conj-mul identity
    have hswap :
        (starRingEnd ℂ (f k)) * ((freePropagatorMomentum m k : ℂ) * f k)
          = (freePropagatorMomentum m k : ℂ) * ((starRingEnd ℂ (f k)) * f k) := by
      simp [mul_left_comm, mul_comm, mul_assoc]
    have hconj : (starRingEnd ℂ (f k)) * f k = (Complex.normSq (f k) : ℂ) := by

      simpa using conj_mul_self_normSq (f k)
    -- Put it together and coerce the real product to ℂ
    have : (starRingEnd ℂ (f k)) * ((freePropagatorMomentum m k : ℂ) * f k)
        = (Complex.ofReal (freePropagatorMomentum m k * Complex.normSq (f k))) := by
      simp [hswap, hconj, Complex.ofReal_mul]
    simpa [h] using this
  -- Convert integral of complex ofReal to real integral
  -- First, replace the integrand by the equal function (h k : ℂ)
  have hfun_eq :
      (fun k => (starRingEnd ℂ (f k)) * (propagatorMultiplication m f k))
        = fun k => (h k : ℂ) := by
    funext k; simpa [propagatorMultiplication] using h_point k
  -- Equality of integrals by function equality
  have hint_eq :
      ∫ k, (starRingEnd ℂ (f k)) * (propagatorMultiplication m f k) ∂volume
        = ∫ k, (h k : ℂ) ∂volume := by
    simp [hfun_eq]
  -- Now apply the ofReal integral identity using the integrability hypothesis
  have h_ofReal : ∫ k, (h k : ℂ) ∂volume = Complex.ofReal (∫ k, h k ∂volume) :=
    integral_ofReal_eq (μ := volume) (h := h) hf
  have h_integral :
      ∫ k, (starRingEnd ℂ (f k)) * (propagatorMultiplication m f k) ∂volume
        = Complex.ofReal (∫ k, h k ∂volume) := by
    simpa [hint_eq] using h_ofReal
  -- Take real part; real part of ofReal is identity
  have h_re_eq : (∫ k, (starRingEnd ℂ (f k)) * (propagatorMultiplication m f k) ∂volume).re
           = ∫ k, h k ∂volume := by
    simp [h_integral]
  -- The real integrand h is nonnegative pointwise
  -- Conclude by nonnegativity of the real integral using pointwise nonnegativity
  have h_int_nonneg : 0 ≤ ∫ k, h k ∂volume :=
    real_integral_nonneg_of_nonneg (μ := volume) (h := h) hf
      (fun k => by
        have h₁ : 0 ≤ freePropagatorMomentum m k := le_of_lt (freePropagator_pos (m := m) k)
        have h₂ : 0 ≤ Complex.normSq (f k) := Complex.normSq_nonneg _
        exact mul_nonneg h₁ h₂)
  simpa [h_re_eq] using h_int_nonneg

/-- For Schwartz functions on ℝ^d, multiplication by the (real, nonnegative) propagator
    g(k) = 1/(‖k‖² + m²) is L²-bounded with operator norm ≤ sup g = 1/m².

    In L² form: ∫ ‖g·f‖² ≤ (sup g)² ∫ ‖f‖² = (1/m²)² ∫ ‖f‖². -/
theorem propagatorMultiplication_bounded_schwartz {m : ℝ} [Fact (0 < m)] (f : TestFunctionℂ) :
  ∃ C > 0, ∫ k, ‖propagatorMultiplication m f k‖^2 ∂volume ≤ C * ∫ k, ‖f k‖^2 ∂volume := by
  -- Choose the sharp L² constant C = (sup_k g(k))² = (1/m²)².
  have mpos : 0 < m := Fact.out
  have m2pos : 0 < m^2 := pow_pos mpos 2
  refine ⟨((m^2)^2)⁻¹, ?_, ?_⟩
  · -- C > 0
    have : 0 < (m^2)^2 := pow_pos m2pos 2
    exact inv_pos.mpr this
  · -- Pointwise bound: ‖(g(k):ℂ)·f(k)‖² ≤ (sup g)² · ‖f(k)‖² with sup g = 1/m².
    -- Then integrate both sides.
    -- g(k) as a real scalar
    have h_pointwise : ∀ k,
        ‖propagatorMultiplication m f k‖^2 ≤ (1 / m^2)^2 * ‖f k‖^2 := by
      intro k
      -- norm of scalar multiplication
      have hmul_norm : ‖propagatorMultiplication m f k‖
            = ‖(freePropagatorMomentum m k : ℂ)‖ * ‖f k‖ := by
        simp [propagatorMultiplication]
      -- square both sides and expand
      have hsq_eq : ‖propagatorMultiplication m f k‖^2
            = (‖(freePropagatorMomentum m k : ℂ)‖)^2 * ‖f k‖^2 := by
        have := congrArg (fun t : ℝ => t^2) hmul_norm
        -- (ab)^2 = a^2 b^2
        simpa [mul_pow] using this
      -- identify the scalar norm with the real value
      have h_nonneg : 0 ≤ freePropagatorMomentum m k := le_of_lt (freePropagator_pos (m := m) k)
      have hnorm : ‖(freePropagatorMomentum m k : ℂ)‖ = freePropagatorMomentum m k := by
        have h1 : ‖(freePropagatorMomentum m k : ℂ)‖ = |freePropagatorMomentum m k| := by
          simp
        have h2 : |freePropagatorMomentum m k| = freePropagatorMomentum m k := abs_of_nonneg h_nonneg
        exact h1.trans h2
      -- use the scalar upper bound and square it
      have hsup : freePropagatorMomentum m k ≤ 1 / m^2 := freePropagator_bounded (m := m) k
      have habs : |freePropagatorMomentum m k| ≤ |(1 / m^2)| := by
        have hpos : 0 < 1 / m^2 := div_pos one_pos (pow_pos (Fact.out : 0 < m) 2)
        simpa [abs_of_nonneg h_nonneg, abs_of_pos hpos] using hsup
      have hsq_scalar : (freePropagatorMomentum m k)^2 ≤ (1 / m^2)^2 := (sq_le_sq.mpr habs)
      -- conclude inequality by multiplying with ‖f k‖^2 ≥ 0
      have : (‖(freePropagatorMomentum m k : ℂ)‖)^2 ≤ (1 / m^2)^2 := by
        simpa [hnorm] using hsq_scalar
      have hnonneg_fk : 0 ≤ ‖f k‖^2 := by exact sq_nonneg _
      have hmul_le : (‖(freePropagatorMomentum m k : ℂ)‖)^2 * ‖f k‖^2 ≤ (1 / m^2)^2 * ‖f k‖^2 :=
        mul_le_mul_of_nonneg_right this hnonneg_fk
      -- rewrite LHS via hsq_eq
      simpa [hsq_eq] using hmul_le
    -- Integrate the pointwise inequality; conclude the L² bound
    -- Define the real-valued functions to integrate
    let F : SpaceTime → ℝ := fun k => ‖propagatorMultiplication m f k‖^2
    let G : SpaceTime → ℝ := fun k => ((m^2)^2)⁻¹ * ‖f k‖^2
    have hF_nonneg : ∀ k, 0 ≤ F k := by intro k; exact sq_nonneg _
    have hFG_le : ∀ k, F k ≤ G k := by
      intro k
      have hconst_eq : (1 / m^2 : ℝ)^2 = ((m^2)^2)⁻¹ := by
        -- rewrite both sides to a common normal form
        simp [one_div, pow_two]
      -- reconcile constants via hconst_eq
      simpa [F, G, propagatorMultiplication, hconst_eq] using h_pointwise k
    -- G is integrable since Schwartz functions are L² and constants preserve integrability
    have h_int_G : Integrable G volume := by
      have hL2 : Integrable (fun k => ‖f k‖^2) volume := schwartz_L2_integrable f
      -- use helper
      simpa [G] using
        (integral_const_mul (μ := volume) (((m^2)^2)⁻¹) (fun k => ‖f k‖^2) hL2)
    -- Monotonicity of the integral gives the desired inequality
    have hInt :=
      real_integral_mono_of_le (μ := volume) F G h_int_G hF_nonneg hFG_le
    -- Rearrange constants to match the statement using equality of integrals for constant multiples
    have h_step1 : ∫ k, ‖propagatorMultiplication m f k‖^2 ∂volume ≤ ∫ k, G k ∂volume := by
      -- rewrite the left side to match F
      change ∫ k, (fun k => ‖propagatorMultiplication m f k‖^2) k ∂volume ≤ ∫ k, G k ∂volume
      exact hInt
    have hG_eq : ∫ k, G k ∂volume = ((m^2)^2)⁻¹ * ∫ k, ‖f k‖^2 ∂volume := by
      have hL2 : Integrable (fun k => ‖f k‖^2) volume := schwartz_L2_integrable f
      simpa [G] using
        (integral_const_mul_eq (μ := volume) (((m^2)^2)⁻¹) (fun k => ‖f k‖^2) hL2)
    -- Final inequality
    calc
      ∫ k, ‖propagatorMultiplication m f k‖^2 ∂volume ≤ ∫ k, G k ∂volume := h_step1
  _ = ((m^2)^2)⁻¹ * ∫ k, ‖f k‖^2 ∂volume := hG_eq

/-! ## Momentum Space Positivity Structure -/

/-- Key structural lemma: The momentum space representation makes positivity manifest.
    This encapsulates the essence of why reflection positivity works for the free field.
-/
theorem momentum_space_positivity_structure (m : ℝ) [Fact (0 < m)] :
  -- The key insight: In momentum space, integrals become
  -- ∫ |f̂(k)|² * (1/(k² + m²)) dk which is positive since:
  -- 1. |f̂(k)|² ≥ 0 (complex norm squared)
  -- 2. 1/(k² + m²) > 0 (freePropagator_pos)
  -- This theorem establishes the general principle for arbitrary functions
  ∀ (f : SpaceTime → ℂ) (_hf_integrable : Integrable (fun k => ‖f k‖^2 * freePropagatorMomentum m k) volume),
    0 ≤ ∫ k, ‖f k‖^2 * freePropagatorMomentum m k ∂volume := by
  -- This establishes the fundamental structural insight of momentum space reflection positivity:
  -- The complex, non-obvious positivity condition in position space becomes manifestly
  -- positive in momentum space due to the factorization into non-negative components.
  --
  -- Mathematical principle: The Fourier transform converts reflection positivity into
  -- an integral of the form ∫ |f̂(k)|² * (positive weight) dk, which is transparently ≥ 0.
  -- This is the essence of why momentum space methods are so powerful in constructive QFT.
  intro f _hf_integrable

  -- The integrand ‖f k‖^2 * freePropagatorMomentum m k is pointwise non-negative:
  -- 1. ‖f k‖^2 ≥ 0 for all k (norm squared is always non-negative)
  -- 2. freePropagatorMomentum m k > 0 for all k (from freePropagator_pos)
  -- Therefore their product is non-negative everywhere
  have h_nonneg : ∀ᵐ k, 0 ≤ ‖f k‖^2 * freePropagatorMomentum m k := by
    apply Filter.Eventually.of_forall
    intro k
    have h1 : 0 ≤ ‖f k‖^2 := sq_nonneg ‖f k‖
    have h2 : 0 ≤ freePropagatorMomentum m k := le_of_lt (freePropagator_pos k)
    exact mul_nonneg h1 h2

  -- Since the integrand is non-negative almost everywhere,
  -- the integral is non-negative by the fundamental theorem of integration
  exact integral_nonneg_of_ae h_nonneg

/-- Helper lemma: For any L² function f, the integral ∫ |f(k)|² * (1/(k²+m²)) dk ≥ 0.
    This is the key positivity result that makes reflection positivity manifest in momentum space.
-/
theorem momentum_space_integral_positive {m : ℝ} [Fact (0 < m)] (f : SpaceTime → ℂ)
  (hf_integrable : Integrable (fun k => ‖f k‖^2 * freePropagatorMomentum m k) volume) :
  0 ≤ ∫ k, ‖f k‖^2 * freePropagatorMomentum m k ∂volume := by
  -- This is a direct application of the momentum space positivity structure theorem
  -- which establishes that integrals of the form ∫ |f(k)|² * (1/(k²+m²)) dk are non-negative
  -- due to the factorization into manifestly non-negative components
  exact momentum_space_positivity_structure m f hf_integrable

/--  (Integrability for Schwartz Functions):**
    The product of the squared norm of a Schwartz function
    and the free propagator in momentum space is integrable. -/
axiom integrable_schwartz_weighted_by_propagator (m : ℝ) (f : TestFunctionℂ) :
  Integrable (fun k => ‖f k‖^2 * freePropagatorMomentum m k) volume

/-- Corollary: the momentum-space quadratic form is non-negative on Schwartz functions. -/
theorem momentum_space_integral_positive_schwartz {m : ℝ} [Fact (0 < m)] (f : TestFunctionℂ) :
  0 ≤ ∫ k, ‖f k‖^2 * freePropagatorMomentum m k ∂volume := by
  have hf_int := integrable_schwartz_weighted_by_propagator (m := m) (f := f)
  exact momentum_space_integral_positive (m := m) f hf_int

/-! ## Complex conjugation properties of the propagator -/

/-- The momentum-space propagator is real-valued: its star (complex conjugate) equals itself. -/
@[simp] lemma freePropagatorMomentum_star (m : ℝ) (k : SpaceTime) :
  star (freePropagatorMomentum m k : ℂ) = (freePropagatorMomentum m k : ℂ) := by
  simp

/-- Same statement via the star ring endomorphism (complex conjugate). -/
@[simp] lemma freePropagatorMomentum_starRing (m : ℝ) (k : SpaceTime) :
  (starRingEnd ℂ) (freePropagatorMomentum m k : ℂ) = (freePropagatorMomentum m k : ℂ) := by
  simp

/-- In particular, the imaginary part of the momentum-space propagator vanishes. -/
@[simp] lemma freePropagatorMomentum_im (m : ℝ) (k : SpaceTime) :
  (freePropagatorMomentum m k : ℂ).im = 0 := by
  simp

/-- Pointwise hermiticity of the momentum-space integrand: taking star swaps f and g
    because the propagator is real-valued. -/
lemma momentum_integrand_hermitian
  (m : ℝ) (f g : SpaceTime → ℂ) (k : SpaceTime) :
  star ((star (f k)) * (freePropagatorMomentum m k : ℂ) * g k)
    = (star (g k)) * (freePropagatorMomentum m k : ℂ) * f k := by
  -- star distributes over products and `star (star (f k)) = f k`; the propagator is real
  simp [mul_comm, mul_assoc]

/-! ## Momentum-space covariance form -/

/-- Momentum-space covariance bilinear form (Fourier side). -/
noncomputable def momentumCovarianceForm (m : ℝ) (f g : SpaceTime → ℂ) : ℂ :=
  ∫ k, (star (f k)) * (freePropagatorMomentum m k : ℂ) * g k ∂volume

/-- Helper axiom: Complex conjugation commutes with integration for integrable functions -/
axiom integral_star_comm {f : SpaceTime → ℂ} (hf : Integrable f volume) :
  star (∫ k, f k ∂volume) = ∫ k, star (f k) ∂volume

/-- Helper axiom: The integrand in momentum covariance forms is integrable -/
axiom momentum_covariance_integrable (m : ℝ) (f g : SpaceTime → ℂ)
  (hf : Integrable f volume) (hg : Integrable g volume) :
  Integrable (fun k => (star (f k)) * (freePropagatorMomentum m k : ℂ) * g k) volume

/-- Hermiticity of the momentum-space covariance form.
    Under standard integrability assumptions, the star of the integral equals the
    integral of the starred integrand, which by `momentum_integrand_hermitian` swaps f and g. -/
lemma momentumCovarianceForm_hermitian (m : ℝ) (f g : SpaceTime → ℂ)
  (hf : Integrable f volume) (hg : Integrable g volume) :
  star (momentumCovarianceForm m f g) = momentumCovarianceForm m g f := by
  -- This proof uses the fundamental property that complex conjugation commutes with integration
  -- combined with the pointwise hermiticity property.

  unfold momentumCovarianceForm

  -- Step 1: Use the fact that star commutes with the integral
  have h_integrable := momentum_covariance_integrable m f g hf hg
  rw [integral_star_comm h_integrable]

  -- Step 2: Apply pointwise hermiticity under the integral
  congr 1
  ext k
  exact momentum_integrand_hermitian m f g k
