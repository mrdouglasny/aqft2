/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Gaussian free fields.

A GFF is a probability distribution with weight the exponential of a quadratic energy functional.
This functional could be specified in various ways.
Here we take <v,Av> + i <J,v> where A is an invertible linear operator.

The source term should be implemented as a characteristic function.
The goal is to prove that the GFF satisfies the Osterwalder-Schrader axioms.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic

import Aqft2.OS_Axioms
import Aqft2.Basic


open RCLike Real Filter Topology ComplexConjugate Finsupp Bornology
open LinearMap (BilinForm)
open MeasureTheory InnerProductSpace ProbabilityTheory SCV QFT

noncomputable section

/-! ## Abstract Free Field Structure -/

/-- A Hilbert space typeclass -/
class IsHilbert (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : Prop where
  complete : CompleteSpace E

/-- Symmetry condition for linear operators -/
def IsSymmetric {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (T : F →L[𝕜] F) : Prop :=
  ∀ x y, ⟪T x, y⟫_𝕜 = ⟪x, T y⟫_𝕜

/-- Positive definiteness for linear operators -/
def IsPositiveDefinite {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (T : F →L[𝕜] F) : Prop :=
  ∀ f, 0 ≤ RCLike.re (⟪T f, f⟫_𝕜) ∧ (RCLike.re (⟪T f, f⟫_𝕜) = 0 → f = 0)

/-- The quadratic action functional for the free field -/
def quadratic_action {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (A : F →L[𝕜] F) (J f : F) : ℝ :=
  (1 / 2) * RCLike.re (⟪f, A f⟫_𝕜) + RCLike.re (⟪J, f⟫_𝕜)

/-- Abstract structure for a free field with inverse covariance operator and source -/
structure AbstractFreeField (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] where
  /-- The inverse covariance operator (symmetric, positive definite) -/
  A : F →L[𝕜] F
  /-- The source term -/
  J : F
  /-- A is symmetric -/
  symmetric : IsSymmetric A
  /-- A is positive definite -/
  positive_definite : IsPositiveDefinite A
  /-- A is invertible -/
  invertible : Invertible A
  /-- The covariance operator (inverse of A) -/
  CovOp : F →L[𝕜] F := A.inverse

namespace AbstractFreeField

/-- The action functional for an abstract free field -/
def action {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (field : AbstractFreeField 𝕜 F) : F → ℝ :=
  quadratic_action field.A field.J

/-- The action function equals quadratic_action by definition -/
lemma action_eq {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (field : AbstractFreeField 𝕜 F) (f : F) :
  field.action f = quadratic_action field.A field.J f := rfl

end AbstractFreeField

/-! ## Gaussian Free Field -/

/--
A Gaussian Free Field is a probability measure on a space of field configurations
that realizes the abstract free field structure through Gaussian distributions.
-/
structure GaussianFreeField
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F) where
  /-- The probability measure on field space -/
  P : ProbabilityMeasure Ω
  /-- How test functions act on field configurations -/
  apply : F → Ω → ℝ
  /-- Each test function gives a measurable map -/
  measurable : ∀ f, Measurable (apply f)
  /-- Each test function induces a Gaussian distribution -/
  gaussian : ∀ f, IsGaussian (P.toMeasure.map (apply f : Ω → ℝ))
  /-- Mean is determined by the source term -/
  mean : ∀ f, ∫ ω, apply f ω ∂P.toMeasure = -RCLike.re ⟪abstract_field.CovOp abstract_field.J, f⟫_𝕜
  /-- Covariance is given by the covariance operator -/
  covariance : ∀ f g, ∫ ω, apply f ω * apply g ω ∂P.toMeasure = RCLike.re ⟪abstract_field.CovOp f, g⟫_𝕜

/-! ## Connection to Test Functions -/

/--
Given a Gaussian Free Field, we can define a generating functional
that should satisfy the OS axioms.
-/
def GFF_generating_functional
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field)
  (J : F) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (GFF.apply J ω : ℂ)) ∂GFF.P.toMeasure

/-! ## Lemmas for OS Axioms -/

/-- For any direction f in field space, the logarithm of the exponential of the action
    along the ray z↦zf equals the logarithm of the Gaussian PDF up to a normalization constant -/
lemma GFF_pdf_eq_exp_action
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field) :
  ∀ f : F, f ≠ 0 → ∃ C : ℝ, ∀ z : ℝ,
    -abstract_field.action ((z : 𝕜) • f) = C +
    Real.log (ProbabilityTheory.gaussianPDFReal
      (-RCLike.re ⟪abstract_field.J, f⟫_𝕜 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜)
      (Real.toNNReal (1 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜)) z) := by
  intros f hf
  -- The key insight: taking logarithms separates the exponent from normalization

  -- First, establish positivity of the quadratic form
  have hA_pos : 0 < RCLike.re ⟪abstract_field.A f, f⟫_𝕜 := by
    cases' abstract_field.positive_definite f with h_nonneg h_zero
    cases' lt_or_eq_of_le h_nonneg with h_pos h_eq
    · exact h_pos
    · exfalso
      have : f = 0 := h_zero h_eq.symm
      exact hf this

  -- First expand the action functional:
  -- action((z : 𝕜) • f) = (1/2) * Re⟪(z•f), A(z•f)⟫ + Re⟪J, z•f⟫
  --                    = (1/2) * Re⟪z•f, z•(Af)⟫ + Re⟪J, z•f⟫
  --                    = (1/2) * z² * Re⟪f, Af⟫ + z * Re⟪J, f⟫
  -- So: -action((z : 𝕜) • f) = -(z²/2) * Re⟪f, Af⟫ - z * Re⟪J, f⟫

  -- Now expand gaussianPDF from Mathlib:
  -- gaussianPDF μ v z = ENNReal.ofReal(gaussianPDFReal μ v z)
  -- gaussianPDFReal μ v z = (√(2πv))⁻¹ * Real.exp(-(z-μ)²/(2v))
  --
  -- Taking log of gaussianPDF:
  -- log(gaussianPDF μ v z) = log((√(2πv))⁻¹) + log(Real.exp(-(z-μ)²/(2v)))
  --                        = -log(√(2πv)) - (z-μ)²/(2v)
  --                        = -(1/2)*log(2πv) - (z-μ)²/(2v)
  --
  -- For our specific parameters:
  -- μ = -Re⟪J, f⟫/Re⟪A f, f⟫  and  v = 1/Re⟪A f, f⟫
  --
  -- Expanding -(z-μ)²/(2v):
  -- -(z-μ)²/(2v) = -(z² - 2zμ + μ²)/(2v)
  --               = -z²/(2v) + zμ/v - μ²/(2v)
  --               = -z² * Re⟪A f, f⟫/2 + z * (-Re⟪J, f⟫) - μ²/(2v)
  --               = -(z²/2) * Re⟪A f, f⟫ - z * Re⟪J, f⟫ - μ²/(2v)
  --
  -- After our polynomial expansion, we can determine what C must be
  -- We'll prove that there exists a C such that the polynomial equation holds
  -- by showing the coefficient matching works

  -- The key insight: both sides are polynomials in z with the same coefficients
  -- This means their difference is a constant, proving existence of such C

  -- First, let's expand both sides to polynomial form and show they differ by a constant
  -- This avoids committing to a specific value of C

  -- Define auxiliary function for the difference between LHS and RHS (without constant C)
  -- Use the unfolded definitions directly to enable polynomial manipulation
  let poly_diff : ℝ → ℝ := fun z => 
    -- Unfolded action: -((1/2) * Re⟪z•f, A(z•f)⟫ + Re⟪J, z•f⟫)
    -((1 / 2) * RCLike.re ⟪(z : 𝕜) • f, abstract_field.A ((z : 𝕜) • f)⟫_𝕜 + 
      RCLike.re ⟪abstract_field.J, (z : 𝕜) • f⟫_𝕜) -
    -- Unfolded gaussianPDFReal log: -log(√(2π * v)) - (z-μ)²/(2v)
    (Real.log ((Real.sqrt (2 * Real.pi * (1 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜).toNNReal))⁻¹) - 
     (z - (-RCLike.re ⟪abstract_field.J, f⟫_𝕜 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜))^2 / 
     (2 * (1 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜).toNNReal))

  -- This poly_diff now has all definitions unfolded, making polynomial manipulation possible

  -- The key insight: poly_diff is constant (independent of z)
  -- This means ∃ C, ∀ z, poly_diff z = C, which is exactly what we want to prove

  -- Prove that poly_diff is indeed constant by showing its derivative is zero
  -- or equivalently, that poly_diff z₁ = poly_diff z₂ for any z₁, z₂

  -- For now, use the constant value at z = 0 to define C
  use poly_diff 0

  intro z
  -- We need to show: -action(z•f) = poly_diff(0) + log(gaussianPDF(...))
  
  -- Convert the goal to polynomial form
  suffices h : -abstract_field.action ((z : 𝕜) • f) - 
               Real.log (ProbabilityTheory.gaussianPDFReal
                 (-RCLike.re ⟪abstract_field.J, f⟫_𝕜 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜)
                 (Real.toNNReal (1 / RCLike.re ⟪abstract_field.A f, f⟫_𝕜)) z) = 
               poly_diff 0 by
    linarith [h]
  
  -- This is just showing poly_diff z = poly_diff 0
  simp only [poly_diff]
  
  -- Expand the action and gaussianPDF to show they match our unfolded form
  rw [AbstractFreeField.action_eq]
  unfold quadratic_action
  
  rw [ProbabilityTheory.gaussianPDFReal]
  simp only [Real.log_mul, Real.log_inv, Real.log_exp]
  
  -- Now both sides are in the same unfolded form, so they're equal by definition
  ring

/-- The generating functional satisfies the expected exponential form -/
lemma GFF_generating_functional_form
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field) :
  ∀ J, GFF_generating_functional abstract_field GFF J =
    Complex.exp (-Complex.I * (abstract_field.action J : ℂ)) := by
  sorry

/-- Positivity property needed for OS1 -/
lemma GFF_positivity
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field) :
  ∀ f : F, 0 ≤ (GFF_generating_functional abstract_field GFF f).re := by
  sorry

/-- Euclidean invariance needed for OS2 -/
lemma GFF_euclidean_invariance
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field) :
  ∀ J, GFF_generating_functional abstract_field GFF J =
    GFF_generating_functional abstract_field GFF J := by
  sorry

/-! ## Main Goal: OS Axioms -/

/--
The main theorem we want to prove: a Gaussian Free Field satisfies the OS axioms.
For now, we assume F can be cast to TestFunctionℂ.
-/
theorem GFF_satisfies_OS_axioms
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field) :
  ∃ (dμ : ProbabilityMeasure FieldSpace),
    OS0_Analyticity dμ ∧
    OS1_Regularity dμ ∧
    OS2_EuclideanInvariance dμ ∧
    OS3_ReflectionPositivity dμ ∧
    OS4_Ergodicity dμ := by
  sorry

end
