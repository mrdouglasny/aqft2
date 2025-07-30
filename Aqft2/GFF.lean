/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Gaussian free fields.

A GFF is a probabi  sorry

enda Hilbert space, with Boltzmann
weight the exponential of a quadratic energy functional.
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

import Aqft2.Basic
import Aqft2.OS_Axioms


open RCLike Real Filter Topology ComplexConjugate Finsupp Bornology
open LinearMap (BilinForm)
open MeasureTheory InnerProductSpace ProbabilityTheory QFT

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
  /-- The action functional -/
  action : F → ℝ := quadratic_action A J

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

/-- The PDF of the GFF is related to the exponential of the action -/
lemma GFF_pdf_eq_exp_action
  {𝕜 : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [IsHilbert 𝕜 F]
  {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (abstract_field : AbstractFreeField 𝕜 F)
  (GFF : GaussianFreeField Ω abstract_field) :
  ∀ f, Real.exp (-abstract_field.action f) =
    ENNReal.toReal (ProbabilityTheory.gaussianPDF
      (-RCLike.re ⟪abstract_field.CovOp abstract_field.J, f⟫_𝕜)
      (Real.toNNReal (RCLike.re ⟪abstract_field.CovOp f, f⟫_𝕜)) f) :=
sorry

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
    (∀ n J, GJAxiom_OS0 n J dμ) ∧
    GJAxiom_OS1 dμ ∧
    GJAxiom_OS2 dμ ∧
    GJAxiom_OS3 dμ ∧
    GJAxiom_OS4 dμ := by
  sorry

end
