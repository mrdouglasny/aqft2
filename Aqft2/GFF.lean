/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Gaussian free fields.

A GFF is a probability distribution over a Hilbert space, with Boltzmann
weight the exponential of a quadratic energy functional.
This functinoal could be specified in various ways.
Here we take <v,Av> + i <J,v> where A is an invertible linear operator.

The source term should be implemented as a characteristic function.
Do we want the real linear term?  Probably yes.

What do we need to prove?  We define the Gaussian measure axiomatically,
then we should show that it exists?
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


open RCLike Real Filter Topology ComplexConjugate Finsupp Bornology

open LinearMap (BilinForm)
open MeasureTheory InnerProductSpace ProbabilityTheory

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (h : HilbertSpace 𝕜 E)

class IsHilbert (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : Prop where
  complete : CompleteSpace E

variable {𝕜 F : Type*} [ NormedAddCommGroup F] [InnerProductSpace ℝ F] [IsHilbert ℝ F]

def IsSymmetric (T : F →L[ℝ] F) : Prop :=
  ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ

/- these should all be class attributes -/
variable (A : F →L[ℝ] F) -- symmetric, positive-definite
variable [Invertible A] -- just for simplicity
variable (J : F)

def quadratic_action (A : F →L[ℝ] F) (J f : F) : ℝ :=
  ((1 : ℝ) / 2) • (⟪f, A f⟫_ℝ : ℝ) + (⟪J, f⟫_ℝ : ℝ)

structure AbstractGFF (A : F →L[ℝ] F) (J : F) where
  A := A
  J := J
  CovOp := A.inverse
  symmetric : IsSymmetric A
  positive : ∀ f, 0 ≤ ⟪A f, f⟫_ℝ
  action : F → ℝ := quadratic_action A J

structure GaussianFreeField
  (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω] [MeasureSpace Ω] [AddCommMonoid Ω]
  (S : AbstractGFF A J) where
  P : ProbabilityMeasure Ω
  apply : F → Ω → ℝ
  measurable : ∀ f, Measurable (apply f)
  gaussian : ∀ f, IsGaussian (P.toMeasure.map (apply f : Ω → ℝ))
  mean : ∀ f, ∫ ω, apply f ω ∂P.toMeasure = - ⟪S.CovOp S.J, f⟫_ℝ
  covariance : ∀ f g, ∫ ω, apply f ω * apply g ω ∂P.toMeasure = ⟪S.CovOp f, g⟫_ℝ

variable (S : AbstractGFF A J)
variable (Ω : Type*) [TopologicalSpace Ω] [MeasurableSpace Ω] [MeasureSpace Ω] [AddCommMonoid Ω]
variable (f : F)
#check ProbabilityTheory.gaussianPDF (- ⟪S.CovOp S.J, f⟫_ℝ) (Real.toNNReal ⟪S.CovOp f, f⟫_ℝ) (1:ℝ)
variable (GFF : GaussianFreeField A J Ω S)

/- let's prove that the pdf is the action -/

lemma GFF_pdf_eq_action (GFF : GaussianFreeField A J Ω S) :
  ∀ f,  (Real.exp (- S.action f)) = ENNReal.toReal ((ProbabilityTheory.gaussianPDF (- ⟪S.CovOp S.J, f⟫_ℝ)) (Real.toNNReal ⟪S.CovOp f, f⟫_ℝ) (1 : ℝ)) :=
  sorry

variable (CovOp : F →L[ℝ] F)

structure GaussianFreeField' where
  P : ProbabilityMeasure Ω
  apply : F → Ω → ℝ
  measurable : ∀ f, Measurable (apply f)
  gaussian : ∀ f, IsGaussian (P.toMeasure.map (apply f : Ω → ℝ))
  mean_zero : ∀ f, ∫ ω, apply f ω ∂P.toMeasure = 0
  covariance : ∀ f g, ∫ ω, apply f ω * apply g ω ∂P.toMeasure = ⟪CovOp f, g⟫_ℝ

/- the standard Gaussian measure -/

variable (n : ℕ)
def Rn := EuclideanSpace ℝ (Fin n)
#check MeasurableSpace (Rn n)

--abbrev μ : Measure (Rn n) := volume    -- Lebesgue, just named “μ”

--def stdGaussianMeasure (n : ℕ) : ProbabilityMeasure (Rn n) :=
--  ProbabilityMeasure.mk (gaussian n) (by simp [gaussian_apply_univ])
