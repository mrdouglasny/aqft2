/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Gaussian free fields.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic

open RCLike Real Filter Topology ComplexConjugate Finsupp Bornology

open LinearMap (BilinForm)
open MeasureTheory InnerProductSpace ProbabilityTheory

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (h : HilbertSpace 𝕜 E)

class IsHilbert (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : Prop where
  complete : CompleteSpace E

variable [ NormedAddCommGroup F] [InnerProductSpace ℝ F] [IsHilbert ℝ F]

variable (A : F →L[ℝ] F) -- symmetric, positive-definite
variable [Invertible A]  -- just for simplicity

noncomputable def CovOp : F →L[ℝ] F := A.inverse

structure AbstractGFF (F : Type*) [ NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] where
  cov : F → F → ℝ
  symm : ∀ f g, cov f g = cov g f
  pos_def : ∀ f, 0 ≤ cov f f
  linear_in_first : ∀ (a : ℝ) (f g h : F), cov (a • f + g) h = a * cov f h + cov g h

variable [TopologicalSpace Ω] [MeasurableSpace Ω] [MeasureSpace Ω] -- defines `volume : Measure Ω`
variable [AddCommMonoid Ω]
variable (CovOp : F →L[ℝ] F)

structure GaussianFreeField where
  P : ProbabilityMeasure Ω
  apply : F → Ω → ℝ
  measurable : ∀ f, Measurable (apply f)
  gaussian : ∀ f, IsGaussian (P.toMeasure.map (apply f : Ω → ℝ))
  mean_zero : ∀ f, ∫ ω, apply f ω ∂P.toMeasure = 0
  covariance : ∀ f g, ∫ ω, apply f ω * apply g ω ∂P.toMeasure = ⟪CovOp f, g⟫_ℝ
