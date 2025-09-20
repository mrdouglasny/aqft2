/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## Gaussian Free Field via Kolmogorov Extension (Hermite-ready skeleton)

We construct a centered Gaussian field by Kolmogorov extension from
finite-dimensional Gaussian marginals. To avoid decidable-equality issues on the
full Schwartz space, we index coordinates by an abstract type ι with
[DecidableEq ι], together with a family of Schwartz test functions Φ : ι → S.

For each finite J : Finset ι, define the centered Gaussian on (↥J → ℝ) with
covariance matrix Σ(i,j) = freeCovarianceFormR m (Φ i) (Φ j). Then apply the
Kolmogorov extension theorem to obtain a probability measure on (ι → ℝ).

This file sets up the skeleton; key steps are left as sorries to be filled.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace

import Aqft2.Basic
import Aqft2.Covariance
import KolmogorovExtension4

open Classical
open MeasureTheory Complex Matrix

namespace GFFK

/-- A convenient countable multi-index for d-dimensional Hermite tensors. -/
abbrev HermiteIndex (d : ℕ) := (Fin d → ℕ)

section Setup

variable (ι : Type*) [DecidableEq ι]
variable (Φ : ι → SchwartzMap SpaceTime ℝ)
variable (m : ℝ) [NeZero m]

/-!
## Finite-dimensional layer over a finite index set J ⊂ ι
-/

/-- Covariance matrix on `↥J` using `freeCovarianceFormR` and the family `Φ`. -/
noncomputable def covMatrix (J : Finset ι) : Matrix (↥J) (↥J) ℝ :=
  Matrix.of (fun i j => freeCovarianceFormR m (Φ i.1) (Φ j.1))

/-- Positive semidefiniteness of the covariance matrix. -/
lemma covMatrix_posSemidef (J : Finset ι) : (covMatrix (ι:=ι) (Φ:=Φ) (m:=m) J).PosSemidef := by
  -- TODO: derive from positivity of freeCovarianceFormR
  sorry

/-- Centered multivariate Gaussian on `(↥J → ℝ)` with covariance `covMatrix J`. -/
noncomputable def finiteDimGaussian (J : Finset ι) : Measure (↥J → ℝ) := by
  -- TODO: build via Mathlib's multivariate Gaussian on EuclideanSpace and identify `(↥J → ℝ)`
  sorry

/-- Finite measure instance (indeed a probability) for the finite-dimensional Gaussian. -/
instance (J : Finset ι) : IsFiniteMeasure (finiteDimGaussian (ι:=ι) (Φ:=Φ) (m:=m) J) := by
  -- TODO: show this is a probability measure
  sorry

/-!
## Projective family and Kolmogorov extension
-/

/-- The projective family of finite-dimensional marginals. -/
noncomputable def projectiveFamily : ∀ J : Finset ι, Measure (↥J → ℝ) :=
  fun J => finiteDimGaussian (ι:=ι) (Φ:=Φ) (m:=m) J

/-- Consistency under coordinate restriction (Gaussian marginals). -/
lemma projectiveFamily_consistent :
    MeasureTheory.IsProjectiveMeasureFamily (projectiveFamily (ι:=ι) (Φ:=Φ) (m:=m)) := by
  -- TODO: pushforward along restrictions ↥J → ↥H yields the smaller Gaussian
  sorry

/-- Kolmogorov extension: the infinite-product Gaussian measure with given marginals. -/
noncomputable def gffMeasure : Measure (ι → ℝ) :=
  MeasureTheory.projectiveLimit (projectiveFamily (ι:=ι) (Φ:=Φ) (m:=m))
    (projectiveFamily_consistent (ι:=ι) (Φ:=Φ) (m:=m))

/-- The resulting measure is a probability measure. -/
instance : IsProbabilityMeasure (gffMeasure (ι:=ι) (Φ:=Φ) (m:=m)) := by
  -- TODO: apply KolmogorovExtension4 probability instance when marginals are probabilities
  sorry

end Setup

/-!
## Specialization to Hermite indices

Choose ι = HermiteIndex d and let Φ enumerate tensor-product Hermite functions.
We keep Φ abstract here; once provided, `gffMeasureHermite` gives the GFF law.
-/

noncomputable def gffMeasureHermite (d : ℕ)
    (ΦH : HermiteIndex d → SchwartzMap SpaceTime ℝ) (m : ℝ) [NeZero m] :
    Measure ((HermiteIndex d) → ℝ) :=
  gffMeasure (ι:=HermiteIndex d) (Φ:=ΦH) (m:=m)

end GFFK
