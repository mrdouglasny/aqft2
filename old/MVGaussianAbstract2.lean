/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Simplified Abstract Multivariate Gaussian analyticity for normed spaces.

This provides a simplified version of MVGaussianAbstract.lean that only requires
NormedAddCommGroup (no inner product structure) and focuses on the core case
needed for GFF3.lean: Gaussian generating functionals of the form exp(-(1/2) * B(f, f)).
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-! ## Helper lemmas for finite sum analyticity -/

lemma analyticOn_finsum {k : Type*} [Fintype k] {α : Type*} [Fintype α]
  {f : α → (k → ℂ) → ℂ} {s : Set (k → ℂ)}
  (h : ∀ a, AnalyticOn ℂ (f a) s) :
  AnalyticOn ℂ (fun t => ∑ a, f a t) s := by
  have h_eq : (fun t => ∑ a, f a t) = (∑ a, f a) := by
    funext t
    simp [Finset.sum_apply]
  rw [h_eq]
  exact Finset.analyticOn_sum Finset.univ (fun a _ => h a)

/-! ## Quadratic form analyticity for normed spaces -/

/-- A quadratic form is analytic as a function of complex linear combinations.
    This requires only normed space structure, not inner product. -/
theorem simple_quadratic_form_analytic
    (B : E →L[ℂ] E →L[ℂ] ℂ) -- Continuous bilinear form
    (n : ℕ) (f : Fin n → E) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      B (∑ i, z i • f i) (∑ j, z j • f j)) Set.univ := by

  -- Coordinate projections are analytic
  have coord_analytic : ∀ (k : Fin n), AnalyticOn ℂ (fun z : Fin n → ℂ => z k) Set.univ := by
    intro k
    let proj : (Fin n → ℂ) →L[ℂ] ℂ := {
      toFun := fun z => z k
      map_add' := fun x y => by simp [Pi.add_apply]
      map_smul' := fun c x => by simp [Pi.smul_apply]
    }
    exact ContinuousLinearMap.analyticOn proj Set.univ

  -- Monomials z_i * z_j are analytic
  have monomial_analytic : ∀ (i j : Fin n), AnalyticOn ℂ (fun z : Fin n → ℂ => z i * z j) Set.univ := by
    intro i j
    exact AnalyticOn.mul (coord_analytic i) (coord_analytic j)

  -- Terms z_i * z_j * c are analytic
  have term_analytic : ∀ (i j : Fin n) (c : ℂ), AnalyticOn ℂ (fun z : Fin n → ℂ => c * z i * z j) Set.univ := by
    intro i j c
    have h_rearrange : (fun z : Fin n → ℂ => c * z i * z j) =
                       (fun z => c * (z i * z j)) := by
      funext z; ring
    rw [h_rearrange]
    exact AnalyticOn.mul analyticOn_const (monomial_analytic i j)

  -- The bilinear form B(∑ i, z i • f i, ∑ j, z j • f j) expands by bilinearity to
  -- ∑ i, ∑ j, z i * z j * B(f i, f j), which is analytic by finite sums
  have h_expansion : (fun z : Fin n → ℂ => B (∑ i, z i • f i) (∑ j, z j • f j)) =
                     (fun z => ∑ i, ∑ j, z i * z j * B (f i) (f j)) := by
    funext z
    -- Expand using bilinearity
    sorry

  rw [h_expansion]

  -- Apply finite sum analyticity
  apply analyticOn_finsum
  intro i
  apply analyticOn_finsum
  intro j
  -- Each term z i * z j * B(f i, f j) is analytic
  have h_reorder : (fun z : Fin n → ℂ => z i * z j * B (f i) (f j)) =
                   (fun z => B (f i) (f j) * z i * z j) := by
    funext z; ring
  rw [h_reorder]
  exact term_analytic i j (B (f i) (f j))

/-! ## Simplified Gaussian generating functional analyticity -/

/-- Simplified Gaussian generating functional for normed spaces.
    This represents functionals of the form exp(-(1/2) * B(f, f))
    without requiring inner product structure. -/
def simpleGaussianMGF
    (B : E →L[ℂ] E →L[ℂ] ℂ) -- Symmetric bilinear form
    (f : E) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * B f f)

/-- The simplified Gaussian MGF is entire in complex linear combinations.
    This is the key theorem for GFF3.lean and similar applications. -/
theorem simpleGaussianMGF_complex_combinations_entire
    (B : E →L[ℂ] E →L[ℂ] ℂ) -- Symmetric bilinear form
    (n : ℕ) (f : Fin n → E) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      simpleGaussianMGF B (∑ i, z i • f i)) Set.univ := by
  unfold simpleGaussianMGF
  -- exp(-(1/2) * B(∑ z_i • f_i, ∑ z_j • f_j))
  apply AnalyticOn.cexp
  apply AnalyticOn.mul
  · -- The constant -(1/2) is analytic
    exact analyticOn_const
  · -- B(∑ z_i • f_i, ∑ z_j • f_j) is a quadratic form in z, hence analytic
    exact simple_quadratic_form_analytic B n f

/-! ## Main theorem -/

/-- The main theorem: Simplified Gaussian generating functionals are entire.
    This provides the foundation for proving OS0 analyticity in QFT frameworks
    without requiring inner product structure. -/
theorem simple_gaussian_generating_functional_entire
    (B : E →L[ℂ] E →L[ℂ] ℂ) -- Symmetric bilinear form
    (n : ℕ) (f : Fin n → E) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      Complex.exp (-(1/2 : ℂ) * B (∑ i, z i • f i) (∑ i, z i • f i))) Set.univ :=
  simpleGaussianMGF_complex_combinations_entire B n f

end
