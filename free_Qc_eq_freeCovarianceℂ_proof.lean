/-
Working file for proving free_Qc_eq_freeCovarianceℂ

This is extracted from GFFMconstruct.lean to allow incremental development
without blocking the main build.

Goal: Prove that MinlosAnalytic.Qc (freeCovarianceForm_struct m) f g = freeCovarianceℂ m f g

Strategy:
1. Both sides are ℂ-bilinear extensions of the same real form freeCovarianceFormR
2. Qc uses the canonical complexification formula:
   Qc(f,g) = Q(Re f, Re g) - Q(Im f, Im g) + i(Q(Re f, Im g) + Q(Im f, Re g))
3. freeCovarianceℂ is defined as ∫∫ f(x) · K(x,y) · star(g(y))
4. Expand f = re(f) + i·im(f), star(g) = re(g) - i·im(g) pointwise
5. Use freeCovarianceℂ_agrees_on_reals to convert each of 4 double integrals
6. Match with Qc formula

Key lemmas now available in Basic.lean:
- complex_testfunction_decompose_fst_apply: (decompose f).1 x = (f x).re
- complex_testfunction_decompose_snd_apply: (decompose f).2 x = (f x).im
- complex_testfunction_decompose_fst_apply_coe: ((decompose f).1 x : ℂ) = (f x).re
- complex_testfunction_decompose_snd_apply_coe: ((decompose f).2 x : ℂ) = (f x).im

Key lemma from Covariance.lean:
- freeCovarianceℂ_agrees_on_reals:
    freeCovarianceℂ m (toComplex f) (toComplex g) = (freeCovarianceFormR m f g : ℂ)
-/

import Aqft2.Basic
import Aqft2.Covariance
import Aqft2.MinlosAnalytic

open MeasureTheory Complex

noncomputable section

-- Copy the freeCovarianceForm_struct definition for reference
noncomputable def freeCovarianceForm_struct (m : ℝ) : MinlosAnalytic.CovarianceForm where
  Q := fun f g => freeCovarianceFormR m f g
  symm := by intro f g; simpa using freeCovarianceFormR_symm m f g
  psd := by intro f; simpa using freeCovarianceFormR_pos m f
  cont_diag := by
    simpa using freeCovarianceFormR_continuous m
  add_left := by
    intro f₁ f₂ g
    exact freeCovarianceFormR_add_left m f₁ f₂ g
  smul_left := by
    intro c f g
    exact freeCovarianceFormR_smul_left m c f g

/-- Working version of the bridge lemma -/
lemma free_Qc_eq_freeCovarianceℂ_working
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  MinlosAnalytic.Qc (freeCovarianceForm_struct m) f g = freeCovarianceℂ m f g := by

  -- Unfold Qc definition
  unfold MinlosAnalytic.Qc freeCovarianceForm_struct

  -- Decompose f and g into real and imaginary parts
  rcases complex_testfunction_decompose f with ⟨f_re, f_im⟩
  rcases complex_testfunction_decompose g with ⟨g_re, g_im⟩

  simp only []

  -- Goal: (Q(f_re, g_re) - Q(f_im, g_im) : ℝ) + I * (Q(f_re, g_im) + Q(f_im, g_re) : ℝ)
  --     = freeCovarianceℂ m f g
  show (freeCovarianceFormR m f_re g_re - freeCovarianceFormR m f_im g_im : ℝ) +
       Complex.I * (freeCovarianceFormR m f_re g_im + freeCovarianceFormR m f_im g_re : ℝ) =
       freeCovarianceℂ m f g

  -- Step 1: Establish pointwise equalities using the new simp lemmas
  -- These now work automatically thanks to the [simp] lemmas in Basic.lean
  have hf_re : ∀ x, (f_re x : ℂ) = ((f x).re : ℂ) := by simp
  have hf_im : ∀ x, (f_im x : ℂ) = ((f x).im : ℂ) := by simp
  have hg_re : ∀ x, (g_re x : ℂ) = ((g x).re : ℂ) := by simp
  have hg_im : ∀ x, (g_im x : ℂ) = ((g x).im : ℂ) := by simp

  -- Step 2: Use agreement-on-reals to convert integrals
  -- freeCovarianceℂ m (toComplex u) (toComplex v) = (freeCovarianceFormR m u v : ℂ)
  have h1 : freeCovarianceℂ m (toComplex f_re) (toComplex g_re) = (freeCovarianceFormR m f_re g_re : ℂ) :=
    freeCovarianceℂ_agrees_on_reals m f_re g_re
  have h2 : freeCovarianceℂ m (toComplex f_re) (toComplex g_im) = (freeCovarianceFormR m f_re g_im : ℂ) :=
    freeCovarianceℂ_agrees_on_reals m f_re g_im
  have h3 : freeCovarianceℂ m (toComplex f_im) (toComplex g_re) = (freeCovarianceFormR m f_im g_re : ℂ) :=
    freeCovarianceℂ_agrees_on_reals m f_im g_re
  have h4 : freeCovarianceℂ m (toComplex f_im) (toComplex g_im) = (freeCovarianceFormR m f_im g_im : ℂ) :=
    freeCovarianceℂ_agrees_on_reals m f_im g_im

  -- Step 3: Expand freeCovarianceℂ m f g using pointwise decomposition
  unfold freeCovarianceℂ

  -- Rewrite f and star(g) pointwise
  have hf_decomp : ∀ x, f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ) := by
    intro x
    exact (Complex.re_add_im (f x)).symm.trans (by ring)

  have hg_star_decomp : ∀ y, (starRingEnd ℂ) (g y) = ((g y).re : ℂ) - Complex.I * ((g y).im : ℂ) := by
    intro y
    simp only [starRingEnd_apply, RCLike.star_def]
    -- star z = conj z = re z - i * im z
    have : conj (g y) = (Complex.re (g y) : ℂ) - Complex.I * (Complex.im (g y) : ℂ) := by
      rw [← Complex.conj_eq_iff_re]
      simp [Complex.conj_ofReal]
      sorry -- Need to show conj z = re z - I * im z
    exact this

  -- Now we need to expand the integrand and match with the four terms
  -- This requires careful manipulation of the product expansion
  sorry

end
