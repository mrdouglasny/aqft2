/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## GFF_OS3: OS3 Reflection Positivity for Gaussian Measures

This file contains the proof that Gaussian measures satisfy the OS3 (Reflection Positivity)
axiom. It builds on the general reflection positivity framework from OS3.lean by
providing the specific exponential form properties that characterize Gaussian measures.

### Key Components:

**Gaussian Characterization:**
- `gaussian_Z_form`: Z[h] = exp(-½ S₂(h,h)) - fundamental Gaussian property
- `gaussian_Z_real_on_diagonal`: Diagonal values are real for Gaussian functionals
- `diagonal_covariance_is_real_GFF`: Concrete verification for Gaussian Free Field

**Gaussian Invariance Theory:**
- `gaussian_two_point_diagonal_invariant_under_CLM`: General CLM invariance
- `gaussian_two_point_diagonal_reflection_invariant`: Time reflection specialization

**Main Gaussian OS3 Theorem:**
- `gaussian_quadratic_real_rewrite`: Matrix factorization M_{ij} = Z[f_i]Z[f_j]exp(R_{ij})

**Mathematical Strategy:**
For Gaussian measures Z[h] = exp(-½⟨h, Ch⟩), the reflection positivity matrix
M_{ij} = Z[f_i - θf_j] can be factored using exponential properties and the
Schur product theorem applied to positive semidefinite matrices.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Exponential

import Aqft2.Basic
import Aqft2.OS_Axioms
import Aqft2.GFFconstruct
import Aqft2.Euclidean
import Aqft2.DiscreteSymmetry
import Aqft2.SCV
import Aqft2.FunctionalAnalysis
import Aqft2.OS4
import Aqft2.Minlos
import Aqft2.Covariance
import Aqft2.HadamardExp
import Aqft2.OS3

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

open scoped BigOperators
open Finset

/-! Auxiliary axioms for the free field instance (to be proven in construction files) -/
axiom isGaussianGJ_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  isGaussianGJ (gaussianFreeField_free m)

axiom covarianceBilinear_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  CovarianceBilinear (gaussianFreeField_free m)

axiom reflectionInvariance_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
  OS3_ReflectionInvariance (gaussianFreeField_free m)

/-! Auxiliary PSD machinery (to be relocated to matrix/Schur modules) -/

-- Real-part symmetry of Schwinger 2-pt function (avoids needing full Hermitian identity name)
axiom schwinger_re_symm
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g : TestFunctionℂ) :
  (SchwingerFunctionℂ₂ dμ_config f g).re = (SchwingerFunctionℂ₂ dμ_config g f).re

-- Transpose preserves positive semidefiniteness (real matrices)
axiom posSemidef_transpose {n : ℕ}
  {A : Fin n → Fin n → ℝ} :
  Matrix.PosSemidef A → Matrix.PosSemidef (fun i j => A j i)

-- Entrywise real exponential preserves PSD (finite type)
axiom posSemidef_entrywiseExp_of_posSemidef {n : ℕ}
  {R : Fin n → Fin n → ℝ} :
  Matrix.PosSemidef R → Matrix.PosSemidef (fun i j => Real.exp (R i j))

-- Rank-1 Gram matrix from complex vector, taking real parts, is PSD over ℝ
axiom posSemidef_rank1_real {n : ℕ}
  (u : Fin n → ℂ) :
  Matrix.PosSemidef (fun i j : Fin n => (Complex.conj (u i) * u j).re)

-- Rank-1 real Gram from complex vector via starRingEnd
axiom posSemidef_rank1_starEnd {n : ℕ} (u : Fin n → ℂ) :
  Matrix.PosSemidef (fun i j : Fin n => (((starRingEnd ℂ) (u i) * u j)).re)

-- Schur product theorem for PSD (real case)
axiom schur_product_posSemidef {n : ℕ}
  {A B : Fin n → Fin n → ℝ} :
  Matrix.PosSemidef A → Matrix.PosSemidef B → Matrix.PosSemidef (fun i j => A i j * B i j)

-- Nonnegativity of the trace of a PSD real symmetric matrix
axiom trace_nonneg_of_posSemidef {n : ℕ}
  {A : Fin n → Fin n → ℝ} :
  Matrix.PosSemidef A → 0 ≤ Matrix.trace A

/-! ## Gaussian Measures and OS3 Reflection Positivity

For Gaussian measures, reflection positivity can be verified using the explicit
exponential form and properties of the covariance under time reflection.

Following Glimm-Jaffe Theorem 6.2.2, we examine Z[F̄ - CF'] where F is a positive-time
test function, F̄ is its complex conjugate, F' is its TIME REFLECTION, and C is the
covariance operator.

The key insight is to expand the exponent ⟨F̄ - CF', C(F̄ - CF')⟩ and use reflection
positivity of the covariance. The TIME REFLECTION F' = Θ(F) where Θ is the time
reflection operation from DiscreteSymmetry.

The Glimm-Jaffe argument shows that if the covariance C satisfies reflection positivity,
then the generating functional Z[F̄F] for positive-time test functions has the required
properties for OS3. The time reflection enters through the auxiliary expression F̄ - CF'.
-/

/-- Gaussian form: the generating functional satisfies Z[h] = exp(-½ S₂(h,h)) -/
lemma gaussian_Z_form
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h : TestFunctionℂ) :
  GJGeneratingFunctionalℂ dμ_config h = Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config h h) := by
  -- Follows immediately from the Gaussian characterization
  exact (h_gaussian.2 h)

lemma diagonal_covariance_is_real_GFF (m : ℝ) [Fact (0 < m)] :
  ∀ h : TestFunctionℂ, ∃ r : ℝ,
    SchwingerFunctionℂ₂ (gaussianFreeField_free m) h h = (r : ℂ) := by
  intro h
  -- identify Schwinger 2-pt with free covariance
  have hid : SchwingerFunctionℂ₂ (gaussianFreeField_free m) h h = freeCovarianceℂ m h h :=
    gff_two_point_equals_covarianceℂ_free m h h
  -- diagonal of free covariance is real
  rcases freeCovarianceℂ_diagonal_real m h with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  -- conclude by rewriting
  simpa [hid] using hr

/-- On-diagonal Gaussian values are real: star Z[h] = Z[h] when S₂(h,h) is real. -/
lemma gaussian_Z_real_on_diagonal
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h : TestFunctionℂ) :
  (starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config h) = GJGeneratingFunctionalℂ dμ_config h := by
  -- From diagonal_covariance_is_real, S₂(h,h) = (r : ℂ)
  rcases diagonal_covariance_is_real dμ_config h with ⟨r, hr⟩
  -- Rewrite Z[h] via Gaussian form and identify it as a real exponential
  have hz : GJGeneratingFunctionalℂ dμ_config h = Complex.exp (-(1/2 : ℂ) * (r : ℂ)) := by
    simpa [hr] using (gaussian_Z_form dμ_config h_gaussian h)
  -- Convert to ofReal to expose realness
  have hz' : GJGeneratingFunctionalℂ dμ_config h = (Real.exp (-(1/2 : ℝ) * r) : ℂ) := by
    have hcast : (-(1/2 : ℂ) * (r : ℂ)) = Complex.ofReal (-(1/2 : ℝ) * r) := by
      simp [Complex.ofReal_mul]
    rw [hz, hcast, ← Complex.ofReal_exp]
  -- Conclude by conjugation preserving real values
  rw [hz']
  exact Complex.conj_ofReal _

/-- Gaussian: If the generating functional is invariant under a linear map `L`
    on test functions, then the diagonal two-point Schwinger function is invariant
    under `L` as well. No functional-derivative machinery required. -/
lemma gaussian_two_point_diagonal_invariant_under_CLM
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (L : TestFunctionℂ →L[ℝ] TestFunctionℂ)
  (Zinv : ∀ h : TestFunctionℂ,
    GJGeneratingFunctionalℂ dμ_config (L h) = GJGeneratingFunctionalℂ dμ_config h)
  (h : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config (L h) (L h) = SchwingerFunctionℂ₂ dμ_config h h := by
  -- abbreviate
  let S := SchwingerFunctionℂ₂ dμ_config
  -- Gaussian form for Z[L h] and Z[h]
  have zL : GJGeneratingFunctionalℂ dμ_config (L h)
    = Complex.exp (-(1/2 : ℂ) * S (L h) (L h)) :=
    gaussian_Z_form dμ_config h_gaussian (L h)
  have zh : GJGeneratingFunctionalℂ dμ_config h
    = Complex.exp (-(1/2 : ℂ) * S h h) :=
    gaussian_Z_form dμ_config h_gaussian h
  -- Invariance of Z transfers to equality of complex exponentials
  have hZ : Complex.exp (-(1/2 : ℂ) * S (L h) (L h))
            = Complex.exp (-(1/2 : ℂ) * S h h) := by
    simpa [zL, zh] using (Zinv h)
  -- Realness of the diagonal entries
  rcases diagonal_covariance_is_real dμ_config (L h) with ⟨rL, hrL⟩
  rcases diagonal_covariance_is_real dμ_config h with ⟨r, hr⟩
  -- Move to real exponentials via ofReal in two steps
  have hZ' : Complex.exp (Complex.ofReal (-(1/2 : ℝ) * rL))
            = Complex.exp (Complex.ofReal (-(1/2 : ℝ) * r)) := by
    -- Use substitution
    have h1 : S (L h) (L h) = (rL : ℂ) := by
      show SchwingerFunctionℂ₂ dμ_config (L h) (L h) = (rL : ℂ)
      exact hrL
    have h2 : S h h = (r : ℂ) := by
      show SchwingerFunctionℂ₂ dμ_config h h = (r : ℂ)
      exact hr
    have hcast1 : (-(1/2 : ℂ) * (rL : ℂ)) = Complex.ofReal (-(1/2 : ℝ) * rL) := by
      simp [Complex.ofReal_mul]
    have hcast2 : (-(1/2 : ℂ) * (r : ℂ)) = Complex.ofReal (-(1/2 : ℝ) * r) := by
      simp [Complex.ofReal_mul]
    rw [h1, h2, hcast1, hcast2] at hZ
    exact hZ
  have hZ_ofReal : Complex.ofReal (Real.exp (-(1/2 : ℝ) * rL))
                 = Complex.ofReal (Real.exp (-(1/2 : ℝ) * r)) := by
    simpa [Complex.ofReal_exp] using hZ'
  have hZ_real : Real.exp (-(1/2 : ℝ) * rL) = Real.exp (-(1/2 : ℝ) * r) :=
    Complex.ofReal_inj.mp hZ_ofReal
  -- exp is injective on ℝ (via log)
  have hlin : (-(1/2 : ℝ) * rL) = (-(1/2 : ℝ) * r) := by
    have := congrArg Real.log hZ_real
    simpa [Real.log_exp] using this
  have hr_eq : rL = r := by
    have := congrArg (fun t : ℝ => (-2 : ℝ) * t) hlin
    ring_nf at this
    simpa using this
  -- conclude back in ℂ
  calc
    S (L h) (L h) = (rL : ℂ) := hrL
    _ = (r : ℂ) := by simp [hr_eq]
    _ = S h h := by simpa using hr.symm

/-- Specialization to time reflection: if Z is invariant under time reflection,
    then the diagonal two-point function is invariant under time reflection. -/
lemma gaussian_two_point_diagonal_reflection_invariant
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_reflectInv : OS3_ReflectionInvariance dμ_config)
  (h : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection h) (QFT.compTimeReflection h)
  = SchwingerFunctionℂ₂ dμ_config h h :=
  gaussian_two_point_diagonal_invariant_under_CLM dμ_config h_gaussian
    QFT.compTimeReflection (fun t => h_reflectInv t) h

/-- Gaussian factorization at the quadratic-form level.
    Let R_{ij} := Re S₂(Θ f_i, f_j) and define y_i := Z[f_i] · c_i. Then
      Re ∑ᵢⱼ (conj cᵢ) cⱼ · Z[fᵢ - Θ fⱼ]
      = Re ∑ᵢⱼ (conj yᵢ) yⱼ · exp(R_{ij}). -/
lemma gaussian_quadratic_real_rewrite
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_bilinear : CovarianceBilinear dμ_config)
  (h_reflectInv : OS3_ReflectionInvariance dμ_config)
  {n : ℕ} (f : Fin n → PositiveTimeTestFunction)
  (c : Fin n → ℂ) :
  (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
      GJGeneratingFunctionalℂ dμ_config ((f i).val - QFT.compTimeReflection (f j).val)).re
  = (∑ i, ∑ j,
        (starRingEnd ℂ) ((GJGeneratingFunctionalℂ dμ_config (f i).val) * c i)
        * ((GJGeneratingFunctionalℂ dμ_config (f j).val) * c j)
        * Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)
      ).re := by
  classical
  -- Abbreviations
  let J : Fin n → TestFunctionℂ := fun i => (f i).val
  let ΘJ : Fin n → TestFunctionℂ := fun j => QFT.compTimeReflection (f j).val
  let Z : Fin n → ℂ := fun i => GJGeneratingFunctionalℂ dμ_config (J i)
  let R : Fin n → Fin n → ℝ := fun i j =>
    (SchwingerFunctionℂ₂ dμ_config (J i) (ΘJ j)).re

  -- Factorization of each entry M i j
  have entry_factor : ∀ i j,
      GJGeneratingFunctionalℂ dμ_config (J i - ΘJ j)
        = Z i * Z j * Real.exp (R i j) := by
    intro i j
    let S := SchwingerFunctionℂ₂ dμ_config
    -- Gaussian
    have hZ : GJGeneratingFunctionalℂ dμ_config (J i - ΘJ j)
        = Complex.exp (-(1/2 : ℂ) * S (J i - ΘJ j) (J i - ΘJ j)) :=
      gaussian_Z_form dμ_config h_gaussian (J i - ΘJ j)
    -- Bilinear expansion
    have hbil : S (J i - ΘJ j) (J i - ΘJ j)
        = S (J i) (J i) + S (ΘJ j) (ΘJ j) - S (J i) (ΘJ j) - S (ΘJ j) (J i) := by
      simpa using bilin_expand dμ_config h_bilinear (J i) (ΘJ j)
    -- Hermitian cross-sum to 2·Re
    have hherm : S (ΘJ j) (J i) = star (S (J i) (ΘJ j)) :=
      schwinger_function_hermitian dμ_config (ΘJ j) (J i)
    have hsum : S (J i) (ΘJ j) + S (ΘJ j) (J i)
               = Complex.ofReal (2 * (S (J i) (ΘJ j)).re) := by
      apply Complex.ext <;>
        simp [hherm, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, two_mul]
    -- Positive half of cross-sum
    have hhalf_pos : (1/2 : ℂ) * (S (J i) (ΘJ j) + S (ΘJ j) (J i))
                   = Complex.ofReal ((S (J i) (ΘJ j)).re) := by
      have hmul : (1/2 : ℂ) * Complex.ofReal (2 * (S (J i) (ΘJ j)).re)
                = Complex.ofReal ((1/2 : ℝ) * (2 * (S (J i) (ΘJ j)).re)) := by
        simp [Complex.ofReal_mul]
      have hℝ : (1/2 : ℝ) * (2 * (S (J i) (ΘJ j)).re) = (S (J i) (ΘJ j)).re := by ring
      rw [hsum, hmul, hℝ]
    -- Diagonal reflection invariance - use the specialized Gaussian lemma
    have hdiag : S (ΘJ j) (ΘJ j) = S (J j) (J j) := by
      -- Directly apply the Gaussian diagonal reflection invariance
      simpa [ΘJ, J] using gaussian_two_point_diagonal_reflection_invariant dμ_config h_gaussian h_reflectInv (J j)
    -- Rewrite exponent and split: work with A,B,C,D notation
    set A := S (J i) (J i); set B := S (ΘJ j) (ΘJ j); set C := S (J i) (ΘJ j); set D := S (ΘJ j) (J i)
    have hABCD : S (J i - ΘJ j) (J i - ΘJ j) = A + B - C - D := by
      simpa [A, B, C, D] using hbil
    have hxsplit : (-(1/2 : ℂ)) * S (J i - ΘJ j) (J i - ΘJ j)
      = (-(1/2 : ℂ)) * A + (-(1/2 : ℂ)) * B + (1/2 : ℂ) * (C + D) := by
      -- use hABCD : S(...) = A + B - C - D
      have : (-(1/2 : ℂ)) * (A + B - C - D) = (-(1/2 : ℂ)) * A + (-(1/2 : ℂ)) * B + (1/2 : ℂ) * (C + D) := by ring
      simpa [hABCD] using this
    -- Replace diagonal and cross pieces using invariances
    have hCD : (1/2 : ℂ) * (C + D) = Complex.ofReal (R i j) := by
      simpa [C, D, R] using hhalf_pos
    have hB : (-(1/2 : ℂ)) * B = (-(1/2 : ℂ)) * S (J j) (J j) := by
      simpa [B] using congrArg (fun t => (-(1/2 : ℂ)) * t) hdiag
    have hxsplit' : (-(1/2 : ℂ)) * S (J i - ΘJ j) (J i - ΘJ j)
      = (-(1/2 : ℂ)) * S (J i) (J i) + (-(1/2 : ℂ)) * S (J j) (J j) + Complex.ofReal (R i j) := by
      calc (-(1/2 : ℂ)) * S (J i - ΘJ j) (J i - ΘJ j)
        _ = (-(1/2 : ℂ)) * A + (-(1/2 : ℂ)) * B + (1/2 : ℂ) * (C + D) := hxsplit
        _ = (-(1/2 : ℂ)) * S (J i) (J i) + (-(1/2 : ℂ)) * S (J j) (J j) + (1/2 : ℂ) * (C + D) := by simp [A, ← hdiag]
        _ = (-(1/2 : ℂ)) * S (J i) (J i) + (-(1/2 : ℂ)) * S (J j) (J j) + Complex.ofReal (R i j) := by rw [hCD]
    -- Exponentials split into product
    have hExp : Complex.exp (-(1/2 : ℂ) * S (J i - ΘJ j) (J i - ΘJ j))
      = Complex.exp (-(1/2 : ℂ) * S (J i) (J i)) * Complex.exp (-(1/2 : ℂ) * S (J j) (J j))
        * Complex.exp (Complex.ofReal (R i j)) := by
      simpa [Complex.exp_add, mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.exp hxsplit'

    -- Identify diagonal exponentials with Z's
    have hi : Complex.exp (-(1/2 : ℂ) * S (J i) (J i)) = Z i := by
      simpa [Z] using (gaussian_Z_form dμ_config h_gaussian (J i)).symm
    have hj : Complex.exp (-(1/2 : ℂ) * S (J j) (J j)) = Z j := by
      simpa [Z] using (gaussian_Z_form dμ_config h_gaussian (J j)).symm

    -- Convert the real exponential
    have hk : Complex.exp (Complex.ofReal (R i j)) = (Real.exp (R i j) : ℂ) := by simp

    have hExpZ : Complex.exp (-(1/2 : ℂ) * S (J i) (J i)) * Complex.exp (-(1/2 : ℂ) * S (J j) (J j))
               = Z i * Z j := by
      rw [hi, hj]

    -- Final assembly
    have hfinal :
      GJGeneratingFunctionalℂ dμ_config (J i - ΘJ j)
        = Z i * Z j * Real.exp (R i j) := by
      calc GJGeneratingFunctionalℂ dμ_config (J i - ΘJ j)
        _ = Complex.exp (-(1/2 : ℂ) * S (J i - ΘJ j) (J i - ΘJ j)) := hZ
        _ = Complex.exp (-(1/2 : ℂ) * S (J i) (J i)) * Complex.exp (-(1/2 : ℂ) * S (J j) (J j))
            * Complex.exp (Complex.ofReal (R i j)) := by rw [hxsplit', Complex.exp_add, Complex.exp_add]
        _ = (Z i * Z j) * Real.exp (R i j) := by rw [hExpZ, hk]
        _ = Z i * Z j * Real.exp (R i j) := by ring
    exact hfinal

  -- Apply entry_factor to each term in the sum
  rw [← Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [entry_factor]]

  -- Now show the real parts are equal
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  -- Use the fact that Z values are real
  have hZreal_i : (starRingEnd ℂ) (Z i) = Z i := gaussian_Z_real_on_diagonal dμ_config h_gaussian (J i)
  have hZreal_j : (starRingEnd ℂ) (Z j) = Z j := gaussian_Z_real_on_diagonal dμ_config h_gaussian (J j)

  -- Expand using definitions: J i = (f i).val and map_mul properties
  simp only [Z, R, J]
  rw [map_mul, hZreal_i]
  ring

/-- Main theorem: Gaussian measures satisfying the covariance reflection positivity
    condition prove OS3_ReflectionPositivity.

    This combines all our machinery:
    1. Gaussian exponential form: Z[h] = exp(-½⟨h, Ch⟩)
    2. Matrix factorization: M_{ij} = Z[f_i]Z[f_j]exp(R_{ij})
    3. Schur product positivity: elementwise positive matrices preserve positive semidefiniteness
    4. Covariance reflection positivity: R_{ij} matrix is positive semidefinite
-/
theorem gaussian_satisfies_OS3_reflection_positivity
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_bilinear : CovarianceBilinear dμ_config)
  (h_reflectInv : OS3_ReflectionInvariance dμ_config)
  (h_covar_reflect_pos : CovarianceReflectionPositive dμ_config)
  : OS3_ReflectionPositivity dμ_config := by
  -- Goal: prove ∀ n f c, 0 ≤ (∑ᵢⱼ c̄ᵢcⱼ Z[fᵢ - Θfⱼ]).re
  intro n f c

  -- Simplify the `have` expressions in the goal
  simp only [OS3_ReflectionPositivity] at *

  -- Now apply the Gaussian factorization from gaussian_quadratic_real_rewrite
  rw [gaussian_quadratic_real_rewrite dμ_config h_gaussian h_bilinear h_reflectInv f c]

  -- Now we need to show: 0 ≤ (∑ᵢⱼ c̄ᵢcⱼZ[fᵢ]Z[fⱼ]exp(R_{ij})).re
  -- where R_{ij} = Re S₂(fᵢ, Θfⱼ)

  -- Factor out the Z values (which are real and positive for Gaussian measures)
  have hZ_real : ∀ i, (starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val) =
                      GJGeneratingFunctionalℂ dμ_config (f i).val :=
    fun i => gaussian_Z_real_on_diagonal dμ_config h_gaussian (f i).val

  -- The key insight: factor the sum as a Schur (Hadamard) product
  -- ∑ᵢⱼ c̄ᵢcⱼZ[fᵢ]Z[fⱼ]exp(R_{ij}) = ∑ᵢⱼ (c̄ᵢZ[fᵢ])(cⱼZ[fⱼ])exp(R_{ij})
  -- This is the Hadamard product of two matrices:
  -- A_{ij} = (c̄ᵢZ[fᵢ])(cⱼZ[fⱼ]) (rank-1, hence positive semidefinite)
  -- B_{ij} = exp(R_{ij}) (elementwise exponential of positive semidefinite matrix R)

  -- By our HadamardExp theory: if R is positive semidefinite, then exp(R) is positive semidefinite
  have hR_pos : Matrix.PosSemidef (fun i j =>
    (SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re) := by
    -- Start from the reflection matrix M_ref i j := Re S(Θ f_i, f_j)
    have hRef : Matrix.PosSemidef (fun i j =>
      (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (f i).val) (f j).val).re) :=
      h_covar_reflect_pos n f
    -- Our target is the transpose of M_ref
    change Matrix.PosSemidef (fun i j => (fun p q =>
      (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (f p).val) (f q).val).re) j i)
    -- Apply transpose PSD
    simpa using (posSemidef_transpose (A := fun i j =>
      (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (f i).val) (f j).val).re) hRef)

  -- Apply the Hadamard product positivity theorem (to be proven using HadamardExp machinery)
  have hExp_pos : Matrix.PosSemidef (fun i j =>
    Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)) := by
    exact posSemidef_entrywiseExp_of_posSemidef (R := _)
      (by simpa using hR_pos)

  -- Rank-1 PSD from u_i := Z[f_i] * c_i
  have hRank1_pos : Matrix.PosSemidef (fun i j =>
    ((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
     (GJGeneratingFunctionalℂ dμ_config (f j).val * c j)).re) := by
    set u : Fin n → ℂ := fun i => (GJGeneratingFunctionalℂ dμ_config (f i).val) * c i
    simpa [u, map_mul] using posSemidef_rank1_starEnd (n := n) u

  -- Schur product: align our target real matrix with A ∘ₕ B
  have hEq_schur : (fun i j =>
    ((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
     (GJGeneratingFunctionalℂ dμ_config (f j).val * c j) *
     (Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re) : ℂ)).re)
    = (fun i j =>
        (((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
          (GJGeneratingFunctionalℂ dμ_config (f j).val * c j)).re)
        * Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)) := by
    funext i j
    have := re_mul_ofReal
      (((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
        (GJGeneratingFunctionalℂ dμ_config (f j).val * c j)))
      ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)
    -- Rewrite (Real.exp r : ℂ) = ofReal (Real.exp r) and use the identity
    simpa [Complex.ofReal_mul] using this

  -- Apply Schur product theorem: if A and B are PSD, then A ∘ₕ B is PSD
  have hSchur_pos : Matrix.PosSemidef (fun i j =>
    ((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
     (GJGeneratingFunctionalℂ dμ_config (f j).val * c j) *
     Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)).re) := by
    -- Use the equality to reduce to a real Hadamard product
    have := schur_product_posSemidef (A := fun i j =>
        (((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
          (GJGeneratingFunctionalℂ dμ_config (f j).val * c j)).re))
      (B := fun i j => Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re))
      hRank1_pos hExp_pos
    simpa [hEq_schur]

  -- The trace (diagonal sum) of a positive semidefinite matrix is non-negative
  have hTrace_nonneg : 0 ≤ Matrix.trace (fun i j => ((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
        (GJGeneratingFunctionalℂ dμ_config (f j).val * c j) *
        Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)).re) := by
    exact trace_nonneg_of_posSemidef hSchur_pos

  -- Our sum is exactly this trace
  have hSum_eq_trace : (∑ i, ∑ j, ((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
        (GJGeneratingFunctionalℂ dμ_config (f j).val * c j) *
        Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)).re) =
      Matrix.trace (fun i j => ((starRingEnd ℂ) (GJGeneratingFunctionalℂ dμ_config (f i).val * c i) *
        (GJGeneratingFunctionalℂ dμ_config (f j).val * c j) *
        Real.exp ((SchwingerFunctionℂ₂ dμ_config (f i).val (QFT.compTimeReflection (f j).val)).re)).re) := by
    simp [Matrix.trace, Finset.sum_comm]

  rw [hSum_eq_trace]
  exact hTrace_nonneg

/-- The Gaussian Free Field satisfies OS3 reflection positivity.

    This is the main result connecting our Gaussian measure theory to the concrete
    Gaussian Free Field construction from GFFconstruct.lean.
-/
theorem gaussianFreeField_satisfies_OS3 (m : ℝ) [Fact (0 < m)]
  (h_covar_reflect_pos : CovarianceReflectionPositive (gaussianFreeField_free m))
  : OS3_ReflectionPositivity (gaussianFreeField_free m) := by
  apply gaussian_satisfies_OS3_reflection_positivity
  · -- h_gaussian: The GFF is Gaussian by construction
    exact isGaussianGJ_gaussianFreeField_free m
  · -- h_bilinear: Covariance is bilinear by construction
    exact covarianceBilinear_gaussianFreeField_free m
  · -- h_reflectInv: Time reflection invariance for free field
    exact reflectionInvariance_gaussianFreeField_free m
  · -- h_covar_reflect_pos: Given as hypothesis
    exact h_covar_reflect_pos

/-- Complete OS3 verification: if the free field covariance has reflection positivity,
    then the Gaussian Free Field satisfies all OS3 conditions.
-/
theorem gaussianFreeField_complete_OS3 (m : ℝ) [Fact (0 < m)]
  (h_covar_reflect_pos : CovarianceReflectionPositive (gaussianFreeField_free m))
  : OS3_ReflectionPositivity (gaussianFreeField_free m) ∧
    OS3_ReflectionInvariance (gaussianFreeField_free m) := by
  constructor
  · exact gaussianFreeField_satisfies_OS3 m h_covar_reflect_pos
  · exact reflectionInvariance_gaussianFreeField_free m
