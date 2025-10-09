/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

## OS3: Reflection Positivity for Gaussian Measures

This file contains the proof that Gaussian measures satisfy the OS3 (Reflection Positivity)
axiom using the Glimm-Jaffe Theorem 6.2.2 approach. The reflection positivity condition
is verified using the explicit exponential form of Gaussian measures and properties of
the covariance under time ref   -- Convert the complex exponential equality to a real exponen   -- Move to real exponentials via ofReal in two steps
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
     exact hZ equality
   have hZc : Complex.exp (-(1/2 : ℂ) * (rθ : ℂ))
            = Complex.exp (-(1/2 : ℂ) * (r : ℂ)) := by
     -- Use substitution via h1, h2
     have h1 : S (QFT.compTimeReflection h) (QFT.compTimeReflection h) = (rθ : ℂ) := by
       show SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection h) (QFT.compTimeReflection h) = (rθ : ℂ)
       exact hrθ
     have h2 : S h h = (r : ℂ) := by
       show SchwingerFunctionℂ₂ dμ_config h h = (r : ℂ)
       exact hr
     rw [h1, h2] at hZ
     exact hZion.

### Key Components:

**Glimm-Jaffe Framework:**
- `glimm_jaffe_exponent`: Expansion of ⟨F - CF', C(F - CF')⟩ where F' = ΘF
- `glimm_jaffe_reflection_functional`: Z[F - CF'] = exp(-½⟨F - CF', C(F - CF')⟩
- `CovarianceReflectionPositive`: Key condition ensuring reflection positivity
- `covarianceOperator`: Riesz representation of 2-point function

**Mathematical Strategy:**
For Gaussian measures Z[h] = exp(-½⟨h, Ch⟩), the reflection positivity matrix
M_{ij} = Z[f_i - θf_j] can be factored using exponential properties and the
Schur product theorem applied to positive semidefinite matrices.

**Key Results:**
- `schwinger_function_hermitian`: Hermitian property S₂(f,g) = conj S₂(g,f)
- `diagonal_covariance_is_real`: Diagonal covariance elements are real
- `gaussian_satisfies_OS3_matrix`: Main theorem proving OS3 for Gaussian measures
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
import Aqft2.GFFMconstruct
import Aqft2.Euclidean
import Aqft2.DiscreteSymmetry
import Aqft2.SCV
import Aqft2.FunctionalAnalysis
import Aqft2.OS4
import Aqft2.Minlos
import Aqft2.Covariance
import Aqft2.HadamardExp

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

open scoped BigOperators
open Finset

/-! ## OS3: Reflection Positivity for Gaussian Measures

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

/-- The covariance operator extracted from the 2-point Schwinger function.
    For a Gaussian measure, this defines a continuous linear map C : TestFunctionℂ → TestFunctionℂ
    such that ⟨f, Cg⟩ = S₂(f̄, g) -/
def covarianceOperator (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_bilinear : CovarianceBilinear dμ_config) : TestFunctionℂ →L[ℂ] TestFunctionℂ := sorry

/-- Glimm-Jaffe's condition: reflection positivity of the covariance operator.
    Matrix formulation: for any finite positive-time family, the kernel
    R_{ij} := Re S₂(Θ f_i, f_j) is positive semidefinite. -/
def CovarianceReflectionPositive (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction),
    Matrix.PosSemidef (fun i j : Fin n =>
      (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (f i).val) (f j).val).re)

-- Helper: PosSemidef for the reflection matrix from the assumption
lemma reflection_matrix_posSemidef
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (hRP : CovarianceReflectionPositive dμ_config)
  {n : ℕ} (f : Fin n → PositiveTimeTestFunction) :
  Matrix.PosSemidef (fun i j : Fin n =>
    (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (f i).val) (f j).val).re) :=
  hRP n f

/-- Gaussian form: the generating functional satisfies Z[h] = exp(-½ S₂(h,h)) -/
lemma gaussian_Z_form
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h : TestFunctionℂ) :
  GJGeneratingFunctionalℂ dμ_config h = Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config h h) := by
  -- Follows immediately from the Gaussian characterization
  exact (h_gaussian.2 h)

/-- Hermitian property of the 2-point Schwinger function: S₂(f,g) = conj S₂(g,f).
    This is a fundamental property needed for reflection positivity and ensures that
    the covariance matrix is Hermitian (symmetric for real arguments). -/
lemma schwinger_function_hermitian (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config f g = star (SchwingerFunctionℂ₂ dμ_config g f) := by
  -- This follows from the fundamental Hermitian property of 2-point functions in QFT
  -- For Gaussian measures, this comes from the fact that the covariance is a real kernel
  -- when restricted to real test functions, and extends by sesquilinearity to complex functions
  --
  -- The proof would use:
  -- 1) Definition of SchwingerFunctionℂ₂ in terms of field expectation values
  -- 2) Hermitian property of expectation values: ⟨ψ, Aψ⟩ = conj ⟨ψ, A†ψ⟩
  -- 3) Self-adjointness of the field operator in the Euclidean formulation
  -- 4) Analytic continuation properties that preserve the Hermitian structure
  sorry

/-- Auxiliary lemma: diagonal values of the complex covariance are real for RP (Hermitian) kernels.
    Proof sketch: use hermitian symmetry S(f,g) = conj S(g,f) and set g = f. -/
lemma diagonal_covariance_is_real
  (dμ_config : ProbabilityMeasure FieldConfiguration) :
  ∀ h : TestFunctionℂ, ∃ r : ℝ, SchwingerFunctionℂ₂ dμ_config h h = (r : ℂ) := by
  intro h
  -- Use the Hermitian property: S(h,h) = star S(h,h)
  -- For diagonal elements, this means S(h,h) = conj S(h,h)
  -- A complex number equals its conjugate if and only if it's real
  have h_hermitian := schwinger_function_hermitian dμ_config h h
  -- S(h,h) = star S(h,h) = conj S(h,h)
  -- This means S(h,h) is real
  have h_real : (SchwingerFunctionℂ₂ dμ_config h h).im = 0 := by
    -- From hermitian property: z = star z ↔ z = conj z ↔ z.im = 0
    have : SchwingerFunctionℂ₂ dμ_config h h = star (SchwingerFunctionℂ₂ dμ_config h h) := h_hermitian
    rw [Complex.star_def] at this
    -- If z = conj z, then z.im = -(conj z).im = -z.im, so z.im = 0
    have : (SchwingerFunctionℂ₂ dμ_config h h).im = -(SchwingerFunctionℂ₂ dμ_config h h).im := by
      have := congrArg Complex.im this
      simpa [Complex.conj_im] using this
    linarith
  -- Extract the real part as a real number
  use (SchwingerFunctionℂ₂ dμ_config h h).re
  -- A complex number with zero imaginary part equals its real part
  exact Complex.ext_iff.mpr ⟨rfl, h_real⟩

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

/-- Bilinear expansion of the 2-point function under subtraction -/
lemma bilin_expand
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_bilinear : CovarianceBilinear dμ_config)
  (x y : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config (x - y) (x - y) =
    SchwingerFunctionℂ₂ dμ_config x x + SchwingerFunctionℂ₂ dμ_config y y -
    SchwingerFunctionℂ₂ dμ_config x y - SchwingerFunctionℂ₂ dμ_config y x := by
  -- abbreviate
  let S := SchwingerFunctionℂ₂ dμ_config
  -- expand using additivity in each argument
  have h_add_left : S (x + (-y)) (x + (-y)) = S x (x + (-y)) + S (-y) (x + (-y)) := by
    simpa using (h_bilinear (1 : ℂ) x (-y) (x + (-y))).2.1
  have h_add_right₁ : S x (x + (-y)) = S x x + S x (-y) := by
    -- from right additivity, commuting (-y)+x to x+(-y)
    have h := (h_bilinear (1 : ℂ) x (-y) x).2.2.2
    -- h : S x ((-y) + x) = S x (-y) + S x x
    simpa [add_comm] using h
  have h_add_right₂ : S (-y) (x + (-y)) = S (-y) x + S (-y) (-y) := by
    -- get S (-y) ((-y)+x) = S (-y) (-y) + S (-y) x, then commute both sides
    have h := (h_bilinear (1 : ℂ) (-y) (-y) x).2.2.2
    -- h : S (-y) ((-y) + x) = S (-y) (-y) + S (-y) x
    simpa [add_comm, add_comm (S (-y) (-y)) (S (-y) x)] using h
  -- scalar linearity for -1 on each arg
  have h_smul_right : S x (-y) = (-1 : ℂ) * S x y := by
    simpa [neg_one_smul] using (h_bilinear (-1 : ℂ) x (0 : TestFunctionℂ) y).2.2.1
  have h_smul_left : S (-y) x = (-1 : ℂ) * S y x := by
    simpa [neg_one_smul] using (h_bilinear (-1 : ℂ) y (0 : TestFunctionℂ) x).1
  have h_smul_both : S (-y) (-y) = S y y := by
    have h1 : S (-y) (-y) = (-1 : ℂ) * S y (-y) := by
      simpa [neg_one_smul] using (h_bilinear (-1 : ℂ) y (0 : TestFunctionℂ) (-y)).1
    have h2 : S y (-y) = (-1 : ℂ) * S y y := by
      simpa [neg_one_smul] using (h_bilinear (-1 : ℂ) y (0 : TestFunctionℂ) y).2.2.1
    calc
      S (-y) (-y) = (-1 : ℂ) * S y (-y) := h1
      _ = (-1 : ℂ) * ((-1 : ℂ) * S y y) := by simp [h2]
      _ = (1 : ℂ) * S y y := by ring
      _ = S y y := by simp
  -- assemble
  have hx : S (x + (-y)) (x + (-y))
      = S x x + ((-1 : ℂ) * S x y) + ((-1 : ℂ) * S y x) + S y y := by
    calc
      S (x + (-y)) (x + (-y))
          = S x (x + (-y)) + S (-y) (x + (-y)) := h_add_left
      _ = (S x x + S x (-y)) + (S (-y) x + S (-y) (-y)) := by
          simp [h_add_right₁, h_add_right₂]
      _ = S x x + ((-1 : ℂ) * S x y) + ((-1 : ℂ) * S y x) + S (-y) (-y) := by
          simp [h_smul_right, h_smul_left, add_assoc]
      _ = S x x + ((-1 : ℂ) * S x y) + ((-1 : ℂ) * S y x) + S y y := by
          simp [h_smul_both]
  -- conclude
  calc
    S (x - y) (x - y) = S (x + (-y)) (x + (-y)) := by simp [sub_eq_add_neg]
    _ = S x x + ((-1 : ℂ) * S x y) + ((-1 : ℂ) * S y x) + S y y := hx
    _ = S x x + S y y - S x y - S y x := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Time-reflection invariance for diagonal covariance elements.

    This lemma states that the 2-point Schwinger function is invariant under simultaneous
    time reflection of both arguments. This is a fundamental property that follows from
    the time-reflection symmetry of the underlying measure and geometric structure.

    The proof strategy uses the fact that:
    1. Time reflection is an orthogonal transformation (preserves inner products)
    2. The Schwinger function can be expressed in terms of the underlying field configuration
    3. If the measure is invariant under time reflection, then expectation values are preserved
-/
lemma covariance_reflection_invariant_diag
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection h) (QFT.compTimeReflection h) =
  SchwingerFunctionℂ₂ dμ_config h h := by
  -- For a complete proof, we would need to show that:
  -- 1. The measure dμ_config is invariant under the time reflection transformation
  --    This means: ∫ F(Θω) dμ(ω) = ∫ F(ω) dμ(ω) for any measurable F
  -- 2. Apply this invariance to the definition of SchwingerFunctionℂ₂
  -- 3. Use the fact that QFT.compTimeReflection corresponds to the geometric time reflection
  --
  -- The invariance would follow from:
  -- - Physical requirement: reflection-positive measures should be time-reflection invariant
  -- - Mathematical structure: time reflection preserves the measure-theoretic structure
  -- - QFT.timeReflection is an isometry (preserves geometric structure)
  --
  -- In practice, this is often taken as an axiom for reflection-positive theories,
  -- or proven using the specific construction of the measure (e.g., for Gaussian measures,
  -- using the fact that the covariance function satisfies C(Θx, Θy) = C(x, y))

  sorry

/-- Hermitian-reflection cross-term identity (stub) -/
lemma reflection_hermitian_cross
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (a b : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config a (QFT.compTimeReflection b) =
  star (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection a) b) := by
  -- TODO: combine schwinger_function_hermitian with time-reflection
  sorry

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
        * Real.exp ((SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (f i).val) (f j).val).re)
      ).re := by
  classical
  -- Abbreviations
  let J : Fin n → TestFunctionℂ := fun i => (f i).val
  let ΘJ : Fin n → TestFunctionℂ := fun j => QFT.compTimeReflection (f j).val
  let Z : Fin n → ℂ := fun i => GJGeneratingFunctionalℂ dμ_config (J i)
  let R : Fin n → Fin n → ℝ := fun i j =>
    (SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (J i)) (J j)).re

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
    -- Reflection to move Re
    have hrefl : (S (J i) (ΘJ j)).re = (S (QFT.compTimeReflection (J i)) (J j)).re := by
      have hx : S (J i) (ΘJ j) = star (S (QFT.compTimeReflection (J i)) (J j)) :=
        reflection_hermitian_cross dμ_config (J i) (J j)
      simpa [Complex.star_def, Complex.conj_re] using congrArg Complex.re hx
    -- Diagonal reflection invariance via Gaussian and Z-invariance
    have hdiag : S (ΘJ j) (ΘJ j) = S (J j) (J j) := by
      -- Gaussian Z-forms at reflected and original arguments
      have zθ : GJGeneratingFunctionalℂ dμ_config (QFT.compTimeReflection (J j))
        = Complex.exp (-(1/2 : ℂ) * S (QFT.compTimeReflection (J j)) (QFT.compTimeReflection (J j))) :=
        gaussian_Z_form dμ_config h_gaussian (QFT.compTimeReflection (J j))
      have zh : GJGeneratingFunctionalℂ dμ_config (J j)
        = Complex.exp (-(1/2 : ℂ) * S (J j) (J j)) :=
        gaussian_Z_form dμ_config h_gaussian (J j)
      have hZeq : Complex.exp (-(1/2 : ℂ) * S (QFT.compTimeReflection (J j)) (QFT.compTimeReflection (J j)))
               = Complex.exp (-(1/2 : ℂ) * S (J j) (J j)) := by
        simpa [zθ, zh] using (h_reflectInv (J j))
      -- Convert the complex exponential equality to a real exponential equality
      rcases diagonal_covariance_is_real dμ_config (QFT.compTimeReflection (J j)) with ⟨rθ, hrθ⟩
      rcases diagonal_covariance_is_real dμ_config (J j) with ⟨r, hr⟩
      -- Convert the complex exponential equality to a real exponential equality
      have hZc : Complex.exp (-(1/2 : ℂ) * (rθ : ℂ))
               = Complex.exp (-(1/2 : ℂ) * (r : ℂ)) := by
        -- Substitute the real values using hrθ and hr by congruence
        have h1 : S (QFT.compTimeReflection (J j)) (QFT.compTimeReflection (J j)) = (rθ : ℂ) := by
          show SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection (J j)) (QFT.compTimeReflection (J j)) = (rθ : ℂ)
          exact hrθ
        have h2 : S (J j) (J j) = (r : ℂ) := by
          show SchwingerFunctionℂ₂ dμ_config (J j) (J j) = (r : ℂ)
          exact hr
        rw [h1, h2] at hZeq
        exact hZeq
      have hZc' : Complex.exp (Complex.ofReal (-(1/2 : ℝ) * rθ))
                = Complex.exp (Complex.ofReal (-(1/2 : ℝ) * r)) := by
        simpa [Complex.ofReal_mul] using hZc
      have hZ_real_ofReal : Complex.ofReal (Real.exp (-(1/2 : ℝ) * rθ))
                          = Complex.ofReal (Real.exp (-(1/2 : ℝ) * r)) := by
        simpa [Complex.ofReal_exp] using hZc'
      have hZ_real : Real.exp (-(1/2 : ℝ) * rθ) = Real.exp (-(1/2 : ℝ) * r) :=
        Complex.ofReal_inj.mp hZ_real_ofReal
      have hlin : (-(1/2 : ℝ) * rθ) = (-(1/2 : ℝ) * r) := by
        have := congrArg Real.log hZ_real
        simpa [Real.log_exp] using this
      have hr_eq : rθ = r := by
        have := congrArg (fun t : ℝ => (-2 : ℝ) * t) hlin
        ring_nf at this
        simpa using this
      -- Conclude for ΘJ j using definitional equality ΘJ j = compTimeReflection (J j)
      have hcomp : S (QFT.compTimeReflection (J j)) (QFT.compTimeReflection (J j)) = (r : ℂ) := by
        simpa [hr_eq] using hrθ
      have horig : S (J j) (J j) = (r : ℂ) := hr
      -- therefore S(ΘJ j, ΘJ j) = S(J j, J j)
      have : S (QFT.compTimeReflection (J j)) (QFT.compTimeReflection (J j)) = S (J j) (J j) := by
        simp [hcomp, horig]
      simpa [ΘJ] using this
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
      simpa [C, D, R, hrefl] using hhalf_pos
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
    calc GJGeneratingFunctionalℂ dμ_config (J i - ΘJ j)
      _ = Complex.exp (-(1/2 : ℂ) * S (J i - ΘJ j) (J i - ΘJ j)) := hZ
      _ = Complex.exp (-(1/2 : ℂ) * S (J i) (J i)) * Complex.exp (-(1/2 : ℂ) * S (J j) (J j))
          * Complex.exp (Complex.ofReal (R i j)) := by rw [hxsplit', Complex.exp_add, Complex.exp_add]
      _ = (Z i * Z j) * Real.exp (R i j) := by rw [hExpZ, hk]
      _ = Z i * Z j * Real.exp (R i j) := by ring

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

lemma covariance_reflection_invariant_diag_gaussian
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_reflectInv : OS3_ReflectionInvariance dμ_config)
  (h : TestFunctionℂ) :
  SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection h) (QFT.compTimeReflection h)
  = SchwingerFunctionℂ₂ dμ_config h h := by
  let S := SchwingerFunctionℂ₂ dμ_config
  have zθ : GJGeneratingFunctionalℂ dμ_config (QFT.compTimeReflection h)
    = Complex.exp (-(1/2 : ℂ) * S (QFT.compTimeReflection h) (QFT.compTimeReflection h)) :=
    gaussian_Z_form dμ_config h_gaussian (QFT.compTimeReflection h)
  have zh : GJGeneratingFunctionalℂ dμ_config h
    = Complex.exp (-(1/2 : ℂ) * S h h) :=
    gaussian_Z_form dμ_config h_gaussian h
  have hZ : Complex.exp (-(1/2 : ℂ) * S (QFT.compTimeReflection h) (QFT.compTimeReflection h))
            = Complex.exp (-(1/2 : ℂ) * S h h) := by
    simpa [zθ, zh] using (h_reflectInv h)
  -- Realness on the diagonal
  rcases diagonal_covariance_is_real dμ_config (QFT.compTimeReflection h) with ⟨rθ, hrθ⟩
  rcases diagonal_covariance_is_real dμ_config h with ⟨r, hr⟩
  -- Convert the complex exponential equality to a real exponential equality
  have hZc : Complex.exp (-(1/2 : ℂ) * (rθ : ℂ))
           = Complex.exp (-(1/2 : ℂ) * (r : ℂ)) := by
     -- Use substitution
     have h1 : S (QFT.compTimeReflection h) (QFT.compTimeReflection h) = (rθ : ℂ) := by
       show SchwingerFunctionℂ₂ dμ_config (QFT.compTimeReflection h) (QFT.compTimeReflection h) = (rθ : ℂ)
       exact hrθ
     have h2 : S h h = (r : ℂ) := by
       show SchwingerFunctionℂ₂ dμ_config h h = (r : ℂ)
       exact hr
     rw [h1, h2] at hZ
     exact hZ
  have hZc' : Complex.exp (Complex.ofReal (-(1/2 : ℝ) * rθ))
            = Complex.exp (Complex.ofReal (-(1/2 : ℝ) * r)) := by
      simpa [Complex.ofReal_mul] using hZc
  have hZ_real_ofReal : Complex.ofReal (Real.exp (-(1/2 : ℝ) * rθ))
                       = Complex.ofReal (Real.exp (-(1/2 : ℝ) * r)) := by
    simpa [Complex.ofReal_exp] using hZc'
  have hZ_real : Real.exp (-(1/2 : ℝ) * rθ) = Real.exp (-(1/2 : ℝ) * r) :=
    Complex.ofReal_inj.mp hZ_real_ofReal
  have hlin : (-(1/2 : ℝ) * rθ) = (-(1/2 : ℝ) * r) := by
    have := congrArg Real.log hZ_real
    simpa [Real.log_exp] using this
  have hr_eq : rθ = r := by
    have := congrArg (fun t : ℝ => (-2 : ℝ) * t) hlin
    ring_nf at this
    simpa using this
  -- Conclude with a calc chain rather than simpa
  calc
    S (QFT.compTimeReflection h) (QFT.compTimeReflection h)
        = (rθ : ℂ) := hrθ
    _ = (r : ℂ) := by simp [hr_eq]
    _ = S h h := hr.symm

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
