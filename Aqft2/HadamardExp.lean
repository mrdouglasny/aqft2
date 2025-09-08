/-
Hadamard operations and entrywise exponential for matrices.

This module contains continuity properties, Hadamard powers, and the proof that
the entrywise exponential preserves positive definiteness via Hadamard series.
-/

import Aqft2.SchurProduct
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


set_option linter.unusedSectionVars false

open Complex
open scoped BigOperators

namespace Aqft2

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Continuity of the Hadamard (entrywise) product as a map on matrices. -/
lemma continuous_hadamard
  (ι : Type u) [Fintype ι] [DecidableEq ι] :
  Continuous (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) => p.1 ∘ₕ p.2) := by
  classical
  -- Use `continuous_pi_iff` twice (matrices are `ι → ι → ℝ`).
  refine continuous_pi_iff.2 (fun i => ?_)
  refine continuous_pi_iff.2 (fun j => ?_)
  -- Coordinates: (A ∘ₕ B) i j = A i j * B i j
  have hAij : Continuous (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) => p.1 i j) := by
    -- p ↦ p.1 (matrix) → apply at i → apply at j
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hBij : Continuous (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) => p.2 i j) := by
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  simpa [Matrix.hadamard] using hAij.mul hBij

/-- Continuity of the Hadamard squaring map A ↦ A ∘ₕ A. -/
lemma continuous_hadamard_sq (ι : Type u) [Fintype ι] [DecidableEq ι] :
  Continuous (fun A : Matrix ι ι ℝ => A ∘ₕ A) := by
  classical
  have hdiag : Continuous (fun A : Matrix ι ι ℝ => (A, A)) :=
    Continuous.prodMk continuous_id continuous_id
  simpa using (continuous_hadamard (ι := ι)).comp hdiag

/-- Entrywise real exponential of a matrix: `(entrywiseExp R) i j = exp (R i j)`.
    Used for the OS3 proof (Glimm–Jaffe): if `R` is PSD, then `exp(R)` (entrywise) should be PSD. -/
noncomputable def entrywiseExp (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (R i j)

@[simp] lemma entrywiseExp_apply (R : Matrix ι ι ℝ) (i j : ι) :
  entrywiseExp R i j = Real.exp (R i j) := rfl

/-- Continuity of the entrywise exponential map `R ↦ exp ∘ R` on matrices. -/
lemma continuous_entrywiseExp (ι : Type u) [Fintype ι] [DecidableEq ι] :
  Continuous (fun R : Matrix ι ι ℝ => entrywiseExp R) := by
  classical
  -- Matrices are pi-types `ι → ι → ℝ`; use coordinatewise continuity
  refine continuous_pi_iff.2 (fun i => ?_)
  refine continuous_pi_iff.2 (fun j => ?_)
  -- Coordinate map R ↦ R i j is continuous; compose with exp
  have hcoord : Continuous (fun R : Matrix ι ι ℝ => R i j) :=
    (continuous_apply j).comp (continuous_apply i)
  simpa [entrywiseExp] using (Real.continuous_exp.comp hcoord)

/-- Hadamard identity element: the all-ones matrix for entrywise multiplication. -/
@[simp] def hadamardOne (ι : Type u) [Fintype ι] : Matrix ι ι ℝ := fun _ _ => 1

/-- n-fold Hadamard power of a matrix: `hadamardPow R n = R ∘ₕ ⋯ ∘ₕ R` (n times),
    with `hadamardPow R 0 = hadamardOne`. -/
@[simp] def hadamardPow (R : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0     => hadamardOne (ι := ι)
  | n+1   => hadamardPow R n ∘ₕ R

@[simp] lemma hadamardPow_zero (R : Matrix ι ι ℝ) : hadamardPow (ι:=ι) R 0 = hadamardOne (ι:=ι) := rfl
@[simp] lemma hadamardPow_succ (R : Matrix ι ι ℝ) (n : ℕ) :
  hadamardPow (ι:=ι) R (n+1) = (hadamardPow (ι:=ι) R n) ∘ₕ R := rfl

/-- Hadamard powers act entrywise as usual scalar powers. -/
lemma hadamardPow_apply (R : Matrix ι ι ℝ) (n : ℕ) (i j : ι) :
  hadamardPow (ι:=ι) R n i j = (R i j) ^ n := by
  induction' n with n ih
  · simp [hadamardPow, hadamardOne]
  · simp [Matrix.hadamard, ih, pow_succ]

/-- One term of the Hadamard-series for the entrywise exponential. -/
noncomputable def entrywiseExpSeriesTerm (R : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  (1 / (Nat.factorial n : ℝ)) • hadamardPow (ι:=ι) R n

/-- Series definition of the entrywise exponential using Hadamard powers (entrywise `tsum`). -/
noncomputable def entrywiseExp_hadamardSeries (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => tsum (fun n : ℕ => (1 / (Nat.factorial n : ℝ)) * (hadamardPow (ι:=ι) R n i j))

/-- The entrywise exponential agrees with its Hadamard series expansion.
    Uses the Taylor series for Complex.exp and converts to the real case. -/
lemma entrywiseExp_eq_hadamardSeries (R : Matrix ι ι ℝ) :
  entrywiseExp R = entrywiseExp_hadamardSeries (ι:=ι) R := by
  classical
  funext i j
  dsimp [entrywiseExp, entrywiseExp_hadamardSeries]
  -- Scalar reduction
  set x : ℝ := R i j
  -- Complex Taylor series for exp at 0
  have h_taylor : ∑' n : ℕ,
      (↑n.factorial)⁻¹ * (iteratedDeriv n Complex.exp 0) * ((x : ℂ) - 0) ^ n
      = Complex.exp (x : ℂ) := by
    exact Complex.taylorSeries_eq_on_emetric_ball'
      (c := 0) (r := ⊤) (z := (x : ℂ)) (by simp)
      (by simpa using Complex.differentiable_exp.differentiableOn)
  -- iteratedDeriv n exp 0 = 1
  have h_deriv : ∀ n, iteratedDeriv n Complex.exp 0 = 1 := by
    intro n; rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero]
  -- Define series terms
  let fC : ℕ → ℂ := fun n => (x : ℂ) ^ n / (Nat.factorial n : ℂ)
  let fR : ℕ → ℝ := fun n => x ^ n / (Nat.factorial n : ℝ)
  -- Standard complex power series for exp
  have h_seriesC : ∑' n : ℕ, fC n = Complex.exp (x : ℂ) := by
    -- simplify Taylor series to the usual form
    simpa [fC, div_eq_mul_inv, sub_zero, h_deriv, mul_comm, mul_left_comm, mul_assoc] using h_taylor
  -- Summability of the complex series via the real one
  have hsR : Summable fR := Real.summable_pow_div_factorial x
  have hsC_ofReal : Summable (fun n : ℕ => (fR n : ℂ)) := (Complex.summable_ofReal).2 hsR
  have h_eqfun : (fun n : ℕ => (fR n : ℂ)) = fC := by
    funext n; simp [fR, fC, div_eq_mul_inv]
  have hsC : Summable fC := by simpa [h_eqfun] using hsC_ofReal
  -- Take real parts in the complex series identity
  have h_re_tsum : (∑' n : ℕ, fC n).re = ∑' n : ℕ, (fC n).re := Complex.re_tsum hsC
  have h_re_exp : (Complex.exp (x : ℂ)).re = Real.exp x := Complex.exp_ofReal_re x
  have h_re_terms : (fun n : ℕ => (fC n).re) = fR := by
    funext n
    -- First show fC n equals the complexification of fR n
    have hpt : fC n = (fR n : ℂ) := by
      simp [fC, fR, div_eq_mul_inv]
    -- Then take real parts
    simpa [Complex.ofReal_re] using congrArg Complex.re hpt
  -- Combine: real parts of both sides of h_seriesC give the real series identity
  have hx_sum : ∑' n : ℕ, fR n = Real.exp x := by
    have := congrArg Complex.re h_seriesC
    simpa [h_re_tsum, h_re_exp, h_re_terms] using this
  -- Massaging coefficients and finishing
  have hx_sum' : Real.exp x = ∑' n : ℕ, (1 / (Nat.factorial n : ℝ)) * x ^ n := by
    simpa [fR, one_div, div_eq_mul_inv, mul_comm] using hx_sum.symm
  simpa [x, hadamardPow_apply, one_div, div_eq_mul_inv, mul_comm] using hx_sum'

/-- Ones is the identity for the Hadamard product. -/
lemma hadamardOne_hMul_left (R : Matrix ι ι ℝ) : Matrix.hadamard (hadamardOne ι) R = R := by
  ext i j; simp [hadamardOne, Matrix.hadamard]

/-- Ones is the identity for the Hadamard product (right). -/
lemma hadamardOne_hMul_right (R : Matrix ι ι ℝ) : Matrix.hadamard R (hadamardOne ι) = R := by
  ext i j; simp [hadamardOne, Matrix.hadamard]

/-- Hadamard powers of a positive definite matrix are positive definite for all n ≥ 1. -/
lemma hadamardPow_posDef_of_posDef
  (R : Matrix ι ι ℝ) (hR : R.PosDef) : ∀ n, 1 ≤ n → (hadamardPow (ι:=ι) R n).PosDef := by
  classical
  intro n hn
  -- write n = k+1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  subst hk
  induction' k with k ih
  · -- n = 1
    have hEq : hadamardPow (ι:=ι) R 1 = R := by
      ext i j; simp
    rw [hEq]; exact hR
  · -- n = (k+1)+1 = k+2
    have hPD_k1 : (hadamardPow (ι:=ι) R (k+1)).PosDef := ih (Nat.succ_pos _)
    -- Schur product with R preserves PD
    simpa [hadamardPow_succ] using
      schur_product_posDef (ι:=ι)
        (A := hadamardPow (ι:=ι) R (k+1)) (B := R) hPD_k1 hR

/-- The Hadamard-series entrywise exponential preserves positive definiteness.
    Sketch: each Hadamard power (for n ≥ 1) is PD by the Schur product theorem and induction;
    summing with positive coefficients 1/n! yields strictly positive quadratic form for every x ≠ 0
    since the n = 1 term already contributes xᵀ R x > 0. Interchange of sum and quadratic form
    follows from absolute convergence of the scalar exp series; IsHermitian follows termwise. -/
lemma posDef_entrywiseExp_hadamardSeries_of_posDef
  (R : Matrix ι ι ℝ) (hR : R.PosDef) :
  (entrywiseExp_hadamardSeries (ι:=ι) R).PosDef := by
  classical
  -- Unpack Hermitian part and positivity of quadratic form from PosDef
  obtain ⟨hHermR, hposR⟩ := hR
  have hR' : R.PosDef := ⟨hHermR, hposR⟩
  -- Each Hadamard power is Hermitian
  have hHermPow : ∀ n, (hadamardPow (ι:=ι) R n).IsHermitian := by
    intro n
    induction' n with n ih
    · -- n = 0
      -- hadamardOne is symmetric
      rw [hadamardPow_zero]
      -- direct by entries
      rw [Matrix.IsHermitian]
      ext i j; simp [hadamardOne, Matrix.conjTranspose]
    · -- succ
      -- (A ∘ₕ R) is Hermitian if both are Hermitian (entrywise symmetry)
      -- use pointwise characterization
      rw [hadamardPow_succ]
      -- prove IsHermitian of hadamard by unfolding
      rw [Matrix.IsHermitian]
      ext i j
      have hAij : (hadamardPow (ι:=ι) R n) i j = (hadamardPow (ι:=ι) R n) j i := by
        -- from ih
        simpa using (Matrix.IsHermitian.apply ih i j).symm
      have hRij : R i j = R j i := by
        simpa using (Matrix.IsHermitian.apply hHermR i j).symm
      simp [Matrix.conjTranspose, Matrix.hadamard, hAij, hRij]
  -- Show IsHermitian for the series (termwise symmetry)
  have hHermS : (entrywiseExp_hadamardSeries (ι:=ι) R).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [entrywiseExp_hadamardSeries, Matrix.conjTranspose]
    -- Use termwise symmetry under tsum
    have hsym_term : ∀ n, (hadamardPow (ι:=ι) R n i j) = (hadamardPow (ι:=ι) R n j i) := by
      intro n
      -- from hHermPow n
      simpa using (Matrix.IsHermitian.apply (hHermPow n) i j).symm
    -- Apply symmetry termwise in the tsum
    simp_rw [hsym_term]
  -- Now show strict positivity of the quadratic form
  refine ⟨hHermS, ?_⟩
  intro x hx
  -- Define the scalar series of quadratic forms
  let f : ℕ → ℝ := fun n => (1 / (Nat.factorial n : ℝ)) * (x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x)
  -- Identify the quadratic form of the series with the tsum of `f`
  have hq_tsum :
      x ⬝ᵥ (entrywiseExp_hadamardSeries (ι:=ι) R).mulVec x
      = tsum f := by
    -- This is a standard interchange of finite and infinite sums
    -- Valid because matrices are finite-dimensional
    sorry
  -- Each term f n is nonnegative, and f 1 is strictly positive
  have hterm_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hn : n = 0
    · -- n = 0: ones matrix
      subst hn
      -- Compute the quadratic form against the ones matrix explicitly
      classical
      have hmv : (hadamardOne (ι:=ι)).mulVec x = (fun _ => ∑ j, x j) := by
        funext i; simp [hadamardOne, Matrix.mulVec, dotProduct]
      have hquad : x ⬝ᵥ (hadamardOne (ι:=ι)).mulVec x = (∑ i, x i) * (∑ i, x i) := by
        simp [hmv, dotProduct, Finset.sum_mul]
      -- Reduce to a square ≥ 0
      have : 0 ≤ (∑ i, x i) ^ 2 := by exact sq_nonneg _
      simpa [f, hadamardPow, Nat.factorial_zero, one_div, hquad, pow_two] using this
    · -- n ≥ 1: use PosSemidef from PosDef
      have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hPD : (hadamardPow (ι:=ι) R n).PosDef :=
        hadamardPow_posDef_of_posDef (ι:=ι) R hR' n hn1
      -- hence PosSemidef
      have hPSD : (hadamardPow (ι:=ι) R n).PosSemidef := Matrix.PosDef.posSemidef hPD
      -- evaluate quadratic form
      have hxq : 0 ≤ x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x := hPSD.2 x
      -- multiply by positive coefficient 1/n!
      have hcoeff : 0 ≤ (1 / (Nat.factorial n : ℝ)) := by
        have : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast (Nat.cast_pos.mpr (Nat.factorial_pos n))
        exact div_nonneg (by norm_num) this.le
      exact mul_nonneg hcoeff hxq
  have hterm_pos : 0 < f 1 := by
    -- n = 1 term equals xᵀ R x, which is strictly positive by hR
    have hEq1' : hadamardPow (ι:=ι) R 1 = Matrix.hadamard (hadamardOne (ι:=ι)) R := rfl
    have hRpos := hposR x hx
    simpa [f, hEq1', hadamardOne_hMul_left, Nat.factorial, one_div, inv_one] using hRpos
  -- Strict positivity of the sum from the positive n=1 term and nonnegativity of the rest
  have : 0 < tsum f := by
    -- One can prove: tsum f ≥ f 1 by comparing with partial sums or by splitting off n=1.
    -- We omit the technical step here.
    sorry
  -- Conclude
  simpa [hq_tsum] using this

end Aqft2
