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
  induction n with
  | zero => simp [hadamardPow, hadamardOne]
  | succ n ih => simp [Matrix.hadamard, ih, pow_succ]

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
  induction k with
  | zero =>
    -- n = 1
    have hEq : hadamardPow (ι:=ι) R 1 = R := by
      ext i j; simp
    rw [hEq]; exact hR
  | succ k ih =>
    -- n = (k+1)+1 = k+2
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
    induction n with
    | zero =>
      -- n = 0
      -- hadamardOne is symmetric
      rw [hadamardPow_zero]
      -- direct by entries
      rw [Matrix.IsHermitian]
      ext i j; simp [hadamardOne, Matrix.conjTranspose]
    | succ n ih =>
      -- succ
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
    classical
    -- Per entry: s_ij n := (1 / (n!)) * hadamardPow R n i j
    let s_ij (i j : ι) (n : ℕ) := (1 / (Nat.factorial n : ℝ)) * hadamardPow (ι:=ι) R n i j

    -- Summability for each entry
    have hs_ij (i j : ι) : Summable (s_ij i j) := by
      simpa [s_ij, hadamardPow_apply, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using Real.summable_pow_div_factorial (R i j)

    -- HasSum for each entry
    have hHas_ij (i j : ι) : HasSum (s_ij i j) ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) := by
      have h1 : (entrywiseExp_hadamardSeries (ι:=ι) R) i j = tsum (s_ij i j) := by
        simp [entrywiseExp_hadamardSeries, s_ij]
      rw [h1]
      exact (hs_ij i j).hasSum

    -- Push scalars inside: first x j
    have hHas_ij_xj (i j : ι) :
        HasSum (fun n => s_ij i j n * x j) ((entrywiseExp_hadamardSeries (ι:=ι) R) i j * x j) :=
      (hHas_ij i j).mul_right (x j)

    -- Then x i
    have hHas_ij_xi_xj (i j : ι) :
        HasSum (fun n => x i * (s_ij i j n * x j)) (x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j * x j)) :=
      (hHas_ij_xj i j).mul_left (x i)

    -- Rewrite term
    have hHas_ij_rewrite (i j : ι) :
        HasSum (fun n => (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j))
               (x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) * x j) := by
      convert hHas_ij_xi_xj i j using 1
      · funext n; simp [s_ij, mul_assoc, mul_left_comm, mul_comm]
      · simp [mul_assoc]

    -- Combine over j (finite) with hasSum_sum
    have hHas_sum_j (i : ι) :
        HasSum (fun n => ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j))
               (∑ j, x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) * x j) := by
      apply hasSum_sum
      intro j _
      exact hHas_ij_rewrite i j

    -- Combine over i (finite) similarly
    have hHas_sum_i :
        HasSum (fun n => ∑ i, ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j))
               (∑ i, ∑ j, x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) * x j) := by
      apply hasSum_sum
      intro i _
      exact hHas_sum_j i

    -- Take tsum of hHas_sum_i
    have htsum_eq := hHas_sum_i.tsum_eq

    -- Expand the RHS to x ⬝ᵥ (...) ⬝ᵥ x
    have hrhs_expand :
        ∑ i, ∑ j, x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) * x j
        = x ⬝ᵥ (entrywiseExp_hadamardSeries (ι:=ι) R).mulVec x := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

    -- Identify the LHS coefficient structure
    have hlhs_identify (n : ℕ) :
        ∑ i, ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j)
        = (1 / (Nat.factorial n : ℝ)) * (x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum,
            mul_comm, mul_left_comm, mul_assoc]

    -- Put it all together
    rw [← hrhs_expand, ← htsum_eq]
    simp only [hlhs_identify]
    rfl
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
    -- First, show f is summable by combining per-entry summable series over finite i,j
    classical
    -- Reuse the per-entry series s_ij
    let s_ij (i j : ι) (n : ℕ) := (1 / (Nat.factorial n : ℝ)) * hadamardPow (ι:=ι) R n i j
    have hs_ij (i j : ι) : Summable (s_ij i j) := by
      simpa [s_ij, hadamardPow_apply, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using Real.summable_pow_div_factorial (R i j)
    -- HasSum per entry, then push scalars and combine over j and i
    have hHas_ij (i j : ι) : HasSum (s_ij i j) ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) := by
      have h1 : (entrywiseExp_hadamardSeries (ι:=ι) R) i j = tsum (s_ij i j) := by
        simp [entrywiseExp_hadamardSeries, s_ij]
      rw [h1]
      exact (hs_ij i j).hasSum
    have hHas_ij_xj (i j : ι) :
        HasSum (fun n => s_ij i j n * x j) ((entrywiseExp_hadamardSeries (ι:=ι) R) i j * x j) :=
      (hHas_ij i j).mul_right (x j)
    have hHas_ij_xi_xj (i j : ι) :
        HasSum (fun n => x i * (s_ij i j n * x j)) (x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j * x j)) :=
      (hHas_ij_xj i j).mul_left (x i)
    have hHas_sum_j (i : ι) :
        HasSum (fun n => ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j))
               (∑ j, x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) * x j) := by
      apply hasSum_sum
      intro j _
      -- rewrite to match scalar shape
      have := hHas_ij_xi_xj i j
      -- Change s_ij form
      simpa [s_ij, mul_assoc, mul_left_comm, mul_comm]
        using this
    have hHas_sum_i :
        HasSum (fun n => ∑ i, ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j))
               (∑ i, ∑ j, x i * ((entrywiseExp_hadamardSeries (ι:=ι) R) i j) * x j) := by
      apply hasSum_sum
      intro i _
      exact hHas_sum_j i
    -- Summability of f by rewriting the inner sums as the quadratic form
    have hSumm_f : Summable f := by
      -- From hHas_sum_i we know the family of inner sums is summable
      have hSumm_g1 : Summable (fun n => ∑ i, ∑ j,
          (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j)) :=
        hHas_sum_i.summable
      -- Identify with f n = (1/n!) * (x ⬝ᵥ (hadamardPow R n).mulVec x)
      simpa [f, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
             mul_comm, mul_left_comm, mul_assoc]
        using hSumm_g1
    -- Now compare tsum with the singleton partial sum at {1}
    have h_f1_le : f 1 ≤ tsum f := by
      -- bound partial sum by tsum for nonnegative terms
      have h := (Summable.sum_le_tsum (s := ({1} : Finset ℕ)) (f := f)
        (by intro n hn; exact hterm_nonneg n) hSumm_f)
      simpa using h
    -- Use strict positivity of f 1
    exact lt_of_lt_of_le hterm_pos h_f1_le
  -- Conclude
  simpa [hq_tsum] using this

/-- The Hadamard-series entrywise exponential preserves positive semidefiniteness.
    This follows from the positive definite case by continuity: if R is PSD, then
    R + εI is PD for ε > 0, so entrywiseExp_hadamardSeries(R + εI) is PD, and
    taking ε → 0⁺ with continuity of entrywiseExp_hadamardSeries gives that
    entrywiseExp_hadamardSeries(R) is PSD. -/
lemma posSemidef_entrywiseExp_hadamardSeries_of_posSemidef
  (R : Matrix ι ι ℝ) (hR : R.PosSemidef) :
  (entrywiseExp_hadamardSeries (ι:=ι) R).PosSemidef := by
  -- Continuity proof sketch (to be implemented):
  -- 1) Define Rε := R + ε • 1 (i.e., add ε to the diagonal). For ε > 0, Rε is PosDef.
  -- 2) By posDef_entrywiseExp_hadamardSeries_of_posDef, entrywiseExp_hadamardSeries(Rε) is PosDef.
  -- 3) Use continuity of the map R ↦ entrywiseExp_hadamardSeries(R) (coordinatewise continuity + tsum)
  --    to pass to the limit ε → 0⁺ and obtain PosSemidef at ε = 0.
  -- 4) IsHermitian follows termwise, as in the PosDef lemma.
  --
  -- Dependencies to wire up precisely:
  -- - Continuity of R ↦ entrywiseExp_hadamardSeries(R): from continuous_entrywiseExp and
  --   entrywiseExp_eq_hadamardSeries, or by direct dominated convergence on the Hadamard series.
  -- - Stability of PosSemidef under limits of PosDef matrices along ε → 0⁺.
  -- - Standard fact: R PosSemidef ⇒ R + εI PosDef for ε > 0, and diagonal addition is continuous.
  sorry
end Aqft2
