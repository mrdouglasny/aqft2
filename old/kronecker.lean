/-
Detailed algebraic proof for Kronecker-like quadratic sum manipulation.

This file contains the complex sum rearrangement proof that was extracted from
SchurProduct.lean to keep the main file focused. The proof here is kept for
reference but is not used in the main theorem.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

set_option linter.unusedSectionVars false

open Complex
open scoped BigOperators

namespace Aqft2

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Kronecker-like product kernel on the product index: (i,j),(k,l) ↦ A i k * B j l. -/
@[simp] def kronLike (A B : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  fun p q => A p.1 q.1 * B p.2 q.2

/-- Column slice of a vector indexed by ι×ι: take j and view i ↦ y (i,j). -/
@[simp] def colSlice (y : ι × ι → ℝ) (j : ι) : ι → ℝ := fun i => y (i, j)

/-- Finite sum over pairs equals iterated double sum over coordinates (binderless sums). -/
lemma sum_pairs_eq_double (g : ι × ι → ℝ) :
  (∑ p, g p) = ∑ i, ∑ j, g (i, j) := by
  classical
  -- Expand both sides to Finset.univ sums and use sum_product
  show (Finset.univ.sum (fun p : ι × ι => g p))
      = (Finset.univ.sum (fun i : ι => Finset.univ.sum (fun j : ι => g (i, j))))
  -- Replace g p by g (p.1, p.2)
  have : (Finset.univ.sum (fun p : ι × ι => g p))
        = (Finset.univ.sum (fun p : ι × ι => g (p.1, p.2))) := by
    simp
  calc
    Finset.univ.sum (fun p : ι × ι => g p)
        = Finset.univ.sum (fun p : ι × ι => g (p.1, p.2)) := this
    _ = (Finset.univ.product (Finset.univ)).sum (fun p : ι × ι => g (p.1, p.2)) := by rfl
    _ = Finset.univ.sum (fun i : ι => Finset.univ.sum (fun j : ι => g (i, j))) := by
      rw [← Finset.sum_product]
      congr

/-- Compute (kronLike A B).mulVec y at a pair (i,j) as a double sum (binderless sums). -/
lemma kronLike_mulVec
  (A B : Matrix ι ι ℝ) (y : ι × ι → ℝ) (i j : ι) :
  ((kronLike (ι:=ι) A B).mulVec y) (i, j)
  = ∑ k, ∑ l, (A i k * B j l) * y (k, l) := by
  classical
  -- Start from definition
  have : (∑ q, (A i q.1 * B j q.2) * y q)
      = ∑ k, ∑ l, (A i k * B j l) * y (k, l) := by
    simpa using sum_pairs_eq_double (g := fun q => (A i q.1 * B j q.2) * y q)
  simpa [Matrix.mulVec, kronLike] using this

/-- Detailed algebraic proof attempt for kronLike_quadratic_sum (for reference). -/
lemma kronLike_quadratic_sum_detailed_attempt
  (A B : Matrix ι ι ℝ) (y : ι × ι → ℝ) :
  (∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p)
  = ∑ j, ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * B j l := by
  classical
  -- Turn the outer sum over pairs into a double sum
  have hsum_pairs :
      (∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p)
      = ∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j) := by
    simpa using sum_pairs_eq_double (g := fun p => y p * ((kronLike (ι:=ι) A B).mulVec y) p)
  -- Use the computed form of mulVec at (i,j).
  have hmul :
      (∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j))
      = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp [kronLike_mulVec]
  -- Distribute and reorder sums to isolate B j l and the A-quadratic form in i,k.
  have hdist :
      (∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)))
      = ∑ j, ∑ l, (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
    -- Push factors and pull out constants with respect to the inner sums
    -- Step 1: distribute the inner double sum and factor B j l
    have hstep1 :
        (∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)))
        = ∑ i, ∑ j, ∑ l, (y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      -- work pointwise in (i,j)
      calc
        y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l))
            = ∑ l, y (i, j) * (∑ k, (A i k * B j l) * y (k, l)) := by
              -- pull the l-sum out first
              simp [Finset.mul_sum]
        _ = ∑ l, y (i, j) * (∑ k, (A i k * y (k, l)) * B j l) := by
              -- for fixed l, reorder products inside the k-sum
              apply Finset.sum_congr rfl; intro l _
              simp [mul_left_comm, mul_comm, mul_assoc]
        _ = ∑ l, (y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
              -- factor the constant B j l out of the inner k-sum
              apply Finset.sum_congr rfl; intro l _
              simp [Finset.sum_mul, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
    -- Step 2: bring (j,l) outside and then factor B j l out of the i-sum
    have hstep2 :
        (∑ i, ∑ j, ∑ l, (y (i, j) * (∑ k, A i k * y (k, l))) * B j l)
        = ∑ j, ∑ l, ∑ i, (y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
      -- swap the first and second sums
      rw [Finset.sum_comm]
    have hstep3 :
        (∑ j, ∑ l, ∑ i, (y (i, j) * (∑ k, A i k * y (k, l))) * B j l)
        = ∑ j, ∑ l, (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := by
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      simp [Finset.sum_mul]
    -- finish hdist
    simpa [hstep2] using hstep1.trans hstep3
  -- Identify the inner expression with colSlice and A.mulVec
  have hid : ∀ j l,
      (∑ i, y (i, j) * (∑ k, A i k * y (k, l)))
      = (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) := by
    intro j l
    simp [colSlice, Matrix.mulVec, Finset.mul_sum]
  -- Chain equalities
  calc
    (∑ p, y p * ((kronLike (ι:=ι) A B).mulVec y) p)
        = ∑ i, ∑ j, y (i, j) * ((kronLike (ι:=ι) A B).mulVec y) (i, j) := hsum_pairs
    _ = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) := hmul
    _ = ∑ j, ∑ l, (∑ i, y (i, j) * (∑ k, A i k * y (k, l))) * B j l := hdist
    _ = ∑ j, ∑ l, (∑ i, (colSlice (ι:=ι) y j) i * (A.mulVec (colSlice (ι:=ι) y l)) i) * B j l := by
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      simp [hid]

end Aqft2
