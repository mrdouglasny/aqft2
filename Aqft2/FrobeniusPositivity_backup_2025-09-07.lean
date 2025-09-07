/-
Frobenius positivity: if G is PSD and nonzero, and B is PD, then
⟪G, B⟫ = ∑ j ∑ l G j l * B j l > 0.

We work over ℝ with finite index type ι.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Orthogonal

open scoped BigOperators

set_option linter.unusedSectionVars false

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Helper: Frobenius inner product equals `trace (Gᵀ * B)` (real case). -/
lemma frobenius_eq_trace_transpose_mul
  (G B : Matrix ι ι ℝ) :
  (∑ j, ∑ l, G j l * B j l) = Matrix.trace (G.transpose * B) := by
  classical
  -- Expand the trace of Gᵀ * B
  have htrace : Matrix.trace (G.transpose * B) = ∑ i, ∑ k, G k i * B k i := by
    simp [Matrix.trace, Matrix.mul_apply]
  -- Reorder the Frobenius double sum and rename indices to match htrace
  calc
    (∑ j, ∑ l, G j l * B j l)
        = ∑ l, ∑ j, G j l * B j l := by
          simpa using
            (Finset.sum_comm :
              (∑ j, ∑ l, G j l * B j l) = (∑ l, ∑ j, G j l * B j l))
    _ = ∑ i, ∑ k, G k i * B k i := by
          -- rename bound variables (l→i) in the outer sum, (j→k) in the inner sum
          apply Finset.sum_congr rfl; intro i _; rfl
    _ = Matrix.trace (G.transpose * B) := htrace.symm

/-- Frobenius positivity for a nonzero PSD matrix against a PD matrix (real case).
If `G` is positive semidefinite and nonzero, and `B` is positive definite,
then the Frobenius inner product `∑ j, ∑ l, G j l * B j l` is strictly positive.

High-level proof sketch (to be formalized):
- Use spectral theorem for real symmetric PD matrices: B = U D Uᵀ with D diagonal, diag(λ), λ > 0.
- Let H := Uᵀ G U. Then H is PSD and H ≠ 0 (congruence by invertible U).
- Frobenius inner product equals trace: ⟪G,B⟫ = tr(G B) = tr(H D) = ∑ i λ i * H i i.
- For PSD H, diagonal entries are ≥ 0, and H ≠ 0 ⇒ ∃ i, H i i > 0.
- Since all λ i > 0, the sum is strictly positive.
- This avoids Cholesky and uses spectral decomposition/unitary congruence invariance.
-/
lemma frobenius_pos_of_psd_posdef
  (G B : Matrix ι ι ℝ) (hG_psd : G.PosSemidef) (hG_ne_zero : G ≠ 0) (hB : B.PosDef) :
  0 < ∑ j, ∑ l, G j l * B j l := by
  classical
  -- Step 1: rewrite as a trace
  have hfrob_trace : (∑ j, ∑ l, G j l * B j l) = Matrix.trace (G.transpose * B) :=
    frobenius_eq_trace_transpose_mul G B
  -- Step 2: spectral decomposition of B using positive definite eigenvalues
  have hB_herm : B.IsHermitian := hB.1
  have hd_pos : ∀ i, 0 < hB_herm.eigenvalues i := hB.eigenvalues_pos
  -- Get the spectral decomposition B = U * D * U*
  have hB_spectral := hB_herm.spectral_theorem
  -- Define U and d for cleaner notation
  let U : Matrix ι ι ℝ := hB_herm.eigenvectorUnitary
  let d : ι → ℝ := hB_herm.eigenvalues
  -- Since we're over ℝ, star = transpose and RCLike.ofReal = identity
  have hB_decomp : B = U * Matrix.diagonal d * U.transpose := by
    -- Start with the spectral theorem
    rw [hB_spectral]
    -- Convert star to transpose and RCLike.ofReal to identity over ℝ
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    -- Handle the diagonal mapping
    congr 2
  -- Define H := Uᵀ * G * U
  let H : Matrix ι ι ℝ := U.transpose * G * U
  -- H is PSD: xᵀ H x = (Ux)ᵀ G (Ux) ≥ 0
  have hH_psd : H.PosSemidef := by
    -- H = U.transpose * G * U, and over ℝ transpose = conjTranspose
    rw [show H = U.conjTranspose * G * U from by
        simp [H, Matrix.conjTranspose_eq_transpose_of_trivial]]
    -- Apply congruence invariance: if G is PSD, then U* G U is PSD
    exact hG_psd.conjTranspose_mul_mul_same U
  -- H ≠ 0 (follows from congruence invariance)
  have hH_ne_zero : H ≠ 0 := by
    -- Contrapositive: if H = 0, then G = 0, contradicting hG_ne_zero
    intro hH_zero
    -- H = U.transpose * G * U by definition
    -- The key insight: orthogonal congruence preserves the zero property
    -- If H = 0 and H = U.transpose * G * U, then G = 0
    -- This follows from the invertibility of U (since it's orthogonal)
    -- For now, we use that congruence by invertible matrices preserves non-zeroness
    sorry
  -- Use trace cyclicity to move U, Uᵀ around and reduce to trace(H * D)
  have hG_herm : G.IsHermitian := by
    rw [Matrix.PosSemidef] at hG_psd
    exact hG_psd.1
  have htrace_cycle : Matrix.trace (G.transpose * B) = Matrix.trace (H * (Matrix.diagonal d)) := by
    -- Since G is Hermitian over ℝ, G.transpose = G
    have hG_symm : G.transpose = G := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hG_herm
      exact hG_herm
    rw [hG_symm, hB_decomp]
    -- We need: trace(G * (U * diagonal d * U.transpose)) = trace(H * diagonal d)
    -- First group the multiplication properly
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    -- Now we have: trace((G * U * diagonal d) * U.transpose) = trace(H * diagonal d)
    -- Use trace cyclicity: trace(A * B) = trace(B * A)
    rw [Matrix.trace_mul_comm]
    -- Now: trace(U.transpose * (G * U * diagonal d)) = trace(H * diagonal d)
    rw [Matrix.mul_assoc]
    -- trace(U.transpose * G * (U * diagonal d)) = trace(H * diagonal d)
    rw [← Matrix.mul_assoc]
    -- trace((U.transpose * G) * U * diagonal d) = trace(H * diagonal d)
    rw [Matrix.mul_assoc]
    -- trace((U.transpose * G * U) * diagonal d) = trace(H * diagonal d)
    -- Unfold the definition of H and use associativity
    simp [H, Matrix.mul_assoc]
  -- Expand trace(H * diagonal d) as ∑ i d i * H i i
  have htrace_sum : Matrix.trace (H * Matrix.diagonal d) = ∑ i, d i * H i i := by
    classical
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  -- Diagonal entries of H are ≥ 0 from PSD
  have hdiag_nonneg : ∀ i, 0 ≤ H i i := by
    -- Standard fact: if M is PSD, then M i i ≥ 0 for all i
    -- From the proof of Matrix.posSemidef_diagonal_iff
    intro i
    have := hH_psd.2 (Pi.single i 1)
    simpa using this
  have hdiag_pos_exists : ∃ i, 0 < H i i := by
    -- Contrapositive: if all H i i ≤ 0 and H is PSD (so all H i i ≥ 0), then H i i = 0 for all i
    -- If a PSD matrix has zero diagonal, we need to show it must be zero
    -- This is a somewhat deeper result requiring the PSD characterization
    by_contra h
    push_neg at h
    -- h : ∀ i, H i i ≤ 0, but we also have hdiag_nonneg : ∀ i, 0 ≤ H i i
    -- So H i i = 0 for all i
    have hdiag_zero : ∀ i, H i i = 0 := by
      intro i
      exact le_antisymm (h i) (hdiag_nonneg i)
    -- For a PSD real matrix, if all diagonal entries are 0, then the matrix is 0
    -- This uses the fact that for PSD matrices, H i j = 0 when H i i = H j j = 0
    have H_zero : H = 0 := by
      ext i j
      -- Case 1: diagonal entries
      by_cases h_diag : i = j
      · rw [h_diag]
        simp [hdiag_zero j]
      -- Case 2: off-diagonal entries - simplified for now
      simp
      sorry
    exact hH_ne_zero H_zero
  -- Conclude positivity: all d i > 0, some H i i > 0, and others ≥ 0
  rcases hdiag_pos_exists with ⟨i0, hi0pos⟩
  have hsum_pos : 0 < ∑ i, d i * H i i := by
    -- Since d i0 * H i0 i0 > 0 and all other terms ≥ 0, the sum > 0
    have h_pos : 0 < d i0 * H i0 i0 := mul_pos (hd_pos i0) hi0pos
    -- Split the sum
    rw [← Finset.add_sum_erase Finset.univ (fun i => d i * H i i) (Finset.mem_univ i0)]
    -- The remaining sum is nonnegative
    have h_nonneg : 0 ≤ ∑ x ∈ Finset.univ.erase i0, d x * H x x := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (le_of_lt (hd_pos i)) (hdiag_nonneg i)
    exact add_pos_of_pos_of_nonneg h_pos h_nonneg
  -- Transport back to the original Frobenius sum
  have htrace_pos : 0 < Matrix.trace (H * Matrix.diagonal d) := by
    simpa [htrace_sum] using hsum_pos
  -- Final assembly
  have htrace_pos' : 0 < Matrix.trace (G.transpose * B) := by
    simpa [htrace_cycle] using htrace_pos
  -- Re-express via hfrob_trace
  simpa [hfrob_trace] using htrace_pos'
