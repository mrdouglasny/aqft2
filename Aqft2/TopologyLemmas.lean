/-
Topology lemmas for continuity arguments and regularization.

General topology principles for extending properties from positive definite to
positive semidefinite matrices via continuity and closure arguments.
-/

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.Real
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

open Topology Filter Set
open scoped BigOperators

namespace Aqft2

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

lemma nonneg_at_zero_of_pos_on_Ioi
  {Y : ℝ → ℝ} (hcont : ContinuousAt Y 0)
  (hpos : ∀ ⦃x⦄, 0 < x → 0 < Y x) :
  0 ≤ Y 0 := by
  have htend : Tendsto Y (𝓝[>] (0 : ℝ)) (𝓝 (Y 0)) := hcont.tendsto_nhdsWithin
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), Y x ∈ Ici (0 : ℝ) := by
    refine eventually_of_forall (fun x hx => ?_)
    exact le_of_lt (hpos hx)
  exact (isClosed_Ici).mem_of_tendsto htend hev

lemma nonneg_on_Ici_of_pos_on_Ioi
  {Y : ℝ → ℝ} (hcont : Continuous Y)
  (hpos : ∀ ⦃x⦄, 0 < x → 0 < Y x) :
  ∀ ⦃x⦄, 0 ≤ x → 0 ≤ Y x := by
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | rfl
  · exact le_of_lt (hpos hlt)
  · simpa using nonneg_at_zero_of_pos_on_Ioi (hcont.continuousAt) hpos

/-- Regularization in ℝ: if `A` is PSD then `A + ε I` is PD for ε>0. -/
lemma posDef_regularize_real {ι : Type u} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (A + ε • (1 : Matrix ι ι ℝ)).PosDef := by
  classical
  -- Hermitian part
  have hHerm : (A + ε • (1 : Matrix ι ι ℝ)).IsHermitian := by
    have h1 : (1 : Matrix ι ι ℝ).IsHermitian := by
      simpa using (Matrix.isHermitian_one : (Matrix.IsHermitian (1 : Matrix ι ι ℝ)))
    simpa using (hA.1.add (h1.smul _))
  -- Strict positivity of quadratic form
  refine ⟨hHerm, ?_⟩
  intro x hx
  have hA_nonneg : 0 ≤ x ⬝ᵥ A.mulVec x := hA.2 x
  -- Evaluate (ε I)
  have hId : (1 : Matrix ι ι ℝ).mulVec x = x := by
    funext i; simp [Matrix.mulVec]
  have hId_quad : x ⬝ᵥ (ε • (1 : Matrix ι ι ℝ)).mulVec x = ε * (∑ i, x i * x i) := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Expand (A + εI)
  have hsum : x ⬝ᵥ (A + ε • (1 : Matrix ι ι ℝ)).mulVec x
      = x ⬝ᵥ A.mulVec x + x ⬝ᵥ (ε • (1 : Matrix ι ι ℝ)).mulVec x := by
    simp [Matrix.mulVec, dotProduct, add_mul, mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]
  -- Sum of nonneg and strictly pos is pos
  have hx_coord : ∃ i, x i ≠ 0 := by
    classical
    by_contra hforall
    push_neg at hforall
    have : x = 0 := funext (fun i => by simpa using hforall i)
    exact hx this
  rcases hx_coord with ⟨i0, hi0⟩
  have hsum_sq_pos : 0 < ∑ i, x i * x i := by
    have hnn : ∀ i, 0 ≤ x i * x i := by intro i; exact mul_self_nonneg _
    have hpos_i0 : 0 < x i0 * x i0 := by
      have : (x i0) ≠ 0 := hi0
      exact mul_self_pos.mpr this
    exact Finset.sum_pos (fun i _ => hnn i) ⟨i0, by simp, by simpa using hpos_i0⟩
  have hpos_eps : 0 < ε * (∑ i, x i * x i) := mul_pos_of_pos_of_pos hε hsum_sq_pos
  have : 0 < x ⬝ᵥ (A + ε • (1 : Matrix ι ι ℝ)).mulVec x := by
    have := add_lt_add_of_le_of_lt hA_nonneg (by simpa [hId_quad] using hpos_eps)
    simpa [hsum] using this
  exact this

/-- Generic regularization lemma: if `A` is PSD then `A + ε I` is PD for ε>0. -/
lemma posDef_regularize {A : Matrix n n 𝕜} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + (IsROrC.ofReal ε) • (1 : Matrix n n 𝕜)).PosDef := by
  sorry -- Proof would use spectral decomposition or direct computation

/-- Generic extension principle: if a closed property holds on PD, it holds on PSD. -/
lemma extend_PD_to_PSD
  {β : Type*} [TopologicalSpace β]
  (f : Matrix n n 𝕜 → β) (hf : Continuous f)
  (C : Set β) (hC : IsClosed C)
  (hPD : ∀ {B : Matrix n n 𝕜}, B.PosDef → f B ∈ C)
  {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
  f A ∈ C := by
  -- ε ↦ A + εI tends to A as ε → 0⁺; compose with f
  have ht : Tendsto (fun ε : ℝ => f (A + (IsROrC.ofReal ε) • (1 : Matrix n n 𝕜))))
      (𝓝[>] 0) (𝓝 (f A)) := by
    refine (hf.comp ?_).tendsto_nhdsWithin
    exact continuous_const.add ((IsROrC.continuous_ofReal.comp continuous_id).smul continuous_const)
  -- property holds along the right-neighborhood (all ε>0)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f (A + (IsROrC.ofReal ε) • (1 : Matrix n n 𝕜)) ∈ C :=
    Filter.eventually_of_forall (fun ε hε => hPD (posDef_regularize hA hε))
  -- closed-set limit
  exact hC.mem_of_tendsto ht hev

end Aqft2
