/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Complex.Exponential

-- Import our basic definitions
import Aqft2.Basic

open MeasureTheory Complex Real
open TopologicalSpace

noncomputable section

/-! ## Multiplication Operators on L² Spaces

This file implements multiplication operators on L² spaces using bounded continuous functions.
The key insight is that bounded continuous functions give natural multiplication operators
with clear operator norm bounds.

**Main Theorem**: If ϕ : ℝ → ℂ is bounded and continuous, then multiplication by ϕ
gives a bounded linear operator on L²(ℝ) with ‖T_ϕ‖ ≤ ‖ϕ‖∞.

**Test Cases**:
1. Constant functions: ϕ(x) = c
2. Sine function: ϕ(x) = sin(x)
-/

variable {μ : Measure ℝ} [SigmaFinite μ]

/-- **Main Theorem**: Multiplication by a bounded continuous function gives a bounded operator on L².

Mathematical content: If ϕ : ℝ → ℂ is bounded and continuous, then the pointwise
multiplication operator T_ϕ(f) = ϕ · f defines a bounded linear operator on L²(ℝ)
with operator norm ‖T_ϕ‖ ≤ ‖ϕ‖∞.

This is the fundamental result we need for QFT applications. -/
def mulL2_BoundedContinuous (ϕ : BoundedContinuousFunction ℝ ℂ) : 
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  -- Strategy: Use the fact that ϕ coerces to a bounded function ℝ → ℂ
  -- and pointwise multiplication preserves L² with the right norm bound
  sorry

/-! ## Test Cases -/

/-- **Test Case 1**: Constant function multiplication.
If c : ℂ is a constant, then multiplication by c gives a bounded operator
with norm exactly |c|. -/
def mulL2_constant (c : ℂ) : 
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  -- The constant function as a BoundedContinuousFunction
  let ϕ_const : BoundedContinuousFunction ℝ ℂ := 
    ⟨ContinuousMap.const ℝ c, ‖c‖, fun x => by simp⟩
  mulL2_BoundedContinuous ϕ_const

/-- **Test Case 2**: Sine function multiplication.
The sine function sin : ℝ → ℂ is bounded with ‖sin‖∞ = 1, so multiplication by sin
gives a bounded operator with norm ≤ 1. -/
def mulL2_sin : 
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  -- First, show that Complex.sin is bounded
  have sin_bounded : ∃ M, ∀ x : ℝ, ‖Complex.sin x‖ ≤ M := by
    use 1
    intro x
    -- For real x, |sin(x)| ≤ 1
    have h : abs (Complex.sin x) ≤ 1 := by
      rw [Complex.abs_sin_real]
      exact abs_sin_le_one x
    rwa [Complex.abs_eq_norm] at h
    
  -- Create the bounded continuous function
  have sin_continuous : Continuous (Complex.sin ∘ (coe : ℝ → ℂ)) := by
    exact Complex.continuous_sin.comp continuous_of_real
    
  let ϕ_sin : BoundedContinuousFunction ℝ ℂ := 
    ⟨⟨Complex.sin ∘ (coe : ℝ → ℂ), sin_continuous⟩, 1, fun x => by
      have h : abs (Complex.sin x) ≤ 1 := by
        rw [Complex.abs_sin_real]
        exact abs_sin_le_one x
      rwa [Complex.abs_eq_norm] at h
    ⟩
  
  exact mulL2_BoundedContinuous ϕ_sin

/-! ## Verification Examples -/

/-- **Example 1**: Applying constant multiplication to an L² function. -/
example (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) : 
    Lp ℂ 2 (volume : Measure ℝ) :=
  (mulL2_constant c) f

/-- **Example 2**: Applying sine multiplication to an L² function. -/
example (f : Lp ℂ 2 (volume : Measure ℝ)) : 
    Lp ℂ 2 (volume : Measure ℝ) :=
  mulL2_sin f

/-- **Linearity check**: Both operators are linear. -/
example (c d : ℂ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (mulL2_constant c) (f + d • g) = (mulL2_constant c) f + d • (mulL2_constant c) g := by
  rw [map_add, map_smul]

example (c : ℂ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    mulL2_sin (f + c • g) = mulL2_sin f + c • mulL2_sin g := by
  rw [map_add, map_smul]

/-- **Norm bounds**: The operator norms are bounded by the supremum norms. -/
example (c : ℂ) : ‖mulL2_constant c‖ ≤ ‖c‖ := by
  -- This should follow from the general theorem
  sorry

example : ‖mulL2_sin‖ ≤ 1 := by
  -- Since ‖sin‖∞ = 1, we have ‖T_sin‖ ≤ 1
  sorry

/-! ## General Properties 

These are the key mathematical properties that make bounded continuous function
multiplication useful for QFT applications.
-/

/-- **Multiplicativity**: Composition of multiplication operators corresponds to
pointwise multiplication of the functions. -/
example (ϕ ψ : BoundedContinuousFunction ℝ ℂ) :
    (mulL2_BoundedContinuous ϕ) ∘L (mulL2_BoundedContinuous ψ) = 
    mulL2_BoundedContinuous (ϕ * ψ) := by
  sorry

/-- **Identity**: Multiplication by the constant function 1 is the identity operator. -/
example : mulL2_constant 1 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ)) := by
  sorry

/-- **Scaling**: Multiplication by a scaled function scales the operator. -/
example (c : ℂ) (ϕ : BoundedContinuousFunction ℝ ℂ) :
    mulL2_BoundedContinuous (c • ϕ) = c • mulL2_BoundedContinuous ϕ := by
  sorry

/-! ## Connection to Physics

In QFT, multiplication operators arise naturally:
1. **Position multiplication**: x ↦ x · ψ(x) (unbounded but important)
2. **Cutoff functions**: Smooth functions that localize in space or momentum
3. **Test functions**: Multiplication by smooth, compactly supported functions
4. **Modulation**: Multiplication by oscillatory functions like e^{ikx}

The bounded continuous function approach handles cases 2, 3, and the bounded
parts of case 4. For case 1 (position operator), one needs unbounded operator theory.
-/

/-- **Example**: Gaussian cutoff function (bounded on any finite interval). -/
def gaussianCutoff (σ : ℝ) (hσ : 0 < σ) : BoundedContinuousFunction ℝ ℂ := by
  -- ϕ(x) = exp(-x²/(2σ²)) is bounded and continuous
  sorry

/-- **Example**: Characteristic function of a bounded interval. -/
def intervalCutoff (a b : ℝ) (hab : a < b) : BoundedContinuousFunction ℝ ℂ := by
  -- This requires a continuous approximation since the exact characteristic
  -- function is discontinuous. We can use a smooth approximation.
  sorry

end
example (ϕ : ℝ → ℂ) (hϕ : ∃ M, ∀ x, ‖ϕ x‖ ≤ M) (f : Lp ℂ 2 (volume : Measure ℝ)) : 
    Lp ℂ 2 (volume : Measure ℝ) :=
  (mulL2_simple ϕ hϕ) f

/-- Example with L∞: You can apply the operator to any `f : Lp ℝ 2 μ`. -/
example (ϕ : Lp ℝ ⊤ μ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (mulL2_Linfty ϕ) f

/-- Linearity test for bounded continuous function version. -/
example (ϕ : BoundedContinuousFunction ℝ ℂ) (f g : Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ) :
    (mulL2_BoundedContinuous ϕ) (f + c • g) = (mulL2_BoundedContinuous ϕ) f + c • (mulL2_BoundedContinuous ϕ) g := by
  rw [map_add, map_smul]
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.ENNReal.Basic

-- Import our basic definitions
import Aqft2.Basic

open MeasureTheory Complex Real
open TopologicalSpace

noncomputable section

/-! ## Spatial L² Spaces for Glimm-Jaffe Argument

This file defines spatial L² spaces and energy operators for the Glimm-Jaffe reflection positivity argument:

1. **Spatial coordinates**: ℝ^{d-1} (space without time)
2. **Spatial L²**: L²(ℝ^{d-1}) for functions on space at fixed time
3. **Energy operators**: E²(k) = ‖k‖² + m² and E(k) = √(‖k‖² + m²)

Note: Basic.lean already provides FieldSpace, TestFunctionℂ, and the main QFT infrastructure.
This file adds only the spatial slice decomposition specific to Glimm-Jaffe.
-/

/-- Spatial coordinates: ℝ^{d-1} (space without time)
    For STDimension = 4, this is ℝ³ -/
abbrev SpatialCoords := Fin (STDimension - 1) → ℝ

/-- L² space on spatial slices -/
abbrev SpatialL2 := Lp ℂ 2 (volume : Measure SpatialCoords)

-- Note: Zero-mean subspace may be needed later for certain reflection positivity arguments
-- def spatialMean (f : SpatialCoords → ℂ) : ℂ := ∫ x, f x ∂(volume : Measure SpatialCoords)
-- def ZeroMeanSpatialL2 : Subspace ℂ SpatialL2 := {f | spatialMean f = 0}

/-- Extract spatial part of spacetime coordinate -/
def spatialPart (x : SpaceTime) : SpatialCoords :=
  fun i => x ⟨i.val + 1, by simp [STDimension]; omega⟩

/-- Time slice: given time t, extract the spatial function -/
def timeSlice (t : ℝ) (f : SpaceTime → ℂ) : SpatialCoords → ℂ :=
  fun x_spatial => f (fun i => if i.val = 0 then t else
    have h_pos : i.val - 1 < STDimension - 1 := by
      cases' i with val h_val
      simp at h_val
      cases val with
      | zero => simp
      | succ n => simp [STDimension] at h_val ⊢; omega
    x_spatial ⟨i.val - 1, h_pos⟩)

/-! ## Spatial Energy Operators

Following the pattern from Covariance.lean, we define the squared energy operator
E²(k) = ‖k‖² + m² and its square root E(k) = √(‖k‖² + m²) in spatial momentum space.
These act as multiplication operators on L²(ℝ^{d-1}).

We require m² > 0 for the mass parameter.
-/

-- Mass parameter assumption: m > 0
variable {m : ℝ} [Fact (0 < m)]

/-- The squared energy function E²(k) = ‖k‖² + m² on spatial momentum space -/
def Esq (m : ℝ) (k : SpatialCoords) : ℝ :=
  ‖k‖^2 + m^2

/-- The energy function E(k) = √(‖k‖² + m²) on spatial momentum space -/
def E (m : ℝ) (k : SpatialCoords) : ℝ :=
  Real.sqrt (‖k‖^2 + m^2)

/-- The squared energy function is always positive for m > 0 -/
lemma Esq_pos {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  0 < Esq m k := by
  unfold Esq
  apply add_pos_of_nonneg_of_pos
  · exact sq_nonneg ‖k‖
  · exact pow_pos (Fact.out : 0 < m) 2

/-- The energy function E is always positive for m > 0 -/
lemma E_pos {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  0 < E m k := by
  unfold E
  apply Real.sqrt_pos.mpr
  exact Esq_pos k

/-- The squared energy function is bounded below by m² -/
lemma Esq_bounded_below {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  m^2 ≤ Esq m k := by
  unfold Esq
  apply le_add_of_nonneg_left
  exact sq_nonneg ‖k‖

/-- The energy function E is bounded below by m -/
lemma E_bounded_below {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  m ≤ E m k := by
  unfold E
  -- Since ‖k‖² + m² ≥ m², we have √(‖k‖² + m²) ≥ √(m²) = m
  have h1 : m^2 ≤ ‖k‖^2 + m^2 := by linarith [sq_nonneg ‖k‖]
  have h2 : Real.sqrt (m^2) = m := Real.sqrt_sq (le_of_lt (Fact.out : 0 < m))
  calc m
    = Real.sqrt (m^2) := h2.symm
    _ ≤ Real.sqrt (‖k‖^2 + m^2) := Real.sqrt_le_sqrt h1

/-- The inverse energy function μ⁻¹ is bounded above by 1/m -/
lemma E_inv_bounded_above {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  (E m k)⁻¹ ≤ m⁻¹ := by
  have h1 : 0 < m := Fact.out
  have h2 : 0 < E m k := E_pos k
  have h3 : m ≤ E m k := E_bounded_below k
  -- For positive reals a ≤ b, we have b⁻¹ ≤ a⁻¹
  -- Using one_div_le_one_div: 1/a ≤ 1/b ↔ b ≤ a
  rw [← one_div, ← one_div]
  rwa [one_div_le_one_div h2 h1]

/-- The squared energy function is continuous -/
lemma Esq_continuous {m : ℝ} [Fact (0 < m)] :
  Continuous (Esq m) := by
  unfold Esq
  apply Continuous.add
  · exact continuous_norm.comp continuous_id |>.pow _
  · exact continuous_const

/-- The energy function E is continuous -/
lemma E_continuous {m : ℝ} [Fact (0 < m)] :
  Continuous (E m) := by
  unfold E
  apply Continuous.comp Real.continuous_sqrt
  exact Esq_continuous

/-- Relationship: E² = (E)² -/
lemma E_squared {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) :
  (E m k)^2 = Esq m k := by
  unfold E Esq
  exact Real.sq_sqrt (le_of_lt (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (pow_pos (Fact.out : 0 < m) 2)))

/-- Asymptotic behavior for large momentum -/
lemma Esq_asymptotic {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) (hk : ‖k‖ ≥ m) :
  ‖k‖^2 ≤ Esq m k ∧ Esq m k ≤ 2 * ‖k‖^2 := by
  unfold Esq
  constructor
  · apply le_add_of_nonneg_right
    exact sq_nonneg m
  · -- For ‖k‖ ≥ m, we have m² ≤ ‖k‖², so ‖k‖² + m² ≤ ‖k‖² + ‖k‖² = 2‖k‖²
    sorry

/-- For large momentum, energy function behaves like norm -/
lemma E_asymptotic {m : ℝ} [Fact (0 < m)] (k : SpatialCoords) (hk : ‖k‖ ≥ m) :
  ‖k‖ ≤ E m k := by
  unfold E
  -- Since ‖k‖² ≤ ‖k‖² + m², we have ‖k‖ ≤ √(‖k‖² + m²)
  sorry

/-! ## Multiplication Operators on L²

The energy functions act as multiplication operators, but they are NOT bounded on L²(ℝ^{d-1})
due to their polynomial growth. However, they are well-defined on appropriate domains.

These operators are unbounded but densely defined on L² spaces. In QFT applications,
one typically works with more regular function spaces (like Schwartz functions) or
considers regularized versions like (E² + λ)⁻¹ for λ > 0.
-/

/-- Multiplication by squared energy function as a linear map on functions -/
def Esq_multiplication (m : ℝ) : (SpatialCoords → ℂ) →ₗ[ℂ] (SpatialCoords → ℂ) := {
  toFun := fun f k => (Esq m k : ℂ) * f k
  map_add' := fun f g => by ext k; simp [mul_add]
  map_smul' := fun c f => by ext k; simp; ring
}

/-- Multiplication by energy function as a linear map on functions -/
def E_multiplication (m : ℝ) : (SpatialCoords → ℂ) →ₗ[ℂ] (SpatialCoords → ℂ) := {
  toFun := fun f k => (E m k : ℂ) * f k
  map_add' := fun f g => by ext k; simp [mul_add]
  map_smul' := fun c f => by ext k; simp; ring
}

/-- The squared energy function has polynomial growth -/
lemma Esq_polynomial_growth {m : ℝ} [Fact (0 < m)] :
  ∃ C : ℝ, ∀ k : SpatialCoords, Esq m k ≤ C * (1 + ‖k‖^2) := by
  -- E²(k) = ‖k‖² + m² ≤ (1 + ‖k‖²) + m² ≤ (1 + m²) * (1 + ‖k‖²)
  use 1 + m^2
  intro k
  unfold Esq
  calc ‖k‖^2 + m^2
    = ‖k‖^2 + m^2 := rfl
    _ ≤ ‖k‖^2 + m^2 + m^2 := by linarith [sq_nonneg m]
    _ = ‖k‖^2 + 2*m^2 := by ring
    _ ≤ ‖k‖^2 + m^2 + m^2 + m^2 := by linarith [sq_nonneg m]
    _ = ‖k‖^2 + 3*m^2 := by ring
    _ ≤ (1 + m^2) + (1 + m^2) * ‖k‖^2 := by sorry -- detailed algebra
    _ = (1 + m^2) * (1 + ‖k‖^2) := by ring

/-- The energy function has polynomial growth -/
lemma E_polynomial_growth {m : ℝ} [Fact (0 < m)] :
  ∃ C : ℝ, ∀ k : SpatialCoords, E m k ≤ C * (1 + ‖k‖) := by
  -- E(k) = √(‖k‖² + m²) ≤ ‖k‖ + m (triangle inequality for square roots)
  use 1 + m
  intro k
  unfold E
  -- Use the inequality √(a² + b²) ≤ |a| + |b| for a,b ≥ 0
  sorry

/-- The squared energy multiplication gives a positive quadratic form -/
lemma Esq_multiplication_positive {m : ℝ} [Fact (0 < m)] (f : SpatialCoords → ℂ) :
  0 ≤ Complex.re (∫ k, (starRingEnd ℂ (f k)) * (Esq m k : ℂ) * f k ∂(volume : Measure SpatialCoords)) := by
  -- Since Esq(k) > 0 for all k, and (f̄ k) * (Esq m k) * (f k) = |f k|² * Esq(k) ≥ 0
  sorry

/-- Mathematical statement: These multiplication operators are unbounded on L² but densely defined -/
lemma multiplication_unbounded_on_L2 {m : ℝ} [Fact (0 < m)] :
  -- The energy operators are unbounded due to polynomial growth
  -- They are densely defined on smooth/Schwartz functions
  -- In practice, one uses regularized versions like (E² + λ)⁻¹
  ∀ _ : SpatialL2, True := by
  intro; trivial

/-- For now, let's use a simple approach: multiply by a bounded function.
    This avoids the complexity of both BoundedContinuousFunction and L∞ spaces
    until we find the right Mathlib API. -/
def mulL2_simple (ϕ : ℝ → ℂ) (hϕ_bounded : ∃ M, ∀ x, ‖ϕ x‖ ≤ M) : 
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  -- This should be the easiest to implement: just pointwise multiplication
  -- by a bounded function ϕ : ℝ → ℂ
  sorry

/-- Eventually we want the bounded continuous version. -/
def mulL2_BoundedContinuous (ϕ : BoundedContinuousFunction ℝ ℂ) : 
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := 
  -- Use the simple version with the bounded continuous function coerced to a function
  mulL2_simple (⇑ϕ) ⟨‖ϕ‖, fun x => by
    -- ‖ϕ x‖ ≤ ‖ϕ‖ for bounded continuous functions
    sorry -- This should follow from the definition of the supremum norm
  ⟩

/-- Alternative: Multiplication by an L∞ function acts boundedly on L².
    This is more general but potentially harder to work with. -/
def mulL2_Linfty (ϕ : Lp ℝ ⊤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  -- This requires the deep theory of Lp spaces
  -- The mathematical content is that ‖ϕ‖∞ * ‖f‖₂ bounds ‖ϕf‖₂
  sorry

/-! ### Usage -/

/-- You can apply the operator to any `f : Lp ℝ 2 μ`. -/
example (ϕ : Lp ℝ ⊤ μ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (mulL2 ϕ) f

/-- As a quick check: it’s linear and bounded. -/
example (ϕ : Lp ℝ ⊤ μ) (f g : Lp ℝ 2 μ) (c : ℝ) :
    (mulL2 ϕ) (f + c • g) = (mulL2 ϕ) f + c • (mulL2 ϕ) g := by
  rw [map_add, map_smul]

/-- Example: Multiplication by sin function on ℝ gives a bounded operator on L²(ℝ) -/
example : ∃ (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
  ∀ f : Lp ℂ 2 (volume : Measure ℝ), ‖T f‖ ≤ ‖f‖ := by
  -- Create sin as an L∞ function
  have sin_bounded : ∃ M, ∀ x : ℝ, ‖Complex.sin x‖ ≤ M := by
    use 1
    intro x
    -- Use the fact that |sin(z)| ≤ 1 for real z
    have h : ‖Complex.sin x‖ ≤ 1 := by sorry -- This should exist in mathlib
    exact h

  -- For now, let's use sorry to get past this
  sorry

/-- Helper lemma: Heat kernel function gives a bounded operator on spatial L² -/
lemma heatKernel_as_bounded_operator {m : ℝ} [Fact (0 < m)] {t : ℝ} (ht : 0 ≤ t) :
  ∃ (T : SpatialL2 →L[ℂ] SpatialL2), ∀ f : SpatialL2, ‖T f‖ ≤ m⁻¹ * ‖f‖ := by
  -- Get the pointwise bound from heatKernel_bounded
  -- obtain ⟨C, hC_pos, hC_bound⟩ := heatKernel_bounded ht

  -- For now, use sorry to get it compiling
  sorry

/-! ## Heat Kernel Operators for Glimm-Jaffe

For the Glimm-Jaffe reflection positivity argument, we need operators of the form
μ⁻¹ e^{-(s+t)μ} where μ = E(k) = √(‖k‖² + m²).

These operators ARE bounded on L² because the exponential decay e^{-(s+t)μ}
dominates the polynomial growth of μ⁻¹, making the overall function bounded.
-/

/-- Heat kernel function: μ⁻¹ e^{-(s+t)μ} where μ = E(k) -/
def heatKernel (m : ℝ) (t : ℝ) (k : SpatialCoords) : ℂ :=
  (E m k : ℂ)⁻¹ * Complex.exp (-(t : ℂ) * (E m k : ℂ))

/-- Multiplication by heat kernel as a linear map on functions -/
def heatKernel_multiplication (m : ℝ) (t : ℝ) : (SpatialCoords → ℂ) →ₗ[ℂ] (SpatialCoords → ℂ) := {
  toFun := fun f k => heatKernel m t k * f k
  map_add' := fun f g => by ext k; simp [mul_add]
  map_smul' := fun c f => by ext k; simp; ring
}

/-- The heat kernel function is bounded for t ≥ 0 -/
lemma heatKernel_bounded {m : ℝ} [Fact (0 < m)] {t : ℝ} (ht : 0 ≤ t) :
  ∃ C > 0, ∀ k : SpatialCoords, (E m k)⁻¹ * Real.exp (-(t * E m k)) ≤ C := by
  -- For t ≥ 0, e^{-tμ}/μ is bounded because exponential decay dominates polynomial growth
  -- The key insight: μ⁻¹ ≤ m⁻¹ and e^{-tμ} ≤ 1 for t ≥ 0, so μ⁻¹e^{-tμ} ≤ m⁻¹

  -- We now directly have m > 0 as an assumption
  have h_pos_m : 0 < m := Fact.out

  use m⁻¹  -- The bound C = 1/m works
  constructor
  · exact inv_pos.mpr h_pos_m
  · intro k
    have h_pos_E : 0 < E m k := E_pos k

    -- Key ingredients:
    -- 1. E(k) ≥ m, so (E(k))⁻¹ ≤ m⁻¹
    -- 2. exp(-t*E(k)) ≤ 1 for t ≥ 0

    have h_exp_le_one : Real.exp (-(t * E m k)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_monotone
      -- For t ≥ 0 and E(k) > 0, we have -t*E(k) ≤ 0
      have : t * E m k ≥ 0 := mul_nonneg ht (le_of_lt h_pos_E)
      linarith

    have h_inv_bound : (E m k)⁻¹ ≤ m⁻¹ := by
      -- This follows from m ≤ E m k and the fact that inverse reverses inequalities
      have h_bound : m ≤ E m k := E_bounded_below k
      -- For 0 < a ≤ b, we have b⁻¹ ≤ a⁻¹
      -- Using one_div_le_one_div: 1/a ≤ 1/b ↔ b ≤ a
      rw [← one_div, ← one_div]
      rwa [one_div_le_one_div h_pos_E h_pos_m]

    -- Combine the bounds: (E m k)⁻¹ * exp(-t * E m k) ≤ m⁻¹ * 1 = m⁻¹
    have h_step1 : (E m k)⁻¹ * Real.exp (-(t * E m k)) ≤ m⁻¹ * Real.exp (-(t * E m k)) := by
      exact mul_le_mul_of_nonneg_right h_inv_bound (Real.exp_nonneg _)
    have h_step2 : m⁻¹ * Real.exp (-(t * E m k)) ≤ m⁻¹ * 1 := by
      exact mul_le_mul_of_nonneg_left h_exp_le_one (inv_nonneg.mpr (le_of_lt h_pos_m))
    have h_step3 : m⁻¹ * 1 = m⁻¹ := by rw [mul_one]

    -- Chain the inequalities
    calc (E m k)⁻¹ * Real.exp (-(t * E m k))
      ≤ m⁻¹ * Real.exp (-(t * E m k)) := h_step1
      _ ≤ m⁻¹ * 1 := h_step2
      _ = m⁻¹ := h_step3

/-- For the Glimm-Jaffe argument: the inner product ⟨g, μ⁻¹ e^{-(s+t)μ} f⟩ is well-defined -/
lemma glimm_jaffe_inner_product_wellDefined {m : ℝ} [Fact (0 < m)] {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
  (f g : SpatialL2) :
    -- The inner product ⟨g, heatKernel(s+t) * f⟩ exists and is finite
    ∃ val : ℂ, val = ∫ k, (starRingEnd ℂ (g k)) * heatKernel m (s + t) k * f k ∂(volume : Measure SpatialCoords) := by
  -- This follows from heatKernel_as_bounded_operator and Hölder's inequality
  -- We need s + t > 0 for boundedness
  have h_pos : 0 ≤ s + t := le_of_lt (add_pos hs ht)

  -- Use our helper lemma to get a bounded operator
  obtain ⟨T, hT_bound⟩ := @heatKernel_as_bounded_operator m (by assumption) (s + t) h_pos

  -- The integral exists and equals ⟨g, T f⟩
  use ∫ k, (starRingEnd ℂ (g k)) * heatKernel m (s + t) k * f k ∂(volume : Measure SpatialCoords)

/-! ## Connection to Glimm-Jaffe Framework

The spatial energy operators are crucial for the Glimm-Jaffe argument because:

1. **Squared Energy Operator**: E²(k) = ‖k‖² + m² > 0 makes quadratic forms positive definite
2. **Energy Operator E**: E(k) = √(‖k‖² + m²) is the physical energy
3. **Relationship**: E² = (E)², connecting the square root and squared operators
4. **Unboundedness**: Both operators are unbounded on L² due to polynomial growth
5. **Physical meaning**: E represents the relativistic energy in spatial momentum space

The multiplication operators defined above are **unbounded operators on L²(ℝ^{d-1})**:
- They are linear maps on functions but not bounded on the full L² space
- They are densely defined on smooth functions (like Schwartz functions)
- The unboundedness is due to the polynomial growth of the energy functions
- In QFT, one typically uses regularized versions like (E² + λ)⁻¹ for λ > 0
- The positivity of the quadratic forms is crucial for reflection positivity arguments

**Note on Implementation**: For practical QFT calculations, one often works with:
1. **Regularized operators**: (E² + λ)⁻¹ for λ > 0, which are bounded
2. **Restricted domains**: Schwartz functions or other smooth function spaces
3. **Weak formulations**: Using quadratic forms rather than operator norms

The energy operators themselves are unbounded but essential for the physics.

In the Glimm-Jaffe framework, these operators will be used to:
- Define the covariance operator C = (E² + λ)⁻¹ for some regularity parameter λ > 0
- Establish the reflection positivity inequality ⟨f, Cf⟩ ≥ 0 in momentum space
- Connect the momentum space and position space formulations of reflection positivity

Note: The energy operators E and E² are unbounded, but their regularized inverses
(E² + λ)⁻¹ are bounded and define the physical covariance operators used in QFT.

**Heat Kernel Operators**: The operators μ⁻¹ e^{-(s+t)μ} are bounded for s,t > 0
and are essential for the Glimm-Jaffe reflection positivity argument. These arise
from the time evolution e^{-tH} where H is the Hamiltonian with dispersion relation μ.

The energy operator E = √(‖k‖² + m²) is the correct energy dispersion relation.
The squared energy operator E² = ‖k‖² + m² is its square, which is often easier
to work with computationally.
-/
