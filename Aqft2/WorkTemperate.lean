/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

# Working file for freePropagator_temperate_growth proof

This is a minimal working file to complete the proof of `freePropagator_temperate_growth`.
The goal is to prove that the free propagator has temperate growth, which requires showing
that all derivatives are polynomially bounded.

## Goal

Complete the `sorry` at line 102 in the `succ n'` case of `freePropagator_temperate_growth`.

The goal is:
```
⊢ ‖iteratedFDeriv ℝ (n' + 1) (fun k ↦ ↑(freePropagatorMomentum m k)) k‖ ≤ 1 / m ^ 2 * (1 + ‖k‖) ^ 0
```

This simplifies to showing that the (n'+1)-th derivative of `freePropagatorMomentum` is bounded by
`1/m²` (since `(1 + ‖k‖)^0 = 1`).

## Strategy

The function `f(k) = 1/(‖k‖² + m²)` has derivatives that decay faster than any polynomial.
Since we're only asking for polynomial bounds (degree 0 in this case), the derivatives are
certainly bounded.

Possible approaches:
1. Use that `f` is a Schwartz function (decays faster than any polynomial)
2. Explicitly compute bounds on the derivatives using the chain rule
3. Use existing lemmas about derivatives of rational functions

-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Complex.Basic

open MeasureTheory Complex Real
open scoped Real InnerProductSpace

-- Spacetime dimension
abbrev STDimension := 4

-- Spacetime as 4-dimensional Euclidean space
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)

-- The free propagator in momentum space
noncomputable def freePropagatorMomentum (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / (‖k‖^2 + m^2)

/-- The free propagator is an even function: it depends only on ‖k‖. -/
lemma freePropagator_even (m : ℝ) (k : SpaceTime) :
    freePropagatorMomentum m (-k) = freePropagatorMomentum m k := by
  unfold freePropagatorMomentum
  simp only [norm_neg]

/-- The free propagator function is smooth (infinitely differentiable). -/
lemma freePropagator_smooth (m : ℝ) [Fact (0 < m)] :
  ContDiff ℝ (⊤ : ℕ∞) (fun k => freePropagatorMomentum m k) := by
  -- The function k ↦ 1/(‖k‖² + m²) is smooth as a composition of smooth functions
  unfold freePropagatorMomentum
  apply ContDiff.div
  · -- The numerator 1 is smooth (constant)
    exact contDiff_const
  · -- The denominator ‖k‖² + m² is smooth
    apply ContDiff.add
    · exact contDiff_norm_sq ℝ
    · exact contDiff_const
  · -- The denominator is never zero
    intro k
    apply ne_of_gt
    apply add_pos_of_nonneg_of_pos
    · exact sq_nonneg ‖k‖
    · exact pow_pos (Fact.out : 0 < m) 2

/-- The complex-valued free propagator function is smooth. -/
lemma freePropagator_complex_smooth (m : ℝ) [Fact (0 < m)] :
  ContDiff ℝ (⊤ : ℕ∞) (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) := by
  have : (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) =
         (fun x : ℝ => (x : ℂ)) ∘ (fun k => freePropagatorMomentum m k) := rfl
  rw [this]
  apply ContDiff.comp
  · exact ofRealCLM.contDiff
  · exact freePropagator_smooth m

/-- The propagator multiplier has temperate growth as a scalar function.
    This follows from the fact that it's bounded and smooth. -/
theorem freePropagator_temperate_growth (m : ℝ) [Fact (0 < m)] :
  Function.HasTemperateGrowth (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) := by
  constructor
  · -- Smoothness follows from our helper lemma
    exact freePropagator_complex_smooth m
  · -- Polynomial bounds on derivatives
    intro n
    use 0, 1 / m^2  -- Use polynomial degree 0 (constant bound)
    intro k
    -- All derivatives are bounded by the same constant since the function is bounded
    have hbound : ‖(freePropagatorMomentum m k : ℂ)‖ ≤ 1 / m^2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      unfold freePropagatorMomentum
      rw [abs_div, abs_of_pos]
      · rw [abs_of_pos]
        · apply div_le_div_of_nonneg_left
          · norm_num
          · exact pow_pos (Fact.out : 0 < m) 2
          · apply le_add_of_nonneg_left
            exact sq_nonneg ‖k‖
        · apply add_pos_of_nonneg_of_pos
          · exact sq_nonneg ‖k‖
          · exact pow_pos (Fact.out : 0 < m) 2
      · norm_num
    -- For n = 0 (the function itself)
    cases n with
    | zero =>
      simp only [pow_zero, mul_one]
      rw [norm_iteratedFDeriv_zero]
      exact hbound
    | succ n' =>
      -- For higher derivatives, we use that the function and all its derivatives are bounded
      sorry -- This requires more detailed analysis of the derivatives of 1/(‖k‖² + m²)
