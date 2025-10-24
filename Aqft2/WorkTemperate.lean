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

/-- Bounding the iterated Fréchet derivatives of the complex-valued propagator.

    This lemma states that for each derivative order n, there exists a uniform bound.
    The bounds can (and do) depend on n, but each individual derivative is uniformly bounded.

    Mathematical insight: The function f(k) = 1/(‖k‖² + m²) and all its derivatives
    are actually bounded by constants (not just polynomially bounded). Each derivative
    has the form P(k)/(‖k‖² + m²)^(j+1) where P is a polynomial of degree ≤ 2j,
    so the denominator dominates and the function remains bounded.

    This is stronger than needed for temperate growth (which only requires polynomial bounds),
    but it's the natural property of this function. -/
lemma freePropagator_iteratedFDeriv_bound (m : ℝ) [Fact (0 < m)] (n : ℕ) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : SpaceTime,
    ‖iteratedFDeriv ℝ n (fun k => (freePropagatorMomentum m k : ℂ)) k‖ ≤ C := by
  classical
  refine Nat.recOn n ?base ?step
  · -- Base case: n = 0, the function itself
    refine ⟨1 / m^2, by positivity, ?_⟩
    intro k
    have hpos : 0 < m := Fact.out
    have hbound : ‖(freePropagatorMomentum m k : ℂ)‖ ≤ 1 / m^2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      unfold freePropagatorMomentum
      have hden_pos : 0 < ‖k‖ ^ 2 + m ^ 2 :=
        add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (pow_pos hpos 2)
      have hden_ge : m ^ 2 ≤ ‖k‖ ^ 2 + m ^ 2 :=
        le_add_of_nonneg_left (sq_nonneg ‖k‖)
      have hineq : 1 / (‖k‖ ^ 2 + m ^ 2) ≤ 1 / m ^ 2 := by
        exact one_div_le_one_div_of_le (pow_pos hpos 2) hden_ge
      have : |1 / (‖k‖ ^ 2 + m ^ 2)| = 1 / (‖k‖ ^ 2 + m ^ 2) :=
        abs_of_nonneg (le_of_lt (div_pos one_pos hden_pos))
      rw [this]
      exact hineq
    simpa [norm_iteratedFDeriv_zero] using hbound
  · intro n hn
    obtain ⟨C, hC₀, hC⟩ := hn
    -- Inductive step: the (n+1)-th derivative
    --
    -- MATHEMATICAL FACT: All derivatives of f(k) = 1/(‖k‖² + m²) are uniformly bounded.
    -- This follows from the general principle that derivatives of rational functions
    -- with polynomial numerators and denominators of higher degree are bounded.
    --
    -- RIGOROUS PROOF STRATEGY (not implemented here):
    -- 1. Show that D^n[1/(‖k‖² + m²)] = P_n(k)/(‖k‖² + m²)^(n+1)
    --    where P_n is a polynomial of degree ≤ 2n
    -- 2. Show that ‖P_n(k)‖ ≤ C_n * (‖k‖² + m²)^n for some constant C_n
    -- 3. Therefore ‖D^n f(k)‖ ≤ C_n/(‖k‖² + m²) ≤ C_n/m²
    --
    -- The bound C_n can be computed explicitly using Faà di Bruno's formula,
    -- or by induction on the derivative structure.
    --
    -- For this proof, we use a generous bound that grows with n
    have hpos : 0 < m := Fact.out
    refine ⟨(n + 2) ^ 4 / m ^ 2, by positivity, ?_⟩
    intro k
    -- TODO: Complete this using either:
    -- (a) Explicit formulas for derivatives of 1/(‖k‖² + m²)
    -- (b) Mathlib lemmas about derivatives of rational functions
    -- (c) The fact that this function is in the Schwartz space
    sorry

/-- Helper lemma: all iterated Fréchet derivatives of `k ↦ (1 + ‖k‖²)⁻¹` are uniformly bounded. -/
lemma iteratedFDeriv_inv_one_add_norm_sq_bounded (n : ℕ) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : SpaceTime,
    ‖iteratedFDeriv ℝ n (fun k => (1 + ‖k‖^2)⁻¹ : SpaceTime → ℝ) k‖ ≤ C := by
  sorry

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
      -- For higher derivatives, we use that all derivatives of 1/(‖k‖² + m²) are bounded
      -- This follows from the fact that each derivative introduces polynomial numerators
      -- but the denominator (‖k‖² + m²) grows quadratically, making derivatives decay faster
      -- For now, we use a generous polynomial bound that works for all derivatives
      simp only [pow_zero, mul_one]
      -- We claim all derivatives are bounded by a constant depending on n and m
      -- The detailed proof requires explicit computation of derivative bounds
      sorry

/-- Alternate proof skeleton for `freePropagator_temperate_growth`. -/
theorem freePropagator_temperate_growth' (m : ℝ) [Fact (0 < m)] :
  Function.HasTemperateGrowth (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) := by
  classical
  constructor
  · exact freePropagator_complex_smooth m
  · intro n
    obtain ⟨C, hC₀, hC⟩ := freePropagator_iteratedFDeriv_bound (m := m) n
    refine ⟨0, C, ?_⟩
    intro k
    simpa using hC k
