/-
Copyright (c) 2025. All rights reserved.
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

open MeasureTheory Real
open TopologicalSpace

noncomputable section

/-! ## Multiplication Operators on L² Spaces

This file provides a general framework for multiplication operators on L² spaces over arbitrary
measure spaces. The key results are:

1. **Bounded continuous functions** give bounded multiplication operators
2. **L∞ functions** give bounded multiplication operators

These lemmas can then be applied to specific spaces in QFT and other applications.
-/

-- General measure space setup
variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
variable (μ : Measure α) [SigmaFinite μ]

/-! ## Core Lemmas

The fundamental results showing that pointwise multiplication gives bounded operators.
-/

/-- **Lemma 1**: Bounded continuous functions give bounded multiplication operators.

If ϕ is a bounded continuous function on α, then pointwise multiplication by ϕ
defines a bounded linear operator on L²(α, μ) with ‖T_ϕ‖ ≤ ‖ϕ‖∞. -/
lemma mulL2_of_boundedContinuous (ϕ : BoundedContinuousFunction α ℝ) :
  ∃ (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), (∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun x => ϕ x • f x) ∧ ‖T‖ ≤ ‖ϕ‖ := by
  -- The key idea: bounded continuous functions are essentially bounded
  -- Step 1: Convert to an essentially bounded function
  let φae : α →ᵃ[μ] ℝ := ϕ.toAEEqFun μ
  -- Step 2: Use the L² multiplication operator
  use L2.mul φae
  constructor
  · intro f
    -- Convert multiplication to scalar multiplication
    have : (fun x => ϕ x * f x) = (fun x => ϕ x • f x) := by
      ext x
      exact smul_eq_mul (ϕ x) (f x)
    rw [← this]
    -- Use the L² multiplication formula
    simpa [mul_comm] using (L2.mul_apply φae f)
  · -- Norm bound follows from the L² operator norm
    simpa using (L2.opNorm_mul_le φae)

/-- **Lemma 2**: L∞ functions give bounded multiplication operators.

If ϕ ∈ L∞(α, μ), then pointwise multiplication by ϕ defines a bounded linear operator
on L²(α, μ) with ‖T_ϕ‖ ≤ ‖ϕ‖∞. -/
lemma mulL2_of_Linfty (ϕ : Lp ℝ ⊤ μ) :
  ∃ (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), (∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun x => ϕ x • f x) ∧ ‖T‖ ≤ ‖ϕ‖ := by
  -- L∞ functions are already essentially bounded
  let φae := Lp.toAEEqFun ϕ
  use L2.mul φae
  constructor
  · intro f
    -- Convert multiplication to scalar multiplication
    have : (fun x => ϕ x * f x) = (fun x => ϕ x • f x) := by
      ext x
      exact smul_eq_mul (ϕ x) (f x)
    rw [← this]
    simpa [mul_comm] using (L2.mul_apply φae f)
  · simpa using (L2.opNorm_mul_le φae)

/-! ## Constructors for Multiplication Operators

Based on the core lemmas, we can construct multiplication operators.
-/

/-- Multiplication operator from a bounded continuous function. -/
noncomputable def mulL2_BoundedContinuous (ϕ : BoundedContinuousFunction α ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Classical.choose (mulL2_of_boundedContinuous μ ϕ)

/-- Multiplication operator from an L∞ function. -/
noncomputable def mulL2_Linfty (ϕ : Lp ℝ ⊤ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Classical.choose (mulL2_of_Linfty μ ϕ)

/-- The norm bound for bounded continuous function multiplication. -/
lemma mulL2_BoundedContinuous_norm_le (ϕ : BoundedContinuousFunction α ℝ) :
    ‖mulL2_BoundedContinuous μ ϕ‖ ≤ ‖ϕ‖ :=
  (Classical.choose_spec (mulL2_of_boundedContinuous μ ϕ)).2

/-- The norm bound for L∞ function multiplication. -/
lemma mulL2_Linfty_norm_le (ϕ : Lp ℝ ⊤ μ) :
    ‖mulL2_Linfty μ ϕ‖ ≤ ‖ϕ‖ :=
  (Classical.choose_spec (mulL2_of_Linfty μ ϕ)).2

/-- The multiplication property for bounded continuous functions. -/
lemma mulL2_BoundedContinuous_apply (ϕ : BoundedContinuousFunction α ℝ) (f : Lp ℝ 2 μ) :
    (mulL2_BoundedContinuous μ ϕ) f =ᵐ[μ] fun x => ϕ x • f x :=
  (Classical.choose_spec (mulL2_of_boundedContinuous μ ϕ)).1 f

/-- The multiplication property for L∞ functions. -/
lemma mulL2_Linfty_apply (ϕ : Lp ℝ ⊤ μ) (f : Lp ℝ 2 μ) :
    (mulL2_Linfty μ ϕ) f =ᵐ[μ] fun x => ϕ x • f x :=
  (Classical.choose_spec (mulL2_of_Linfty μ ϕ)).1 f

/-! ## Basic Properties

These properties hold for all multiplication operators constructed using our framework.
-/

/-- **Linearity**: All multiplication operators are linear. -/
example (ϕ : BoundedContinuousFunction α ℝ) (f g : Lp ℝ 2 μ) (c : ℝ) :
    mulL2_BoundedContinuous μ ϕ (c • f + g) = c • mulL2_BoundedContinuous μ ϕ f + mulL2_BoundedContinuous μ ϕ g :=
  (mulL2_BoundedContinuous μ ϕ).map_add_smul c f g

/-! ## Examples

Concrete examples showing how to construct multiplication operators from common functions.
-/

-- For examples, we work with ℝ and Lebesgue measure
variable [MeasurableSpace ℝ] [BorelSpace ℝ]
variable (μ_ex : Measure ℝ) [SigmaFinite μ_ex]

/-- The constant function as a bounded continuous function. -/
def constantFunction (c : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.const ℝ c

/-- Multiplication by a constant. -/
def constantMultiplication (c : ℝ) : Lp ℝ 2 μ_ex →L[ℝ] Lp ℝ 2 μ_ex :=
  mulL2_BoundedContinuous μ_ex (constantFunction c)

/-- The sine function as a bounded continuous function. -/
def sineBoundedFunction : BoundedContinuousFunction ℝ ℝ := by
  refine ⟨⟨sin, continuous_sin⟩, 1, ?_⟩
  intro x
  simp [Real.norm_sin_le_one]

/-- Multiplication by sine. -/
def sineBoundedMultiplication : Lp ℝ 2 μ_ex →L[ℝ] Lp ℝ 2 μ_ex :=
  mulL2_BoundedContinuous μ_ex sineBoundedFunction

end
