/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.NormedSpace.Extend

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.SemidirectProduct

abbrev STDimension := 4
abbrev STvector : Type := (Fin STDimension) → ℝ
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev getTimeComponent (x : SpaceTime) : ℝ :=
 x ⟨0, by simp +arith⟩

/- Symmetries of spacetime
   These include translation, rotation, discrete symmetries
   All should be combined into a single group (to do).
 -/

open Matrix

variable (n : ℕ)
variable (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))

#check specialOrthogonalGroup
#check A
#check (↑(A⁻¹ * A)) *ᵥ x = x

example : (↑(A⁻¹ * A)) *ᵥ x = x := by
  rw [Subtype.val]
  have h : A⁻¹ * A = 1 := inv_mul_self A
  -- Now rewrite the goal using this fact.
  rw [h]
  rw [one_mul_vec]

abbrev STTranslationGroup := Multiplicative SpaceTime

-- The rotation group SO(n)
abbrev STRotationGroup := Matrix.specialOrthogonalGroup (Fin STDimension) ℝ

/-- The action of the rotation group on the translation group by automorphisms. -/
noncomputable def rotationAction : STRotationGroup →* (STTranslationGroup ≃* STTranslationGroup) where
  toFun A := {
    toFun    := fun v => Multiplicative.ofAdd (↑A *ᵥ Multiplicative.toAdd v)
    invFun   := fun v => Multiplicative.ofAdd (↑A⁻¹ *ᵥ Multiplicative.toAdd v)
    left_inv  := by
      intro x
      simp [Multiplicative.toAdd, Multiplicative.ofAdd]
      rw [congr_arg Subtype.val invOf_mul_self A]
    right_inv := by intro; simp
    map_mul'  := by intros; simp [Matrix.mul_vec_add]
  }
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [mul_assoc]


variable (M : STRotationGroup) (x : STTranslationGroup)
#check ⇑(x) + (M.1 *ᵥ ⇑(x))

/--
The Euclidean group E(n) as pairs of an orthogonal matrix `A` and a
translation vector `v`.
-/
structure EuclideanGroup where
  rot : STRotationGroup
  trans : STTranslationGroup

@[ext]
lemma EuclideanGroup.ext {g₁ g₂ : EuclideanGroup}
    (h_rot : g₁.rot = g₂.rot)
    (h_trans : g₁.trans = g₂.trans) : g₁ = g₂ := by
  cases g₁; cases g₂; simp_all

def EuclideanGroup.mul (g₁ g₂ : EuclideanGroup) : EuclideanGroup := {
  rot := ↑g₁.rot * ↑g₂.rot,
  trans := ⇑g₁.trans + ((g₁.rot.1) *ᵥ ⇑g₂.trans)
}

variable (g : EuclideanGroup)
#check g.rot.1
#check g.rot
#check (λ x ↦ Subtype.val x.rot) g

-- We now prove this structure forms a group.
noncomputable instance : Group EuclideanGroup where
  mul := EuclideanGroup.mul
  one := {
    rot := 1,
    trans := 0
  }
  -- The inverse of (A, v) is (A⁻¹, -A⁻¹v)
  inv g := {
    rot := g.rot⁻¹,
    trans := -(g.rot⁻¹ *ᵥ g.trans)
  }
  mul_assoc := by
    intros g₁ g₂ g₃
    ext
    dsimp [EuclideanGroup.mul]
    have h_assoc := mul_assoc g₁.rot g₂.rot g₃.rot
    have h_assoc_coe := congr_arg Subtype.val h_assoc
    rw [h_assoc_coe]
    simp [EuclideanGroup.mul, Subtype.coe_eta, mul_assoc]
    dsimp [EuclideanGroup.mul]
    simp [EuclideanGroup.mul, mul_assoc, Matrix.mulVec_add, add_assoc]
    simp [add_assoc, Matrix.mulVec_add]
    noncomm_ring
  one_mul := by
    intros g; ext; rw [one_mul]; simp [EuclideanGroup.mul]
  mul_one := by
    intros g; ext <;> simp
  inv_mul_cancel := by
    intros g; ext <;> simp [Matrix.mul_vec_add]
