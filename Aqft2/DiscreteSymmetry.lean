
import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.MetricSpace.Isometry

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real

--import Mathlib.LinearAlgebra.TensorAlgebra.Basic

import Aqft2.Basic
import Aqft2.EuclideanS

namespace QFT

abbrev timeReflection (x : SpaceTime) : SpaceTime :=
  Function.update x 0 (-x 0)

def timeReflectionMatrix : Matrix (Fin STDimension) (Fin STDimension) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

lemma timeReflectionMatrix_is_orthogonal :
   timeReflectionMatrix ∈ Matrix.orthogonalGroup (Fin STDimension) ℝ := by
      simp [Matrix.mem_orthogonalGroup_iff, timeReflectionMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      simp [Matrix.diagonal]
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> norm_num

def timeReflectionIsometry  : Matrix.orthogonalGroup (Fin STDimension) ℝ :=
  ⟨timeReflectionMatrix, timeReflectionMatrix_is_orthogonal⟩

#check timeReflectionIsometry.val.toLin'

def timeReflectionLinear' : SpaceTime →ₗ[ℝ] SpaceTime :=  timeReflectionIsometry.val.toLin'

#check LinearIsometry (RingHom.id ℝ) SpaceTime SpaceTime

--def timeReflectionIsometry_act (x : SpaceTime) : SpaceTime := timeReflectionIsometry.1 (Fin STDimension) x

def timeReflectionLinear : SpaceTime →ₗ[ℝ] SpaceTime :=
{ toFun := timeReflection
  map_add' := by
    intro x y; funext i
    -- Split on whether `i = 0`
    by_cases h : (i : Fin STDimension) = 0
    · subst h
      simp
      ring
    · simp [h],
  map_smul' := by
    intro c x; funext i
    by_cases h : (i : Fin STDimension) = 0
    <;> simp [Function.update, h] }

def timeReflectionCLM : SpaceTime →L[ℝ] SpaceTime :=
timeReflectionLinear.toContinuousLinearMap (E := SpaceTime) (F' := SpaceTime)

open InnerProductSpace

/-- Time reflection preserves inner products -/
lemma timeReflection_inner_map (x y : SpaceTime) :
    ⟪timeReflection x, timeReflection y⟫_ℝ = ⟪x, y⟫_ℝ := by
  -- Direct proof using fintype inner product
  simp only [inner]
  congr 1
  ext i
  simp only [timeReflection, Function.update]
  by_cases h : i = 0
  · rw [h]; simp
  · simp [h]

/-- Time reflection as a linear isometry equivalence -/
def timeReflectionLE : SpaceTime ≃ₗᵢ[ℝ] SpaceTime :=
{ toFun := timeReflection
  invFun := timeReflection  -- Time reflection is self-inverse
  left_inv := by
    intro x
    ext i
    by_cases h : i = 0
    · simp [timeReflection, Function.update]
      subst h
      simp
    · simp [timeReflection, Function.update, h]
  right_inv := by
    intro x
    ext i
    by_cases h : i = 0
    · simp [timeReflection, Function.update]
      subst h
      simp
    · simp [timeReflection, Function.update, h]
  map_add' := timeReflectionLinear.map_add'
  map_smul' := timeReflectionLinear.map_smul'
  norm_map' := by
    intro x
    -- The goal is to show that the LinearIsometryEquiv preserves norms
    -- First simplify the LinearIsometryEquiv application
    show ‖timeReflection x‖ = ‖x‖
    -- Use that time reflection preserves inner products
    have h : ⟪timeReflection x, timeReflection x⟫_ℝ = ⟪x, x⟫_ℝ := timeReflection_inner_map x x
    -- For real inner product spaces, ⟪x, x⟫ = ‖x‖^2 directly
    have h1 : ⟪timeReflection x, timeReflection x⟫_ℝ = ‖timeReflection x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
    have h2 : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [← h1, ← h2, h] }

example (x : SpaceTime) :
    timeReflectionCLM x =
      Function.update x (0 : Fin STDimension) (-x 0) := rfl
