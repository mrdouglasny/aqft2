
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
--import Mathlib.Geometry.Manifold.Algebra.GroupAction

import Aqft2.Basic

open Manifold

noncomputable section

universe u

/- A spacetime as a structure -/

class SpaceTime
    {E H M G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M]  [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ E M)
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [IsManifold I ⊤ G]
    [IsManifold J ⊤ M]
    [MulAction G M] where

  dimension : ℕ
  symmetry_is_lie_group : LieGroup I ⊤ G
  smooth_action : ContDiff (I.prod J) J ⊤ (λ p : G × M => p.1 • p.2)

-- Instance for G = ℝ, M = ℝ with translation action
noncomputable instance realTranslationSpacetime :
    SpaceTime (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (M := ℝ) (G := ℝ) :=
  {
    dimension := 1
    symmetry_is_lie_group := inferInstance
    smooth_action := contDiff_id.add contDiff_snd
  }



structure QuantumFieldTheory (ST: SpaceTime) where
  FieldValue : ℝ
  FieldSpace : Lp (p := 2) (μ := μ) ℝ
