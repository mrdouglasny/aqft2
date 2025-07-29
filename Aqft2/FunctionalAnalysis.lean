
/-© 2025 Math definitions which arguably should be in mathlib
 -/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace

import Mathlib.Topology.Algebra.Module.LinearMapPiProd

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.NormedSpace.Real

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section

/- Multiplication of Schwarz functions
 -/

open scoped SchwartzMap

variable {𝕜 : Type} [RCLike 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma SchwartzMap.hasTemperateGrowth
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : 𝓢(E, V)) :
    Function.HasTemperateGrowth (⇑g) := by
  refine ⟨g.smooth', ?_⟩
  intro n
  -- take k = 0 in the decay estimate
  rcases g.decay' 0 n with ⟨C, hC⟩
  refine ⟨0, C, ?_⟩
  intro x
  have : ‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    simpa using hC x
  simpa using this
