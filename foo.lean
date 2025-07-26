import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic

-- We define STDimension as a concrete number.
def STDimension : Nat := 4

-- Because STDimension is a `def`, its value is known.
-- We do not need a `[Fact]` assumption.
abbrev SpaceTime := EuclideanSpace ℝ (Fin 4)

/-- A function that returns the time-component (index 0) of a spacetime vector. -/
def getTimeComponent (x : SpaceTime) : ℝ :=
  -- We use the `norm_num` tactic, which is specialized for this kind of proof.
  -- It will evaluate `STDimension` to `4` and solve the goal `0 < 4`.
  x ⟨0, by norm_num⟩

-- Let's define an example vector to test the function.
--def myVector : SpaceTime := fun i => (i : Nat) + 10

-- This line will only compile if `getTimeComponent` is valid.
-- It should evaluate to `10`.
--#eval getTimeComponent myVector
