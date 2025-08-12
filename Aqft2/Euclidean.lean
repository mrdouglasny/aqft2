/-© 2025 SYH - OS-2 (Euclidean invariance)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Topology.MetricSpace.Isometry

import Aqft2.Basic

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section

/-OS2 R^d with d=4, where mu is the Lebegue measure.
We know the OS2 dp must be Euclidean invariant -/

open scoped Real InnerProductSpace SchwartzMap

namespace QFT

/-- Orthogonal linear isometries of ℝ⁴ (the group O(4)).
LinearIsometry is an orthogonal linear map, ie an element of O(4)-/
abbrev O4 : Type :=
  LinearIsometry (RingHom.id ℝ) SpaceTime SpaceTime

/-!  Euclidean group -/
/-- Euclidean motion = rotation / reflection + translation. E= R^4 x O(4)-/
structure E where
  R : O4
  t : SpaceTime

/-- Action of g : E on a spacetime point x.
Impliments the pullback map x to Rx+ t -/
def act (g : E) (x : SpaceTime) : SpaceTime := g.R x + g.t

/-act_one, act_mul and act_inv lemmas prove
identity, composition and inverse. They are needed to say Euclidean sym
form a group. This mirrors OS-2's S_j= S_{EJ} -/
@[simp] lemma act_one   (x : SpaceTime) : act ⟨1,0⟩ x = x := by
  simp [act]

@[simp] lemma act_mul   (g h : E) (x : SpaceTime) :
    act ⟨g.R.comp h.R, g.R h.t + g.t⟩ x = g.R (h.R x + h.t) + g.t := by
  simp [act, add_comm, add_left_comm]

@[simp] lemma act_inv (g : E) (x : SpaceTime) :
    act ⟨g.R, -g.R g.t⟩ x = g.R (x - g.t) := by
  -- unfold the two sides and use linearity of g.R
  simp [act, sub_eq_add_neg, map_add, map_neg]
        -- the map_sub lemma is in mathlib
/- Linear-iso helper lemmas are explicitly in Os-2
but are used as a counter part to rotations that preserve the metric and R^-1 R=1-/
open LinearIsometryEquiv

namespace LinearIsometry
/-- Inverse of a linear isometry : we turn the canonical equivalence
    (available in finite dimension) back into a `LinearIsometry`. -/
noncomputable def inv (g : O4) : O4 :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry

@[simp] lemma comp_apply (g h : O4) (x : SpaceTime) :
    (g.comp h) x = g (h x) := rfl

@[simp] lemma inv_apply (g : O4) (x : SpaceTime) :
    (LinearIsometry.inv g) (g x) = x := by
  -- unfold `inv`, then use the standard `symm_apply_apply` lemma
  dsimp [LinearIsometry.inv]
  simpa using
    (LinearIsometryEquiv.symm_apply_apply (g.toLinearIsometryEquiv rfl) x)
@[simp] lemma one_apply (x : SpaceTime) : (1 : O4) x = x := rfl

@[simp] lemma one_comp (R : O4) : (1 : O4).comp R = R := by
  ext x; simp [comp_apply, one_apply]

@[simp] lemma comp_one (R : O4) : R.comp (1 : O4) = R := by
  ext x; simp [comp_apply, one_apply]

@[simp] lemma inv_comp (R : O4) :
    (LinearIsometry.inv R).comp R = 1 := by
  ext x i
  simp [comp_apply, inv_apply, one_apply]
@[simp] lemma comp_inv (R : O4) :
    R.comp (LinearIsometry.inv R) = 1 := by
  -- equality of linear-isometries, proved coordinate-wise
  ext x i
  have h : (R.toLinearIsometryEquiv rfl) ((LinearIsometry.inv R) x) = x :=
    LinearIsometryEquiv.apply_symm_apply (R.toLinearIsometryEquiv rfl) x
  simpa [comp_apply, inv_apply, one_apply] using congrArg (fun v : SpaceTime => v i) h

end LinearIsometry

/-(extentionality) Allows Lean to prove equality of Euclidean motions by checking the R and t
components separately—hugely convenient for the group-law proofs. -/
@[ext] lemma E.ext {g h : E} (hR : g.R = h.R) (ht : g.t = h.t) : g = h := by
  cases g; cases h; cases hR; cases ht; rfl

/-!  ##  Group structure on `E`  ----------------------------------------- -/

/- 1.  Primitive instances of group operations
Implements the semidirect-product multiplication in OS-2:
first rotate, then translate the second translation by the first rotation. -/
instance : Mul E where
  mul g h := ⟨g.R.comp h.R, g.R h.t + g.t⟩

instance : One E where
  one := ⟨1, 0⟩

instance : Inv E where
  inv g := ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩

/-- We need a `Div` instance because `Group` extends `DivInvMonoid`. -/
instance : Div E where
  div g h := g * h⁻¹

/- helper lemmas mirroring (g. h)_R= g_R dot h_r, and
(g.h)_t= g_R h_t+ g_t)-
-/
@[simp] lemma mul_R (g h : E) : (g * h).R = g.R.comp h.R := rfl
@[simp] lemma mul_t (g h : E) : (g * h).t = g.R h.t + g.t := rfl
@[simp] lemma one_R : (1 : E).R = 1 := rfl
@[simp] lemma one_t : (1 : E).t = 0 := rfl
@[simp] lemma inv_R (g : E) : (g⁻¹).R = LinearIsometry.inv g.R := rfl
@[simp] lemma inv_t (g : E) : (g⁻¹).t = -(LinearIsometry.inv g.R) g.t := rfl

/-- LinearIsometry.comp is associative.
OS-2’s “group” assertion needs rotation composition to be associative; this
lemma certifies it for Lean.
-/
@[simp] lemma LinearIsometry.comp_assoc (f g h : O4) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext x; rfl

/-Provides the formal group demanded by OS-2’s statement
“Euclidean transformations define a group.”-/
instance : Group E where
  mul := (· * ·)
  one := (1 : E)
  inv := Inv.inv

  -- associativity
  mul_assoc a b c := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_assoc]
    · simp [mul_t, add_comm, add_left_comm]

  -- left and right identity
  one_mul a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.one_comp]
    · simp [mul_t, one_t]

  mul_one a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_one]
    · simp [mul_t, one_t]
  inv_mul_cancel a := by
    -- prove  a⁻¹ * a = 1
    apply E.ext
    · simp [mul_R, inv_R, one_R, LinearIsometry.inv_comp]
    · simp [mul_t, inv_t, one_t]

/-theorem ---------------------------------------------

     For all Euclidean motions g,h and every point x ∈ ℝ⁴ we have
         act (g * h) x  =  act g (act h x).
     In words: the `act` map is a group action of E on spacetime.

     We also prove the inverse law
         act g⁻¹ (act g x) = x.
-/

/-for all Euclidean motions g and h and any point x ∈ ℝ⁴, pulling x forward by the product g*h equals pulling by h first and then by g.
This is precisely the group-action law(𝑔ℎ)⁣⋅𝑥=𝑔.(ℎ. 𝑥)(gh)⋅x=g⋅(h⋅x).-/

@[simp] lemma act_mul_general (g h : E) (x : SpaceTime) :
    act (g * h) x = act g (act h x) := by
  -- destructure g and h so Lean can see their components
/-cases on g/h: expands each motion into its components
gR : O4 the rotation, gt : ℝ⁴ the translation.
hR, ht likewise. That lets Lean see the literal structure of g*h.-/
  cases g with
  | mk gR gt =>
    cases h with
    | mk hR ht =>
      -- unfold everything; `mul_R`, `mul_t` give the components of g*h
      /-simp does it all:

act unfolds to R x + t.

mul_R, mul_t give formulas for the rotation/translation of g*h.

A handful of commutativity/associativity lemmas reorganise 𝑔𝑅(ℎ𝑅𝑥+ℎ𝑡)+𝑔𝑡gR(hRx+ht)+g
t into the desired form.
→ Goal reduces to reflexive equality, proof finished.-/
      simp [act, mul_R, mul_t, add_comm, add_left_comm]

/-Statement: applying g to x and then applying the inverse motion g⁻¹ returns you to x.
This is the inverse law of a group action.-/
/-Result: we’ve established that act : E → (ℝ⁴ → ℝ⁴) is a homomorphism into the function-composition monoid—exactly what OS-2 needs for its pull-back action on fields.-/

@[simp] lemma act_inv_general (g : E) (x : SpaceTime) :
    act g⁻¹ (act g x) = x := by
  cases g with
  | mk gR gt =>
      -- unfold act, inverse components, then use linearity of gR
      simp [act, inv_R, inv_t, add_comm, add_assoc]
/-Result: confirms that act really is a faithful left action of the Euclidean group; no hidden sign or composition mistakes remain.-/


/-! ### Lebesgue measure is invariant under every Euclidean motion --------- -/

open MeasureTheory
/-- For every rigid motion `g : E`, the push‑forward of Lebesgue measure `μ`
    by the map `x ↦ g • x` is again `μ`.  Equivalently, `act g` is
    measure‑preserving. -/
lemma measurePreserving_act (g : E) :
    MeasurePreserving (fun x : SpaceTime => act g x) μ μ := by
  have rot : MeasurePreserving (fun x : SpaceTime => g.R x) μ μ := by
    simpa using (g.R.toLinearIsometryEquiv rfl).measurePreserving
  have trans : MeasurePreserving (fun x : SpaceTime => x + g.t) μ μ := by
    refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
    simpa using map_add_right_eq_self μ g.t
  simpa [act, Function.comp] using trans.comp rot

/-! ### Unified Action of Euclidean group on function spaces --------- 
    
    UNIFIED EUCLIDEAN ACTION FRAMEWORK
    
    This section demonstrates how the same geometric transformation (euclidean_pullback)
    can be used to define Euclidean actions on both test functions and L² functions:

    1. **Common foundation**: All actions are based on the pullback map x ↦ g⁻¹ • x
    2. **Key enabling result**: measurePreserving_act proves this map preserves Lebesgue measure
    3. **Dual routes**:
       - Test functions: Use temperate growth + Schwartz space structure
       - L² functions: Use measure preservation + Lp space structure
    4. **Unified interface**: Both yield continuous linear maps with the same group action laws

    This approach eliminates code duplication and ensures consistency between 
    the test function and L² formulations of the Osterwalder-Schrader axioms.
-/

/-- The fundamental pullback map for Euclidean actions.
    This is the geometric transformation x ↦ g⁻¹ • x that underlies
    all Euclidean actions on function spaces. -/
noncomputable def euclidean_pullback (g : E) : SpaceTime → SpaceTime := act g⁻¹

/-- The Euclidean pullback map has temperate growth (needed for Schwartz space actions). -/
lemma euclidean_pullback_temperate_growth (g : E) :
    Function.HasTemperateGrowth (euclidean_pullback g) := by
  -- The map x ↦ g⁻¹.R x + g⁻¹.t is affine (linear isometry + translation)
  -- Affine maps automatically have temperate growth
  sorry

/-- The Euclidean pullback map satisfies polynomial growth bounds. -/
lemma euclidean_pullback_polynomial_bounds (g : E) :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime), ‖x‖ ≤ C * (1 + ‖euclidean_pullback g x‖) ^ k := by
  -- Since euclidean_pullback g x = g⁻¹.R x + g⁻¹.t and g⁻¹.R is an isometry:
  -- ‖euclidean_pullback g x‖ = ‖g⁻¹.R x + g⁻¹.t‖ ≥ ‖g⁻¹.R x‖ - ‖g⁻¹.t‖ = ‖x‖ - ‖g⁻¹.t‖
  -- So ‖x‖ ≤ ‖euclidean_pullback g x‖ + ‖g⁻¹.t‖ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖euclidean_pullback g x‖)
  use 1; use (1 + ‖g⁻¹.t‖); intro x
  unfold euclidean_pullback act
  -- Use triangle inequality and isometry property
  sorry

/-- Action of Euclidean group on test functions via pullback.
    For g ∈ E and f ∈ TestFunctionℂ, define (g • f)(x) = f(g⁻¹ • x).
    This is the standard pullback action: to evaluate the transformed function
    at x, we evaluate the original function at the inverse-transformed point. -/
noncomputable def euclidean_action (g : E) (f : TestFunctionℂ) : TestFunctionℂ :=
  SchwartzMap.compCLM (𝕜 := ℂ) 
    (hg := euclidean_pullback_temperate_growth g) 
    (hg_upper := euclidean_pullback_polynomial_bounds g) f

/-- Action of Euclidean group on L² functions via pullback.
    For g ∈ E and f ∈ Lp ℂ 2 μ, define (g • f)(x) = f(g⁻¹ • x).
    This uses the same fundamental pullback transformation as the test function action,
    but leverages measure preservation instead of temperate growth bounds. -/
noncomputable def euclidean_action_L2 (g : E) {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  -- Use the continuous composition with measure-preserving map
  -- This is enabled by measurePreserving_act
  sorry  -- Implementation follows from measure preservation

/-- The measure preservation result enables both test function and L² actions.
    This is the key unifying lemma that works specifically for the spacetime measure μ. -/
lemma euclidean_action_unified_basis (g : E) :
    MeasurePreserving (euclidean_pullback g) (μ : Measure SpaceTime) μ := by
  -- This is just measurePreserving_act applied to g⁻¹
  unfold euclidean_pullback
  exact measurePreserving_act g⁻¹

/-- The Euclidean action as a continuous linear map on test functions.
    This leverages the Schwartz space structure and temperate growth bounds. -/
noncomputable def euclidean_action_CLM (g : E) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  SchwartzMap.compCLM (𝕜 := ℂ) 
    (hg := euclidean_pullback_temperate_growth g) 
    (hg_upper := euclidean_pullback_polynomial_bounds g)

/-- The Euclidean action as a continuous linear map on L² functions.
    This leverages measure preservation rather than temperate growth. -/
noncomputable def euclidean_action_L2_CLM (g : E) :
    Lp ℂ 2 (μ : Measure SpaceTime) →L[ℂ] Lp ℂ 2 μ := by
  -- Use continuous composition with the measure-preserving map
  -- The key insight: measurePreserving_act gives us the continuous linear map structure
  have h_meas_pres : MeasurePreserving (euclidean_pullback g) μ μ := 
    euclidean_action_unified_basis g
  -- Now we can use Mathlib's infrastructure for measure-preserving compositions on Lp spaces
  sorry  -- This follows from measure preservation and Lp space theory

/-- Both actions are instances of the same abstract pattern. -/
lemma euclidean_actions_unified (g : E) : 
    (∃ (T_test : TestFunctionℂ →L[ℂ] TestFunctionℂ), 
       ∀ f, euclidean_action g f = T_test f) ∧
    (∃ (T_L2 : Lp ℂ 2 (μ : Measure SpaceTime) →L[ℂ] Lp ℂ 2 μ), 
       ∀ f, euclidean_action_L2 g f = T_L2 f) := by
  constructor
  · use euclidean_action_CLM g
    intro f
    rfl  -- by definition of euclidean_action
  · use euclidean_action_L2_CLM g
    intro f
    sorry  -- follows from the definitions

/-- The Euclidean action is invertible as a continuous linear map.
    This expresses that Euclidean transformations act as invertible transformations
    on the space of test functions. -/
lemma euclidean_action_isInvertible (g : E) :
    ∃ (h : TestFunctionℂ →L[ℂ] TestFunctionℂ),
      (euclidean_action_CLM g).comp h = ContinuousLinearMap.id ℂ TestFunctionℂ ∧
      h.comp (euclidean_action_CLM g) = ContinuousLinearMap.id ℂ TestFunctionℂ := by
  -- The invertibility follows from:
  -- - The Euclidean group structure: g has an inverse g⁻¹
  -- - euclidean_action_CLM g⁻¹ should be the inverse of euclidean_action_CLM g
  -- - This reflects the group action property on test functions
  sorry
