/-
Tools for differentiating parameterized integrals that appear in the Gaussian
moments proofs.  The main lemma is a work-in-progress rewrite of the
`mixed_deriv_under_integral` argument from `GFFMComplex.lean`, now organized to
follow the dominated-convergence strategy outlined in `texts/mixed.txt`.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open scoped Topology
open MeasureTheory
open Filter

namespace Aqft2

variable {α : Type*} [MeasurableSpace α]

/-- Single derivative under the integral for exponential integrands.
This is the building block for mixed derivatives.  In addition to integrability,
we assume a uniform almost-everywhere bound `‖f ω‖ ≤ M` and restrict to a small
neighbourhood `|t| < ε`, which together provide the integrable majorant needed
for dominated convergence.  For `g(t, ω) = exp(I * t * f ω)` we obtain the
familiar identity `∂ₜ g |₀ = I * f ω`. -/
lemma deriv_under_integral_exp
    (μ : Measure α) [SigmaFinite μ]
  [IsFiniteMeasure μ]
    (f : α → ℂ)
  (hf_int : Integrable f μ)
  (M ε : ℝ)
  (hε_pos : 0 < ε)
  (hM_nonneg : 0 ≤ M)
  (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    HasDerivAt
      (fun t : ℂ ↦ ∫ ω, Complex.exp (Complex.I * t * f ω) ∂μ)
      (∫ ω, Complex.I * f ω * Complex.exp (Complex.I * 0 * f ω) ∂μ) 0 := by
  -- Simplify the goal first
  have h_goal_simp : (∫ ω, Complex.I * f ω * Complex.exp (Complex.I * 0 * f ω) ∂μ) =
      (∫ ω, Complex.I * f ω ∂μ) := by
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one]

  rw [h_goal_simp]

  -- Basic setup for the dominated-convergence argument
  classical

  -- Parameterized integrand and its formal derivative
  let F : ℂ → α → ℂ := fun t ω ↦ Complex.exp (Complex.I * t * f ω)
  let F' : ℂ → α → ℂ := fun t ω ↦ Complex.I * f ω * Complex.exp (Complex.I * t * f ω)

  -- Natural majorant controlling the derivative; domination will use the extra exponential factor
  let H : α → ℝ := fun ω ↦ ‖f ω‖
  let K : ℝ := Real.exp (2 * ε * M)

  -- Collect immediate measurability/integrability facts that will feed into later steps
  have hf_meas : AEStronglyMeasurable f μ := hf_int.aestronglyMeasurable
  obtain ⟨g, hg_sm, hfg⟩ := hf_meas
  have hH_int : Integrable H μ := hf_int.norm
  have hH_meas : AEStronglyMeasurable H μ := hH_int.aestronglyMeasurable

  -- Auxiliary estimate: the domination constant K is finite and nonnegative
  have hK_pos : 0 < K := by
    simpa [K] using Real.exp_pos (2 * ε * M)
  have hK_nonneg : 0 ≤ K := hK_pos.le

  -- KEY BOUND: ‖F' t ω‖ ≤ K · ‖f ω‖ for t in the ε-ball
  have h_bound : ∀ᵐ ω ∂μ, ∀ t : ℂ, ‖t‖ < ε → ‖F' t ω‖ ≤ K * H ω := by
    refine hf_bound.mono ?_
    intro ω hω_bound t ht_small
    have ht_le : ‖t‖ ≤ ε := le_of_lt ht_small
    have hf_le : ‖f ω‖ ≤ M := hω_bound

    have h_normF' : ‖F' t ω‖ = ‖f ω‖ * Real.exp (Complex.re (Complex.I * t * f ω)) := by
      simp [F', Complex.norm_exp, mul_comm, mul_left_comm]

    have h_re_le_two : Complex.re (Complex.I * t * f ω) ≤ 2 * ε * M := by
      have h_norm_prod : ‖Complex.I * t * f ω‖ = ‖t‖ * ‖f ω‖ := by
        simp [mul_comm, mul_left_comm]
      have h_re_le_norm : Complex.re (Complex.I * t * f ω) ≤ ‖t‖ * ‖f ω‖ := by
        have h₁ : Complex.re (Complex.I * t * f ω) ≤ |Complex.re (Complex.I * t * f ω)| :=
          le_abs_self _
        have h₂ : |Complex.re (Complex.I * t * f ω)| ≤ ‖t‖ * ‖f ω‖ := by
          simpa [h_norm_prod] using Complex.abs_re_le_norm (Complex.I * t * f ω)
        exact h₁.trans h₂
      have h_mul_le : ‖t‖ * ‖f ω‖ ≤ ε * M := by
        have h_mul_le₁ : ‖t‖ * ‖f ω‖ ≤ ε * ‖f ω‖ :=
          mul_le_mul_of_nonneg_right ht_le (norm_nonneg _)
        have h_mul_le₂ : ε * ‖f ω‖ ≤ ε * M :=
          mul_le_mul_of_nonneg_left hf_le (le_of_lt hε_pos)
        exact h_mul_le₁.trans h_mul_le₂
      have h_epsM_nonneg : 0 ≤ ε * M := mul_nonneg (le_of_lt hε_pos) hM_nonneg
      have h_epsM_le : ε * M ≤ 2 * ε * M := by
        have h_one_le_two : (1 : ℝ) ≤ 2 := by norm_num
        have := mul_le_mul_of_nonneg_right h_one_le_two h_epsM_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_re_le_eps : Complex.re (Complex.I * t * f ω) ≤ ε * M :=
        h_re_le_norm.trans h_mul_le
      exact h_re_le_eps.trans h_epsM_le

    have h_exp_le : Real.exp (Complex.re (Complex.I * t * f ω)) ≤ K :=
      Real.exp_le_exp.mpr h_re_le_two

    calc ‖F' t ω‖
      = ‖f ω‖ * Real.exp (Complex.re (Complex.I * t * f ω)) := h_normF'
    _ ≤ ‖f ω‖ * K := mul_le_mul_of_nonneg_left h_exp_le (norm_nonneg _)
    _ = K * H ω := by simp [H, mul_comm]

  -- Strong measurability of the parametrized integrand in a neighborhood of 0
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℂ), AEStronglyMeasurable (F t) μ := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have h_meas_inner : Measurable fun ω => g ω * (Complex.I * t) :=
      (hg_sm.measurable.mul_const (Complex.I * t))
    refine ⟨fun ω => Complex.exp (Complex.I * t * g ω),
      by
        have h_meas_exp : Measurable fun ω => Complex.exp (Complex.I * t * g ω) := by
          simpa [mul_comm, mul_left_comm] using h_meas_inner.cexp
        exact h_meas_exp.stronglyMeasurable,
      ?_⟩
    refine hfg.mono ?_
    intro ω hω
    simp [F, hω, mul_comm, mul_left_comm]

  -- Integrability at the base point t = 0 (constant integrand 1)
  have hF_int : Integrable (F 0) μ := by simp [F]

  -- Strong measurability of the derivative candidate at t = 0
  have hF'_meas : AEStronglyMeasurable (F' 0) μ := by
    refine ⟨fun ω => Complex.I * g ω, ?_, ?_⟩
    · have h_meas : Measurable fun ω => Complex.I * g ω :=
        (measurable_const.mul hg_sm.measurable)
      exact h_meas.stronglyMeasurable
    · refine hfg.mono ?_
      intro ω hω
      simp [F', hω, mul_comm, mul_left_comm]

  -- The dominating function is integrable since H is
  have h_bound_int : Integrable (fun ω => K * H ω) μ := by
    simp [H, mul_comm]
    exact hH_int.mul_const K

  -- Pointwise differentiability of the integrand (holds everywhere)
  have h_diff : ∀ᵐ ω ∂μ, ∀ t ∈ Metric.ball (0 : ℂ) ε, HasDerivAt (fun z => F z ω) (F' t ω) t := by
    refine Filter.Eventually.of_forall ?_
    intro ω t ht
    have h_inner : HasDerivAt (fun z : ℂ => z * (Complex.I * f ω)) (Complex.I * f ω) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id t).mul_const (Complex.I * f ω))
    have h_inner' : HasDerivAt (fun z : ℂ => Complex.I * z * f ω) (Complex.I * f ω) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_inner
    have h_exp := (Complex.hasDerivAt_exp _).comp t h_inner'
    simpa [F, F', mul_comm, mul_left_comm] using h_exp

  -- Apply the dominated differentiation theorem for parametrized integrals
  obtain ⟨-, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
      (bound := fun ω => K * H ω) hε_pos hF_meas hF_int hF'_meas
      (by
        refine h_bound.mono ?_
        intro ω hω t ht
        have : ‖t‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ht
        exact hω t this) h_bound_int h_diff
  -- Finish by rewriting the target derivative expression
  simpa [F', F, mul_comm, mul_left_comm] using h_deriv

/-- Helper structure for the dominated convergence estimates that control the
mixed derivatives of the exponential integrand.  Splitting the proof into
leaner lemmas keeps the main statement readable. -/
lemma _root_.bound_difference_quotient_exp
  (u v : α → ℂ) (μ : Measure α) [SigmaFinite μ]
  (_hu : Integrable (fun ω ↦ ‖u ω‖) μ)
  (_hv : Integrable (fun ω ↦ ‖v ω‖) μ) :
    True := by
  -- TODO: prove the quantitative bound described in `texts/mixed.txt`.
  -- This placeholder keeps the tactic state lightweight while we build out
  -- the rest of the argument.  The eventual goal is to bound the mixed
  -- difference quotient by an integrable majorant depending only on `u` and
  -- `v`.
  trivial

/-- Mixed differentiation under the integral sign for characteristic-type
integrands.  This lemma is being developed in `IntegralDifferentiation.lean`
so that it can be reused by multiple files without duplicating the analytic
machinery.

*Hypotheses*
* `μ` is sigma-finite.
* `u`, `v` are measurable functions with integrable product (this follows from
  the Option B axiom in the GFF application).

*Conclusion*
The mixed derivative of the parameterized integral equals the integral of the
pointwise mixed derivative.
-/
lemma mixed_deriv_under_integral
    (μ : Measure α) [SigmaFinite μ]
    (u v : α → ℂ)
    (hu_int : Integrable u μ)
    (hv_int : Integrable v μ)
    (huv_int : Integrable (fun ω ↦ u ω * v ω) μ) :
    deriv
        (fun t : ℂ ↦ deriv
          (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) ∂μ) 0)
        0
      = ∫ ω,
          deriv
            (fun t : ℂ ↦ deriv
              (fun s : ℂ ↦ Complex.exp (Complex.I * (t * u ω + s * v ω))) 0)
            0 ∂μ := by
  classical
  -- Step 1: express the inner derivative using the single derivative lemma in `s`.
  -- For fixed t, we differentiate ∫ exp(i*(t*u + s*v)) with respect to s.
  have h_step_s : ∀ t : ℂ,
      HasDerivAt
        (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) ∂μ)
        (∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (t * u ω)) ∂μ) 0 := by
    intro t
    -- Rewrite the integrand as exp(i*t*u) * exp(i*s*v) and apply the single derivative lemma
    have h_rewrite : ∀ s ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) =
        Complex.exp (Complex.I * t * u ω) * Complex.exp (Complex.I * s * v ω) := by
      intro s ω
      rw [← Complex.exp_add]
      congr 1
      ring
    -- Apply deriv_under_integral_exp with f = v and multiply by exp(i*t*u)
    sorry

  -- Step 2: differentiate the resulting integral with respect to `t`.
  -- Now we differentiate ∫ i*v*exp(i*t*u) with respect to t.
  have h_step_t :
      HasDerivAt
        (fun t : ℂ ↦
          ∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (t * u ω)) ∂μ)
        (∫ ω, Complex.I * v ω * (Complex.I * u ω) * Complex.exp (Complex.I * 0 * u ω) ∂μ) 0 := by
    -- Apply deriv_under_integral_exp with f = i*v*u
    sorry

  -- Step 3: simplify and assemble the final statement.
  have h_simplify : ∫ ω, Complex.I * v ω * (Complex.I * u ω) * Complex.exp (Complex.I * 0 * u ω) ∂μ =
      ∫ ω, -(u ω * v ω) ∂μ := by
    simp only [mul_zero]
    congr 1
    ext ω
    -- i * v * (i * u) = i^2 * u * v = -u * v
    ring_nf
    simp [Complex.I_sq]

  -- Connect the derivative computations using h_step_s
  have h_deriv_eq : deriv (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (0 * u ω + s * v ω)) ∂μ) 0 =
      ∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (0 * u ω)) ∂μ := by
    exact (h_step_s 0).deriv

  -- Simplify the derivative expression
  have h_step_s_simplified : ∫ ω, Complex.I * v ω * Complex.exp (Complex.I * (0 * u ω)) ∂μ =
      ∫ ω, Complex.I * v ω ∂μ := by
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one]

  -- Apply the chain rule using HasDerivAt.comp
  have h_comp : HasDerivAt
      (fun t : ℂ ↦ deriv (fun s : ℂ ↦ ∫ ω, Complex.exp (Complex.I * (t * u ω + s * v ω)) ∂μ) 0)
      (∫ ω, -(u ω * v ω) ∂μ) 0 := by
    -- Use the fact that deriv commutes with our derivative computations
    rw [← h_simplify]
    -- Apply h_step_t to the simplified form
    convert h_step_t using 1
    -- Show that deriv (h_step_s t) equals the target function
    ext t
    simp only [zero_mul, mul_zero, Complex.exp_zero, mul_one] at h_step_s_simplified
    exact (h_step_s t).deriv

  -- Convert HasDerivAt to deriv equation
  rw [h_comp.deriv]

  -- The RHS computation: pointwise mixed derivative
  have h_rhs : ∫ ω, -(u ω * v ω) ∂μ =
      ∫ ω, deriv (fun t ↦ deriv (fun s ↦ Complex.exp (Complex.I * (t * u ω + s * v ω))) 0) 0 ∂μ := by
    congr 1
    ext ω
    -- Pointwise: ∂_t[∂_s[exp(i*(t*u + s*v))]|_{s=0}]|_{t=0}
    -- = ∂_t[i*v*exp(i*t*u)]|_{t=0} = i*v*i*u*exp(0) = -u*v
    sorry

  exact h_rhs

end Aqft2
