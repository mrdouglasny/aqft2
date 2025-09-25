/-
Draft implementation of mixed_deriv_schwinger for testing and development.
This is a standalone file to work on the proof before copying back to GFFMconstruct.lean.

## PROOF PLAN FOR mixed_deriv_schwinger

**Goal:** Prove that for centered Gaussian measure μ and test functions f, g:
  deriv (fun t => deriv (fun s => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0 = -(SchwingerFunctionℂ₂ μ f g)

**Mathematical Background:**
The mixed derivative of the generating functional Φ(t,s) = Z[t•f + s•g] gives the second moment:
∂²Φ/∂t∂s|₀ = ∂²/∂t∂s ∫ exp(i⟨ω, t•f + s•g⟩) dμ(ω)|₀ = -∫ ⟨ω,f⟩⟨ω,g⟩ dμ = -E[⟨ω,f⟩⟨ω,g⟩]

**Step-by-Step Proof Strategy:**

1. **Integral Representation**
   Express GJGeneratingFunctionalℂ μ J as ∫ ω, exp(i⟨ω, J⟩) ∂μ

2. **Linearity of Pairing**
   Use ⟨ω, t•f + s•g⟩ = t⟨ω,f⟩ + s⟨ω,g⟩ to get pointwise form

3. **Pointwise Integrand**
   Define ϕω(t,s) = exp(i(t⟨ω,f⟩ + s⟨ω,g⟩))

4. **Pointwise Derivatives** (Chain Rule)
   - ∂ϕω/∂s = ϕω · (i⟨ω,g⟩)
   - ∂²ϕω/∂t∂s = ϕω · (i⟨ω,f⟩) · (i⟨ω,g⟩)
   - At (0,0): ϕω(0,0) = 1 and i² = -1
   - So: ∂²ϕω/∂t∂s|₀ = -⟨ω,f⟩⟨ω,g⟩

5. **Integrability Conditions**
   Show required functions are integrable under Gaussian measure:
   - ∫ |⟨ω,g⟩| dμ < ∞ (for first derivative)
   - ∫ |⟨ω,f⟩||⟨ω,g⟩| dμ < ∞ (for mixed derivative)
   (These follow from L² property of Gaussian linear functionals)

6. **Dominated Convergence** (Apply twice)
   - First: ∂/∂s under integral sign using majorant |⟨ω,g⟩|
   - Second: ∂/∂t under integral sign using majorant |⟨ω,f⟩||⟨ω,g⟩|

7. **Chain the Steps**
   ∂²/∂t∂s GJGeneratingFunctionalℂ μ (t•f + s•g)|₀
   = ∂²/∂t∂s ∫ ϕω(t,s) dμ|₀        (by definition)
   = ∫ ∂²ϕω/∂t∂s|₀ dμ              (by dominated convergence, twice)
   = ∫ (-⟨ω,f⟩⟨ω,g⟩) dμ             (by pointwise calculation)
   = -∫ ⟨ω,f⟩⟨ω,g⟩ dμ               (linearity of integral)
   = -SchwingerFunctionℂ₂ μ f g      (by definition)

**Key Technical Requirements:**
- Complex differentiability (analytic continuation from real case)
- Dominated convergence theorem for complex integrals
- Gaussianity ensures required integrability conditions
- Chain rule for complex exponentials

**Connection to Existing Code:**
This is the "sorry" proof at line 554 in Aqft2/GFFMconstruct.lean.
The mathematical structure is standard in constructive QFT.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Complex.Basic

import Aqft2.Basic
import Aqft2.Schwinger
import Aqft2.FunctionalAnalysis
import Aqft2.Euclidean
import Aqft2.DiscreteSymmetry
-- import Aqft2.GFFMconstruct  -- removed to avoid access to `schwinger_eq_Qc_free`

open MeasureTheory Complex

-- Local definition copied from before line 529 of `GFFMconstruct.lean`
/-- The complex 2-point Schwinger function for complex test functions. -/
noncomputable def SchwingerFunctionℂ₂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ ψ : TestFunctionℂ) : ℂ :=
  SchwingerFunctionℂ dμ_config 2 ![φ, ψ]

-- NOTE: This file is a WORKING TEMPLATE that should be implemented directly
-- in GFFMconstruct.lean where all the actual types and definitions exist.
-- The structure below shows the proof outline with placeholder sorrys.

-- Axioms supplying the analysis pieces we will later discharge from Gaussian facts
axiom integrable_pairing_L1
  (μ : ProbabilityMeasure FieldConfiguration) (f : TestFunctionℂ) :
  Integrable (fun ω => distributionPairingℂ_real ω f) μ.toMeasure

axiom integrable_pairing_product_L1
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  Integrable (fun ω => distributionPairingℂ_real ω f * distributionPairingℂ_real ω g) μ.toMeasure

axiom deriv_under_integral_s'
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  ∀ t : ℂ,
    deriv (fun s => ∫ ω, Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g)) ∂μ.toMeasure) 0
      = ∫ ω, deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0 ∂μ.toMeasure

axiom deriv_under_integral_t'
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  deriv (fun t => ∫ ω, (deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0) ∂μ.toMeasure) 0
    = ∫ ω, deriv (fun t => deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0) 0 ∂μ.toMeasure

-- Linearity of the complex pairing in the test-function argument
axiom pairing_linear_combo
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  distributionPairingℂ_real ω (t • f + s • g)
    = t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g

-- Schwinger function at n=2 equals the product integral
axiom schwinger_eq_integral_product
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ μ f g
    = ∫ ω, distributionPairingℂ_real ω f * distributionPairingℂ_real ω g ∂μ.toMeasure

-- Remove circular Minlos/bridge lemma to avoid dependency cycles
-- lemma mixed_deriv_schwinger'
--   (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
--   let μ := gaussianFreeField_free m
--   deriv (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
--     = -(SchwingerFunctionℂ₂ μ f g) := by
--   classical
--   -- Removed: relied on GFF_Minlos_Complex and schwinger_eq_Qc_free, creates circularity
--   skip

-- Auxiliary calculus lemma: mixed derivative at (0,0) of exp(I*(t*A + s*B)) equals -(A*B)
lemma cexp_mixed_deriv_at_zero (A B : ℂ) :
  deriv (fun t => deriv (fun s => Complex.exp (Complex.I * (t * A + s * B))) 0) 0 = -(A * B) := by
  classical
  -- First, compute the inner derivative with respect to s at 0
  have h_aff : ∀ t : ℂ, HasDerivAt (fun s : ℂ => t * A + s * B) B 0 := by
    intro t
    have h_const : HasDerivAt (fun _ : ℂ => t * A) 0 0 := by
      simpa using (hasDerivAt_const (x := (0 : ℂ)) (c := t * A))
    have h_lin : HasDerivAt (fun s : ℂ => s * B) B 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const B
    simpa [Pi.add_def] using h_const.add h_lin
  have h_inner : ∀ t : ℂ, HasDerivAt (fun s : ℂ => Complex.I * (t * A + s * B)) (Complex.I * B) 0 := by
    intro t; simpa [mul_add] using (h_aff t).const_mul Complex.I
  have h_s : ∀ t : ℂ, deriv (fun s => Complex.exp (Complex.I * (t * A + s * B))) 0
      = Complex.exp (Complex.I * (t * A)) * (Complex.I * B) := by
    intro t
    have h := (h_inner t).cexp
    -- derivative at s=0 equals exp(inner(0))*inner'(0), and inner(0) = I*(t*A)
    simpa using h.deriv
  -- Now differentiate in t at 0 the function g(t) = exp(I t A) * (I B)
  let f : ℂ → ℂ := fun t => Complex.exp (Complex.I * (t * A))
  have hf : HasDerivAt f (Complex.exp (Complex.I * (0 * A)) * (Complex.I * A)) 0 := by
    have h_tA : HasDerivAt (fun t : ℂ => t * A) A 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const A
    have h_inner_t : HasDerivAt (fun t : ℂ => Complex.I * (t * A)) (Complex.I * A) 0 := by
      simpa using h_tA.const_mul Complex.I
    simpa using h_inner_t.cexp
  let g : ℂ → ℂ := fun t => f t * (Complex.I * B)
  have hg : HasDerivAt g ((Complex.exp (Complex.I * (0 * A)) * (Complex.I * A)) * (Complex.I * B)) 0 := by
    simpa using hf.mul_const (Complex.I * B)
  have h_deriv_g : deriv g 0 = (Complex.exp (Complex.I * (0 * A)) * (Complex.I * A)) * (Complex.I * B) := by
    simpa using hg.deriv
  -- Simplify the value step by step
  have h_step0 : (Complex.exp (Complex.I * (0 * A)) * (Complex.I * A)) * (Complex.I * B)
              = (Complex.I * A) * (Complex.I * B) := by
    simp
  have h_step1 : (Complex.I * A) * (Complex.I * B) = (Complex.I * Complex.I) * (A * B) :=
    mul_mul_mul_comm (Complex.I) A (Complex.I) B
  have hI : Complex.I * Complex.I = (-1 : ℂ) := by simp
  -- Tie together with the outer derivative equality
  have h_fun_eq : (fun t => deriv (fun s => Complex.exp (Complex.I * (t * A + s * B))) 0) = g := by
    funext t; simp [g, f, h_s t]
  have h_eq2 : deriv g 0 = -(A * B) := by
    calc
      deriv g 0 = (Complex.exp (Complex.I * (0 * A)) * (Complex.I * A)) * (Complex.I * B) := h_deriv_g
      _ = (Complex.I * A) * (Complex.I * B) := h_step0
      _ = (Complex.I * Complex.I) * (A * B) := h_step1
      _ = -(A * B) := by simp [hI]
  simpa [h_fun_eq] using h_eq2

/-- Direct dominated-convergence approach (non-circular). -/
lemma mixed_deriv_schwinger_direct
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  deriv (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
    = -(SchwingerFunctionℂ₂ μ f g) := by
  classical
  let ϕω : FieldConfiguration → ℂ → ℂ → ℂ :=
    fun ω t s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))
  have generating_functional_eq : ∀ t s : ℂ,
    GJGeneratingFunctionalℂ μ (t • f + s • g) = ∫ ω, ϕω ω t s ∂μ.toMeasure := by
    intro t s
    unfold GJGeneratingFunctionalℂ
    have hfun : (fun ω => Complex.exp (Complex.I * distributionPairingℂ_real ω (t • f + s • g)))
              = (fun ω => ϕω ω t s) := by
      funext ω
      simp [ϕω, pairing_linear_combo ω f g t s, mul_add]
    simp [hfun]
  have diff_s := deriv_under_integral_s' μ f g
  have diff_t := deriv_under_integral_t' μ f g
  have pointwise_mixed_deriv : ∀ ω : FieldConfiguration,
      deriv (fun t => deriv (fun s => ϕω ω t s) 0) 0
        = -(distributionPairingℂ_real ω f * distributionPairingℂ_real ω g) := by
    intro ω
    -- apply the calculus lemma with A = ⟪ω,f⟫, B = ⟪ω,g⟫
    have := cexp_mixed_deriv_at_zero (A := distributionPairingℂ_real ω f) (B := distributionPairingℂ_real ω g)
    simpa [ϕω]
  calc
    deriv (fun t : ℂ => deriv (fun s : ℂ => GJGeneratingFunctionalℂ μ (t • f + s • g)) 0) 0
        = deriv (fun t : ℂ => deriv (fun s : ℂ => ∫ ω, ϕω ω t s ∂μ.toMeasure) 0) 0 := by
          congr 1; funext t; congr 1; funext s; simpa using generating_functional_eq t s
    _ = deriv (fun t : ℂ => ∫ ω, (deriv (fun s => ϕω ω t s) 0) ∂μ.toMeasure) 0 := by
          congr 1; funext t; simpa using diff_s t
    _ = ∫ ω, deriv (fun t => deriv (fun s => ϕω ω t s) 0) 0 ∂μ.toMeasure := by
          simpa using diff_t
    _ = ∫ ω, -(distributionPairingℂ_real ω f * distributionPairingℂ_real ω g) ∂μ.toMeasure := by
          congr 1; funext ω; simpa using pointwise_mixed_deriv ω
    _ = -(∫ ω, (distributionPairingℂ_real ω f * distributionPairingℂ_real ω g) ∂μ.toMeasure) := by
          simpa using (MeasureTheory.integral_neg (μ := μ.toMeasure) (f := fun ω => distributionPairingℂ_real ω f * distributionPairingℂ_real ω g))
    _ = -(SchwingerFunctionℂ₂ μ f g) := by
          rw [schwinger_eq_integral_product μ f g]

-- Remove GFF-specific integrability lemmas and Minlos-based utilities from this draft to avoid circular imports.
-- They will be discharged in a separate GFF-specific file by importing MinlosAnalytic/GFF.
