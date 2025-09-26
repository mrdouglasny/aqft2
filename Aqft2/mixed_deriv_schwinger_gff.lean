/-
Discharge axioms for the direct DCT proof of mixed_deriv_schwinger in the GFF case.

This file provides GFF-specific lemmas (or axioms to be proved) that justify:
- Linearity of the complex pairing in the test-function argument
- Differentiation under the integral in s and t (Dominated Convergence)
- Identification of SchwingerFunctionℂ₂ with the product integral
- Integrability bounds required for DCT

Strategy:
- pairing_linear_combo: algebraic, independent of μ; can be proved from the definition
  of distributionPairingℂ_real (complex decomposition) and linearity of ω on real test functions.
- schwinger_eq_integral_product: follows by unfolding SchwingerFunctionℂ at n = 2
  and computing the product over Fin 2.
- deriv_under_integral_* and integrability lemmas: GFF-specific; use Minlos/real CF
  to derive L¹/L² integrability of linear functionals, then apply DCT.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.Complex.Basic

import Aqft2.Basic
import Aqft2.Schwinger
import Aqft2.MinlosAnalytic
import Aqft2.GFFMconstruct

open MeasureTheory Complex

noncomputable section

namespace MixedDerivGFF

-- Key lemma: how reCLM behaves with complex operations
private lemma re_of_complex_combination (a b : ℂ) (u v : ℂ) :
  Complex.re (a * u + b * v) = a.re * u.re - a.im * u.im + b.re * v.re - b.im * v.im := by
  -- Use basic complex arithmetic
  simp only [add_re, mul_re]
  ring

-- Key lemma: how imCLM behaves with complex operations
private lemma im_of_complex_combination (a b : ℂ) (u v : ℂ) :
  Complex.im (a * u + b * v) = a.re * u.im + a.im * u.re + b.re * v.im + b.im * v.re := by
  -- Use basic complex arithmetic
  simp only [add_im, mul_im]
  ring

/-- ω-linearity of the real component of the complex test-function decomposition under
    complex linear combinations. This follows from ℝ-linearity of ω and pointwise
    behavior of complex operations on Schwartz functions. -/
lemma ω_re_decompose_linear
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  ω ((complex_testfunction_decompose (t • f + s • g)).1)
    = t.re * ω ((complex_testfunction_decompose f).1)
      - t.im * ω ((complex_testfunction_decompose f).2)
      + s.re * ω ((complex_testfunction_decompose g).1)
      - s.im * ω ((complex_testfunction_decompose g).2) := by
  -- First, identify the real-part test function of t•f + s•g as a linear combination
  have h_sum_re_eq :
      (complex_testfunction_decompose (t • f + s • g)).1
        = t.re • (complex_testfunction_decompose f).1
          - t.im • (complex_testfunction_decompose f).2
          + s.re • (complex_testfunction_decompose g).1
          - s.im • (complex_testfunction_decompose g).2 := by
    ext x
    -- Rewrite to Complex.re/Complex.im and use algebra on ℂ
    change Complex.reCLM ((t • f + s • g) x)
        = t.re * Complex.reCLM (f x) - t.im * Complex.imCLM (f x)
          + s.re * Complex.reCLM (g x) - s.im * Complex.imCLM (g x)
    -- Evaluate pointwise scalar multiplication and addition
    simp
    -- Switch CLMs to the scalar functions and finish with the algebraic identity
    change Complex.re (t * f x + s * g x)
        = t.re * Complex.re (f x) - t.im * Complex.im (f x)
          + s.re * Complex.re (g x) - s.im * Complex.im (g x)
    simpa using re_of_complex_combination t s (f x) (g x)
  -- Apply ω (a real-linear functional) to both sides
  have := congrArg (fun (φ : TestFunction) => ω φ) h_sum_re_eq
  -- Simplify using linearity of ω over ℝ
  simpa [map_add, map_sub, map_smul]
    using this

/-- ω-linearity of the imaginary component of the complex test-function decomposition under
    complex linear combinations. -/
lemma ω_im_decompose_linear
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  ω ((complex_testfunction_decompose (t • f + s • g)).2)
    = t.re * ω ((complex_testfunction_decompose f).2)
      + t.im * ω ((complex_testfunction_decompose f).1)
      + s.re * ω ((complex_testfunction_decompose g).2)
      + s.im * ω ((complex_testfunction_decompose g).1) := by
  -- Identify the imaginary-part test function of t•f + s•g as a linear combination
  have h_sum_im_eq :
      (complex_testfunction_decompose (t • f + s • g)).2
        = t.re • (complex_testfunction_decompose f).2
          + t.im • (complex_testfunction_decompose f).1
          + s.re • (complex_testfunction_decompose g).2
          + s.im • (complex_testfunction_decompose g).1 := by
    ext x
    -- Rewrite to Complex.im/Complex.re and use algebra on ℂ
    change Complex.imCLM ((t • f + s • g) x)
        = t.re * Complex.imCLM (f x) + t.im * Complex.reCLM (f x)
          + s.re * Complex.imCLM (g x) + s.im * Complex.reCLM (g x)
    -- Evaluate pointwise scalar multiplication and addition
    simp
    -- Switch CLMs to scalar functions and finish with the algebraic identity
    change Complex.im (t * f x + s * g x)
        = t.re * Complex.im (f x) + t.im * Complex.re (f x)
          + s.re * Complex.im (g x) + s.im * Complex.re (g x)
    simpa using im_of_complex_combination t s (f x) (g x)
  -- Apply ω (a real-linear functional) to both sides
  have := congrArg (fun (φ : TestFunction) => ω φ) h_sum_im_eq
  -- Simplify using linearity of ω over ℝ
  simpa [map_add, map_smul]
    using this

/-- Linearity of the complex pairing in the test-function argument. -/
lemma pairing_linear_combo
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  distributionPairingℂ_real ω (t • f + s • g)
    = t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g := by
  classical
  apply Complex.ext
  · -- Real parts
    -- Expand both sides to re/imag pieces
    simp [distributionPairingℂ_real]
    -- Goal is now: ω ((complex_testfunction_decompose (t•f+s•g)).1)
    --              = (t * ((ω (..f..).1 + i ω (..f..).2)) + s * ((ω (..g..).1 + i ω (..g..).2))).re
    -- Use algebraic identity on the RHS
    have hre_rhs :
        (t * ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
            + s * ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))).re
          = t.re * ω ((complex_testfunction_decompose f).1)
              - t.im * ω ((complex_testfunction_decompose f).2)
              + s.re * ω ((complex_testfunction_decompose g).1)
              - s.im * ω ((complex_testfunction_decompose g).2) := by
      simpa using re_of_complex_combination t s
        ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
        ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))
    -- Use ω-linearity identity on the LHS
    have hre := ω_re_decompose_linear ω f g t s
    -- Finish by rewriting both sides to the same expression
    simpa [hre_rhs, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using hre
  · -- Imag parts
    simp [distributionPairingℂ_real]
    have him_rhs :
        (t * ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
            + s * ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))).im
          = t.re * ω ((complex_testfunction_decompose f).2)
              + t.im * ω ((complex_testfunction_decompose f).1)
              + s.re * ω ((complex_testfunction_decompose g).2)
              + s.im * ω ((complex_testfunction_decompose g).1) := by
      simpa using im_of_complex_combination t s
        ((ω ((complex_testfunction_decompose f).1) : ℂ) + I * (ω ((complex_testfunction_decompose f).2) : ℂ))
        ((ω ((complex_testfunction_decompose g).1) : ℂ) + I * (ω ((complex_testfunction_decompose g).2) : ℂ))
    have him := ω_im_decompose_linear ω f g t s
    simpa [him_rhs, add_comm, add_left_comm, add_assoc]
      using him

/-- Schwinger function at n=2 equals the product integral (complex version). -/
lemma schwinger_eq_integral_product
  (μ : ProbabilityMeasure FieldConfiguration) (f g : TestFunctionℂ) :
  SchwingerFunctionℂ₂ μ f g
    = ∫ ω, distributionPairingℂ_real ω f * distributionPairingℂ_real ω g ∂μ.toMeasure := by
  -- Unfold SchwingerFunctionℂ₂ and compute the product over Fin 2
  unfold SchwingerFunctionℂ₂
  unfold SchwingerFunctionℂ
  -- The product over Fin 2 of v i is v 0 * v 1; here v 0 = f, v 1 = g
  -- Use the Fin.prod_univ_two simp lemma
  simp [Fin.prod_univ_two]

/-- Dominated convergence for the t-derivative at 0 of the integrand obtained after differentiating in s at 0. -/
axiom gff_dom_t_linear_exp_at0
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  deriv (fun t =>
    ∫ ω, (Complex.I * distributionPairingℂ_real ω g)
          * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))
        ∂(gaussianFreeField_free m).toMeasure) 0
  = ∫ ω, (Complex.I * distributionPairingℂ_real ω g)
           * (Complex.I * distributionPairingℂ_real ω f)
        ∂(gaussianFreeField_free m).toMeasure

/-- t-derivative at 0 of exp(I·t·A(ω)) is I·A(ω). -/
private lemma deriv_exp_linear_in_t_at0
  (A : FieldConfiguration → ℂ) (ω : FieldConfiguration) :
  deriv (fun t => Complex.exp (Complex.I * (t * A ω))) 0 = Complex.I * A ω := by
  -- h(t) = I * (t * A ω) has derivative I * A ω at 0
  have h1 : HasDerivAt (fun t : ℂ => t * A ω) (A ω) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const (A ω)
  have h2 : HasDerivAt (fun t : ℂ => Complex.I * (t * A ω)) (Complex.I * (A ω)) 0 := by
    simpa using h1.const_mul Complex.I
  -- cexp ∘ h has derivative cexp(h 0) * h'(0) = 1 * (I * A ω)
  have h3 := h2.cexp
  simpa using h3.deriv

/-- HasDerivAt version of the above for compositional usage -/
private lemma hasDeriv_exp_linear_in_t_at0
  (A : FieldConfiguration → ℂ) (ω : FieldConfiguration) :
  HasDerivAt (fun t => Complex.exp (Complex.I * (t * A ω))) (Complex.I * A ω) 0 := by
  -- h(t) = I * (t * A ω) has derivative I * A ω at 0
  have h1 : HasDerivAt (fun t : ℂ => t * A ω) (A ω) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const (A ω)
  have h2 : HasDerivAt (fun t : ℂ => Complex.I * (t * A ω)) (Complex.I * (A ω)) 0 := by
    simpa using h1.const_mul Complex.I
  -- cexp ∘ h has derivative cexp(h 0) * h'(0) = 1 * (I * A ω)
  have h3 := h2.cexp
  simpa [zero_mul] using h3

/-- GFF-specific dominated convergence axiom to swap derivative and integral at s=0. -/
axiom gff_deriv_under_integral_s_at0
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) (t : ℂ) :
  deriv (fun s =>
    ∫ ω, Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                + s * distributionPairingℂ_real ω g))
        ∂(gaussianFreeField_free m).toMeasure) 0
  = ∫ ω, Complex.I * distributionPairingℂ_real ω g
          * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))
        ∂(gaussianFreeField_free m).toMeasure

/-- Pointwise derivative in s at 0 for the exponential with linear argument. -/
axiom deriv_exp_linear_at0
  (t : ℂ) (A B : FieldConfiguration → ℂ) (ω : FieldConfiguration) :
  deriv (fun s => Complex.exp (Complex.I * (t * A ω + s * B ω))) 0
    = Complex.I * B ω * Complex.exp (Complex.I * (t * A ω))

/-- Swap t-derivative and integral at 0 for the s-differentiated integrand (GFF case). -/
lemma gff_deriv_under_integral_t_at0
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  deriv (fun t =>
    ∫ ω, deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                                  + s * distributionPairingℂ_real ω g))) 0
        ∂(gaussianFreeField_free m).toMeasure) 0
  = ∫ ω, deriv (fun t => deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                                                 + s * distributionPairingℂ_real ω g))) 0) 0
        ∂(gaussianFreeField_free m).toMeasure := by
  -- First, rewrite the inner s-derivative using the GFF s-axiom
  have hrepr : (fun t =>
      ∫ ω, deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                                    + s * distributionPairingℂ_real ω g))) 0
          ∂(gaussianFreeField_free m).toMeasure)
      = (fun t =>
      ∫ ω, (Complex.I * distributionPairingℂ_real ω g)
              * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))
          ∂(gaussianFreeField_free m).toMeasure) := by
    funext t
    -- Use the GFF s-axiom and a pointwise derivative identity
    have hpt : (fun ω => deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0)
              = (fun ω => Complex.I * distributionPairingℂ_real ω g * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))) := by
      funext ω
      simpa using deriv_exp_linear_at0 t (fun ω' => distributionPairingℂ_real ω' f) (fun ω' => distributionPairingℂ_real ω' g) ω
    -- Apply integral extensionality
    simp [hpt]
  -- Take derivative at 0 of both sides
  have hderiv : deriv (fun t =>
      ∫ ω, deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                                    + s * distributionPairingℂ_real ω g))) 0
          ∂(gaussianFreeField_free m).toMeasure) 0
      = deriv (fun t =>
      ∫ ω, (Complex.I * distributionPairingℂ_real ω g)
              * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))
          ∂(gaussianFreeField_free m).toMeasure) 0 := by
    simp [hrepr]

  -- Identify the mixed pointwise derivative with (I·B)*(I·A)
  have hpt_mixed : (fun ω =>
        deriv (fun t => deriv (fun s =>
          Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                   + s * distributionPairingℂ_real ω g))) 0) 0)
      = (fun ω => (Complex.I * distributionPairingℂ_real ω g)
                    * (Complex.I * distributionPairingℂ_real ω f)) := by
    funext ω
    -- The inner s-derivative equals I·B·exp(I·t·A); then t-derivative at 0 gives I·B·I·A
    have hs : (fun t => deriv (fun s =>
        Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                 + s * distributionPairingℂ_real ω g))) 0)
        = (fun t => (Complex.I * distributionPairingℂ_real ω g)
                      * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))) := by
      funext t
      simpa using (deriv_exp_linear_at0 t (fun ω' => distributionPairingℂ_real ω' f)
                                  (fun ω' => distributionPairingℂ_real ω' g) ω)
    -- Differentiate in t at 0 using the calculus lemma in HasDerivAt form
    have hcexp := hasDeriv_exp_linear_in_t_at0 (fun ω' => distributionPairingℂ_real ω' f) ω
    have hmul := hcexp.const_mul (Complex.I * distributionPairingℂ_real ω g)
    simpa [hs] using hmul.deriv
  -- Conclude by chaining equalities
  calc
    deriv (fun t =>
      ∫ ω, deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                                    + s * distributionPairingℂ_real ω g))) 0
          ∂(gaussianFreeField_free m).toMeasure) 0
      = deriv (fun t =>
          ∫ ω, (Complex.I * distributionPairingℂ_real ω g)
                  * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f))
              ∂(gaussianFreeField_free m).toMeasure) 0 := hderiv
  _ = ∫ ω, (Complex.I * distributionPairingℂ_real ω g)
            * (Complex.I * distributionPairingℂ_real ω f)
        ∂(gaussianFreeField_free m).toMeasure := gff_dom_t_linear_exp_at0 m f g
  _ = ∫ ω, deriv (fun t => deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f
                                                                   + s * distributionPairingℂ_real ω g))) 0) 0
        ∂(gaussianFreeField_free m).toMeasure := by
          -- Rewrite the integrand via the pointwise identity
          simp [hpt_mixed]

/-- Differentiation under the integral in t at 0 (GFF case). -/
lemma deriv_under_integral_t'
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  deriv (fun t => ∫ ω, (deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0) ∂(gaussianFreeField_free m).toMeasure) 0
    = ∫ ω, deriv (fun t => deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0) 0 ∂(gaussianFreeField_free m).toMeasure := by
  -- Use the GFF domination axiom to interchange derivative and integral at 0
  exact gff_deriv_under_integral_t_at0 m f g

/-- Differentiation under the integral in s at 0 for the free GFF (derivative equals integral of pointwise derivative). -/
lemma deriv_under_integral_s'
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  ∀ t : ℂ,
    deriv (fun s => ∫ ω, Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g)) ∂(gaussianFreeField_free m).toMeasure) 0
      = ∫ ω, deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0 ∂(gaussianFreeField_free m).toMeasure := by
  intro t
  -- Use the GFF domination axiom to interchange derivative and integral at 0
  have h := gff_deriv_under_integral_s_at0 m f g t
  -- Identify the pointwise derivative
  have hpt : (fun ω => Complex.I * distributionPairingℂ_real ω g * Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f)))
            = (fun ω => deriv (fun s => Complex.exp (Complex.I * (t * distributionPairingℂ_real ω f + s * distributionPairingℂ_real ω g))) 0) := by
    funext ω
    -- apply the pointwise derivative lemma with A = ⟪ω,f⟫, B = ⟪ω,g⟫
    simpa using (deriv_exp_linear_at0 t (fun ω' => distributionPairingℂ_real ω' f) (fun ω' => distributionPairingℂ_real ω' g) ω).symm
  -- Rewrite the RHS of h using the pointwise derivative identity
  simpa [hpt]
    using h

/-
TODO (sketches):
- Prove pairing_linear_combo from the definition of distributionPairingℂ_real
  using complex_testfunction_decompose, additivity and ℝ-linearity of ω, and CLMs reCLM/imCLM.
- Prove schwinger_eq_integral_product by unfolding SchwingerFunctionℂ at n=2 and computing
  the product over Fin 2.
- For integrability and DCT, use MinlosAnalytic: apply all_real_moments_integrable_from_realCF
  with the free covariance to get L¹/L² moments on real pairings, then convert to complex
  (triangle inequality) and apply dominated convergence.
-/

end MixedDerivGFF
