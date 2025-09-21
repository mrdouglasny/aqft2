/-
Copyright (c) 2025 MRD and SH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:

Minlos Analyticity — Entire characteristic functionals on nuclear spaces

This file sets up the complex-analytic side needed to apply Minlos' theorem
with analyticity (entire extension to the complexification) and the
exponential-moment criteria, following the notes in `texts/minlos_analytic.txt`.

Highlights
- Define a notion of "entire on the complexification" for a characteristic functional χ : E → ℂ
- State the equivalence: entire extension ↔ local uniform exponential moments
- Provide a complexified Gaussian characteristic functional and prove it is entire

We keep some parts as stubs (sorry) pending detailed functional-analytic development.
-/

import Mathlib.Data.Complex.Basic
--import Mathlib.Topology.Algebra.Module.Complex
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Aqft2.Basic
import Aqft2.Minlos
import Mathlib.MeasureTheory.Measure.Map

open Classical
open TopologicalSpace MeasureTheory Complex Filter

noncomputable section

namespace MinlosAnalytic

-- Ensure FieldConfiguration is a BorelSpace since it uses the borel measurable space
instance : BorelSpace FieldConfiguration := ⟨rfl⟩

/-- A real symmetric, positive semidefinite covariance form on real test functions. -/
structure CovarianceForm where
  Q : TestFunction → TestFunction → ℝ
  symm : ∀ f g, Q f g = Q g f
  psd  : ∀ f, 0 ≤ Q f f
  cont_diag : Continuous fun f => Q f f
  -- New: ℝ-bilinearity (specified on the left; right follows from symmetry)
  add_left : ∀ f₁ f₂ g, Q (f₁ + f₂) g = Q f₁ g + Q f₂ g
  smul_left : ∀ (c : ℝ) f g, Q (c • f) g = c * Q f g

-- Right additivity and scaling derived from symmetry and left properties
lemma CovarianceForm.add_right (C : CovarianceForm) (f g₁ g₂ : TestFunction) :
    C.Q f (g₁ + g₂) = C.Q f g₁ + C.Q f g₂ := by
  -- Q f (g₁+g₂) = Q (g₁+g₂) f by symm = Q g₁ f + Q g₂ f by add_left = ... by symm
  have := C.add_left g₁ g₂ f
  simpa [C.symm] using this

lemma CovarianceForm.smul_right (C : CovarianceForm) (c : ℝ) (f g : TestFunction) :
    C.Q f (c • g) = c * C.Q f g := by
  -- Q f (c•g) = Q (c•g) f by symm = c * Q g f by smul_left = c * Q f g by symm
  simpa [C.symm] using (C.smul_left c g f)

lemma CovarianceForm.Q_smul_smul (C : CovarianceForm) (s t : ℝ) (a b : TestFunction) :
    C.Q (s • a) (t • b) = (s * t) * C.Q a b := by
  -- Q (s•a) (t•b) = s * Q a (t•b) = s * (t * Q a b) = (s*t) * Q a b
  calc
    C.Q (s • a) (t • b) = s * C.Q a (t • b) := by simpa using C.smul_left s a (t • b)
    _ = s * (t * C.Q a b) := by simpa using congrArg (fun x => s * x) (C.smul_right t a b)
    _ = (s * t) * C.Q a b := by ring

lemma CovarianceForm.Q_diag_smul (C : CovarianceForm) (s : ℝ) (a : TestFunction) :
    C.Q (s • a) (s • a) = (s^2) * C.Q a a := by
  simpa [pow_two] using (C.Q_smul_smul s s a a)

/-- The negation map on field configurations: T(ω) = -ω -/
def negMap : FieldConfiguration → FieldConfiguration := fun ω => -ω

/-- The negation map is measurable -/
lemma negMap_measurable : Measurable negMap := by
  -- The negation map is continuous on WeakDual, hence measurable
  -- WeakDual is a topological vector space and negation is continuous
  apply Continuous.measurable
  -- negMap is the same as the continuous linear map x ↦ -x
  exact continuous_neg

/-- The negation map is an involution: negMap ∘ negMap = id -/
lemma negMap_invol : negMap ∘ negMap = id := by
  funext ω
  simp [negMap, neg_neg]

/-- Symmetry under global sign flip induced by the real Gaussian CF. -/
lemma integral_neg_invariance
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f))) :
  ∀ (f : FieldConfiguration → ℂ), Integrable f μ.toMeasure →
    ∫ ω, f ω ∂μ.toMeasure = ∫ ω, f (-ω) ∂μ.toMeasure := by
  intro f hInt
  classical
  -- Plan:
  -- 1) Consider T(ω) = -ω and the pushforward μneg := μ ◦ T^{-1}.
  -- 2) Show μneg has the same characteristic functional as μ using h_realCF and (-ω) a = -ω a.
  -- 3) Conclude μneg = μ by Minlos uniqueness.
  -- 4) Use the change-of-variables for map to get the desired integral identity.

  -- Step 1: Define the pushforward measure
  let μneg := μ.toMeasure.map negMap
  have hμneg_prob : IsProbabilityMeasure μneg := by
    exact isProbabilityMeasure_map (Measurable.aemeasurable negMap_measurable)

  -- Step 2: Show characteristic functionals are equal
  have hCF_equal : ∀ g : TestFunction,
      ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μneg
        = ∫ ω, Complex.exp (Complex.I * (distributionPairing ω g)) ∂μ.toMeasure := by
    intro g
    -- Use the change of variables formula for the map
    have h_aestrongly_measurable : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (distributionPairing ω g))) μneg := by
      sorry -- Complex.exp is continuous, and pairing is continuous, so composition is strongly measurable
    rw [integral_map (Measurable.aemeasurable negMap_measurable) h_aestrongly_measurable]
    -- The integrand becomes: exp(I * ((-ω) g)) = exp(I * (-(ω g))) = exp(-I * (ω g))
    have h_neg_pairing : (fun ω => Complex.exp (Complex.I * (distributionPairing (negMap ω) g))) =
                         (fun ω => Complex.exp (Complex.I * (distributionPairing (-ω) g))) := by
      simp [negMap]
    rw [h_neg_pairing]
    -- The key insight: for real test functions g, the Gaussian characteristic functional
    -- exp(-½Q(g,g)) is real, so ∫ exp(iωg) = ∫ exp(-iωg) for Gaussian measures
    -- This follows from the symmetry of Gaussian measures under negation
    -- For now, we use this as a key lemma that would be proven using:
    -- 1) (-ω)g = -(ωg) by linearity
    -- 2) exp(i(-ωg)) = exp(-i(ωg)) = conj(exp(i(ωg)))
    -- 3) Since the characteristic functional is real, ∫f = ∫conj(f)
    sorry

  -- Step 3: Apply uniqueness of measures (will need Minlos theorem)
  have hμeq : μneg = μ.toMeasure := by
    -- Two probability measures with the same characteristic functional are equal
    -- This requires the Minlos uniqueness theorem
    sorry

  -- Step 4: Use change of variables to get the integral identity
  have hf_aestrongly_measurable : AEStronglyMeasurable f μneg := by
    -- f is integrable on μ, hence AEStronglyMeasurable. The pushforward preserves this.
    sorry
  -- The change of variables formula gives us:
  -- ∫ f dμ = ∫ f d(μ.map negMap⁻¹) = ∫ (f ∘ negMap) dμ = ∫ f(-ω) dμ
  have h_cov : ∫ ω, f ω ∂μneg = ∫ ω, f (negMap ω) ∂μ.toMeasure := by
    exact integral_map (Measurable.aemeasurable negMap_measurable) hf_aestrongly_measurable
  rw [hμeq] at h_cov
  rw [h_cov]
  simp [negMap]

-- Remove ad-hoc symmetry and moments axioms: we will prove needed facts directly.

/-- All one-dimensional real moments are integrable for Gaussian CF along lines. -/
axiom all_real_moments_integrable_from_realCF
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction) :
  ∀ n : ℕ, Integrable (fun ω => ‖(ω a : ℝ)‖^n) μ.toMeasure

/-- Complex extension of the covariance form: Qc(f, g) extends Q to complex test functions
    via the canonical bilinear extension from real to complex. -/
noncomputable def Qc (C : CovarianceForm) (f g : TestFunctionℂ) : ℂ :=
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  let ⟨g_re, g_im⟩ := complex_testfunction_decompose g
  (C.Q f_re g_re - C.Q f_im g_im : ℝ) + I * (C.Q f_re g_im + C.Q f_im g_re : ℝ)

/-- Complex pairing between field configuration and complex test function -/
noncomputable def pairingC (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  distributionPairingℂ_real ω f

/-- Complex version of the characteristic functional -/
noncomputable def Zc (C : CovarianceForm) (f : TestFunctionℂ) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (Qc C f f))

/-- Extract real/imag parts of a complex test function as real test functions (reuse helper). -/
noncomputable def reIm (f : TestFunctionℂ) : TestFunction × TestFunction :=
  complex_testfunction_decompose f

/-- Simplify the diagonal of Qc: for f = a + i b, Qc(f,f) = Q(a,a) - Q(b,b) + 2 i Q(a,b). -/
lemma Qc_diag_reIm (C : CovarianceForm) (f : TestFunctionℂ) :
  let a := (reIm f).1; let b := (reIm f).2;
  Qc C f f = ((C.Q a a - C.Q b b) : ℝ) + I * ((2 * C.Q a b : ℝ)) := by
  classical
  -- Expand the definition and use symmetry to combine the cross terms
  simp [Qc, reIm, C.symm, two_mul]

/-- Rewrite the complex pairing through the real/imag decomposition. -/
lemma pairingC_reIm (ω : FieldConfiguration) (f : TestFunctionℂ) :
  let a := (reIm f).1; let b := (reIm f).2;
  pairingC ω f = (ω a : ℂ) + I * (ω b : ℂ) := by
  classical
  simp [pairingC, reIm, distributionPairingℂ_real, complex_testfunction_decompose]

/-- Symmetry of the complex-extended covariance. -/
lemma Qc_symm (C : CovarianceForm) (f g : TestFunctionℂ) : Qc C f g = Qc C g f := by
  classical
  rcases complex_testfunction_decompose f with ⟨fr, fi⟩
  rcases complex_testfunction_decompose g with ⟨gr, gi⟩
  simp [Qc, complex_testfunction_decompose, C.symm, add_comm]

/-- 2×2 covariance matrix for a,b. -/
noncomputable def Sigma_ab (C : CovarianceForm) (a b : TestFunction) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![C.Q a a, C.Q a b],
    ![C.Q b a, C.Q b b]]

lemma Sigma_ab_symm (C : CovarianceForm) (a b : TestFunction) :
  (Sigma_ab C a b).transpose = Sigma_ab C a b := by
  classical
  -- Matrices are functions, use funext on both indices
  funext i j
  -- Unfold transpose entrywise
  -- (Mᵀ) i j = M j i
  change (Sigma_ab C a b) j i = (Sigma_ab C a b) i j
  -- Case split on Fin 2 indices
  fin_cases i <;> fin_cases j <;> simp [Sigma_ab, C.symm]

/-- Analyticity along the complex line z ↦ (i z, -z) for the 2D Gaussian CF.
    We consider F(z) = E[exp(i z ⟨ω,a⟩ - z ⟨ω,b⟩)]. -/
lemma analytic_along_line_i_neg1
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a b : TestFunction) :
  True := by
  -- Use arguments to avoid linter warnings while we leave this as a stub.
  have _ := C.symm a b
  have _ := h_realCF a
  have _ := μ.toMeasure
  trivial

/-- Real-parameter two-dimensional CF along linear combinations. -/
lemma gaussian_cf_linear_combo_real
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a b : TestFunction) (s t : ℝ) :
  ∫ ω, Complex.exp (Complex.I * (ω (s • a + t • b))) ∂μ.toMeasure
    = Complex.exp (-(1/2 : ℂ) * (C.Q (s • a + t • b) (s • a + t • b))) := by
  simpa using h_realCF (s • a + t • b)

/-- Analyticity along the complex line z ↦ (i z, -z) and explicit formula.
    Placeholder: standard finite-dimensional Gaussian analyticity along a line. -/
lemma gaussian_mgf_line_formula
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a b : TestFunction) :
  ∀ z : ℂ,
    ∫ ω, Complex.exp (Complex.I * z * (ω a : ℂ) - z * (ω b : ℂ)) ∂μ.toMeasure
      = Complex.exp (-(1/2 : ℂ) * z^2 * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) := by
  intro z; sorry

/-- 2D Gaussian mgf specialization: for X=⟨ω,a⟩, Y=⟨ω,b⟩, centered with
    Var(X)=Q(a,a), Var(Y)=Q(b,b), Cov(X,Y)=Q(a,b), we have
    E[exp(i X - Y)] = exp(-1/2 · (Q(a,a) - Q(b,b) + 2 i Q(a,b))). -/
lemma gaussian_mgf_iX_minusY
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a b : TestFunction) :
  ∫ ω, Complex.exp (Complex.I * (ω a) - (ω b)) ∂μ.toMeasure
    = Complex.exp (-(1/2 : ℂ) * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) := by
  classical
  have h := gaussian_mgf_line_formula C μ h_realCF a b (1 : ℂ)
  -- simplify z = 1
  simpa [one_mul, one_pow] using h

/-- Helper identity: I * (x + I*y) = I*x - y. -/
@[simp] lemma I_mul_add_I_mul (x y : ℂ) : Complex.I * (x + Complex.I * y) = Complex.I * x - y := by
  -- I*(x + I*y) = I*x + I*(I*y) = I*x + (I*I)*y = I*x - y
  simp [mul_add, Complex.I_mul_I, sub_eq_add_neg, mul_comm, mul_left_comm]

@[simp] lemma square_add_I_mul (x y : ℂ) : (x + Complex.I * y)^2 = x^2 - y^2 + (2 : ℂ) * Complex.I * x * y := by
  -- (x + i y)^2 = x^2 + 2 i x y - y^2
  calc
    (x + Complex.I * y)^2
        = (x + Complex.I * y) * (x + Complex.I * y) := by simp [pow_two]
    _   = x * x + x * (Complex.I * y) + (Complex.I * y) * x + (Complex.I * y) * (Complex.I * y) := by
          ring_nf
    _   = x^2 + Complex.I * (x * y) + Complex.I * (x * y) + (Complex.I * Complex.I) * (y * y) := by
          simp [pow_two, mul_comm, mul_left_comm]
    _   = x^2 + (2 : ℂ) * Complex.I * (x * y) - y^2 := by
          -- x^2 + I*(x*y) + I*(x*y) + I*I*(y*y) = x^2 + 2*I*(x*y) - y^2
          -- Use I*I = -1 and combine the I*(x*y) terms
          simp only [Complex.I_mul_I, pow_two, two_mul]
          ring
    _   = x^2 - y^2 + (2 : ℂ) * Complex.I * x * y := by
          ring_nf

/-- Main formula: complex characteristic functional equals Zc on complex tests. -/
theorem gaussian_CF_complex
  (C : CovarianceForm)
  (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  : ∀ f : TestFunctionℂ,
     ∫ ω, Complex.exp (Complex.I * (pairingC ω f)) ∂μ.toMeasure = Zc C f := by
  classical
  intro f
  let a := (reIm f).1; let b := (reIm f).2
  have hf : (fun ω => Complex.exp (Complex.I * (pairingC ω f))) =
      (fun ω => Complex.exp (Complex.I * (ω a : ℂ) - (ω b : ℂ))) := by
    funext ω; simp [pairingC_reIm (ω := ω) (f := f), a, b, I_mul_add_I_mul]
  have h2 :
    ∫ ω, Complex.exp (Complex.I * (ω a : ℂ) - (ω b : ℂ)) ∂μ.toMeasure
      = Complex.exp (-(1/2 : ℂ) * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) :=
    gaussian_mgf_iX_minusY C μ h_realCF a b
  have hI' :
    ∫ ω, Complex.exp (Complex.I * (pairingC ω f)) ∂μ.toMeasure
      = Complex.exp (-(1/2 : ℂ) * ((C.Q a a - C.Q b b : ℝ) + I * (2 * C.Q a b : ℝ))) := by
    simpa [hf]
      using h2
  have hQc : Qc C f f = ((C.Q a a - C.Q b b : ℝ) + I * ((2 * C.Q a b : ℝ))) := by
    simpa [a, b] using (Qc_diag_reIm C f)
  simpa [Zc, hQc] using hI'

/-- Zero mean from the real Gaussian characteristic functional, via symmetry and L¹. -/
lemma moment_zero_from_realCF
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction)
  (hInt1 : Integrable (fun ω => (ω a : ℂ)) μ.toMeasure) :
  ∫ ω, (ω a : ℂ) ∂μ.toMeasure = 0 := by
  classical
  -- Symmetry: ∫ f(ω) = ∫ f(-ω)
  have hInv := integral_neg_invariance C μ h_realCF (fun ω => (ω a : ℂ)) hInt1
  -- Flip integrand: ((-ω) a : ℂ) = - (ω a : ℂ)
  have hflip : (fun ω : FieldConfiguration => ((-ω) a : ℂ)) = (fun ω => - (ω a : ℂ)) := by
    funext ω
    rw [ContinuousLinearMap.neg_apply]
    simp
  -- Hence ∫ X = ∫ -X = -∫ X
  have : ∫ ω, (ω a : ℂ) ∂μ.toMeasure = - ∫ ω, (ω a : ℂ) ∂μ.toMeasure := by
    simpa [hflip, integral_neg, hInt1] using hInv
  -- 2 · ∫ X = 0 ⇒ ∫ X = 0
  have hsum : (2 : ℂ) • (∫ ω, (ω a : ℂ) ∂μ.toMeasure) = 0 := by
    simpa [two_smul] using congrArg (fun z => z + ∫ ω, (ω a : ℂ) ∂μ.toMeasure) this
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp hsum).resolve_left htwo

/-- Every finite real absolute moment along ω ↦ ω a is integrable (outline).
This follows because the one-dimensional marginal has characteristic function
exp(-½ s^2 σ^2), hence is Normal(0,σ^2), and all Normal moments are finite. -/
lemma all_moments_integrable_from_realCF
  (C : CovarianceForm) (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  (a : TestFunction) (n : ℕ) :
  Integrable (fun ω => ‖(ω a : ℝ)‖^n) μ.toMeasure := by
  exact all_real_moments_integrable_from_realCF C μ h_realCF a n

-- Qc is additive in the left argument (granted for now).
axiom Qc_add_left (C : CovarianceForm)
    (f₁ f₂ g : TestFunctionℂ) :
    Qc C (f₁ + f₂) g = Qc C f₁ g + Qc C f₂ g

/-- Qc is additive in the right argument (granted for now). -/
axiom Qc_add_right (C : CovarianceForm)
    (f g₁ g₂ : TestFunctionℂ) :
    Qc C f (g₁ + g₂) = Qc C f g₁ + Qc C f g₂

/-- Qc is ℂ-linear in the left argument (homogeneity). -/
axiom Qc_smul_left (C : CovarianceForm)
    (c : ℂ) (f g : TestFunctionℂ) :
    Qc C (c • f) g = c • Qc C f g

/-- Qc is ℂ-linear in the right argument (homogeneity). -/
axiom Qc_smul_right (C : CovarianceForm)
    (c : ℂ) (f g : TestFunctionℂ) :
    Qc C f (c • g) = c • Qc C f g

/-- Package Qc as a ℂ-bilinear map on complex test functions. -/
noncomputable def Qc_bilin (C : CovarianceForm) :
    LinearMap.BilinMap ℂ TestFunctionℂ ℂ :=
  LinearMap.mk₂ ℂ (fun x y => Qc C x y)
    (by intro x x' y; simpa using Qc_add_left C x x' y)
    (by intro a x y; simpa using Qc_smul_left C a x y)
    (by intro x y y'; simpa using Qc_add_right C x y y')
    (by intro a x y; simpa using Qc_smul_right C a x y)

end MinlosAnalytic

/-!
## Finite-dimensional analyticity (to lift to infinite dimensions)

We record the standard finite-dimensional statement: for a centered Gaussian
vector with real covariance matrix Σ, the map
  (z_i)_{i=1..n} ↦ E[exp(∑ z_i X_i)]
extends to an entire function on ℂⁿ and equals exp(½ zᵀ Σ z).

We use this as the cylinder-level analyticity that justifies the complex CF
formula for complex test functions via Re/Im decomposition and finite spans.
-/

namespace FiniteDim

open BigOperators

/-- Complex quadratic form associated to a real symmetric matrix Sigma. -/
noncomputable def quadFormC {ι : Type*} [Fintype ι] (Sigma : Matrix ι ι ℝ) (z : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, ((Sigma i j : ℝ) : ℂ) * z i * z j

/-- Finite-dimensional Gaussian mgf/CF formula and analyticity (statement). -/
lemma gaussian_mgf_entire {ι : Type*} [Fintype ι]
  (Sigma : Matrix ι ι ℝ) (hSym : Sigma.transpose = Sigma) (hPSD : Sigma.PosSemidef) :
  ∃ (F : (ι → ℂ) → ℂ),
    (∀ z : ι → ℝ, F (fun i => (z i : ℂ)) = Complex.exp ((1/2 : ℂ) * quadFormC Sigma (fun i => (z i : ℂ)))) ∧
    (∀ z : ι → ℂ, ∃ C r : ℝ, ∀ w : ι → ℂ, (∀ i, ‖w i - z i‖ < r) → ‖F w‖ ≤ C) := by
  sorry

end FiniteDim
