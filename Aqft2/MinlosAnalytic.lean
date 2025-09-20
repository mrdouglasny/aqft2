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

import Aqft2.Basic
import Aqft2.Minlos

open Classical
open TopologicalSpace MeasureTheory Complex

noncomputable section

namespace MinlosAnalytic

/-- A real symmetric, positive semidefinite covariance form on real test functions. -/
structure CovarianceForm where
  Q : TestFunction → TestFunction → ℝ
  symm : ∀ f g, Q f g = Q g f
  psd  : ∀ f, 0 ≤ Q f f
  cont_diag : Continuous fun f => Q f f

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
  -- Placeholder: follows directly from C.symm by case analysis on Fin 2
  sorry

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
