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

/-- Real and complex test function aliases from Aqft2.Basic. -/
abbrev TestFunction := SchwartzMap SpaceTime ℝ
abbrev TestFunctionℂ := SchwartzMap SpaceTime ℂ

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
  -- Placeholder: follows from symmetry of Q and the definition of Qc
  sorry

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
  -- Placeholder: 2D centered Gaussian mgf with vector (i, -1)
  sorry

/-- Main formula: complex characteristic functional equals Zc on complex tests. -/
 theorem gaussian_CF_complex
  (C : CovarianceForm)
  (μ : ProbabilityMeasure FieldConfiguration)
  (h_realCF : ∀ f : TestFunction,
     ∫ ω, Complex.exp (Complex.I * (ω f)) ∂μ.toMeasure
       = Complex.exp (-(1/2 : ℂ) * (C.Q f f)))
  : ∀ f : TestFunctionℂ,
     ∫ ω, Complex.exp (Complex.I * (pairingC ω f)) ∂μ.toMeasure = Zc C f := by
  -- Placeholder: reduce to 2D mgf using re/im decomposition
  intro f;
  sorry

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

/-- Two-dimensional explicit formula (used in the complex CF proof). -/
lemma gaussian_mgf_entire_2d :
  ∃ (F : ℂ × ℂ → ℂ),
    (∀ u v : ℝ, ∀ sigma11 sigma22 sigma12 : ℝ,
      F ((u : ℂ), (v : ℂ)) = Complex.exp ((1/2 : ℂ) * (sigma11 * u^2 + 2 * sigma12 * u * v + sigma22 * v^2))) ∧
    (∀ z w : ℂ, ∃ C r : ℝ, ‖F (z, w)‖ ≤ C) := by
  sorry

end FiniteDim
