/-
  Plancherel_theorem_Rn.lean
  2π-normalized Fourier transform on ℝⁿ; ℏ = 1.
  This file *states* Plancherel with `sorry` proofs.
-/
import Mathlib

noncomputable section
open scoped Real
open Complex MeasureTheory

namespace PlancherelRn

/-- ℝⁿ with the standard inner product and Lebesgue measure. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Position-space L²(ℝⁿ) with complex scalars, Lebesgue measure. -/
abbrev Hx (n : ℕ) := Lp ℂ 2 (volume : Measure (Rn n))

/-- Momentum-space L²(ℝⁿ); same underlying space/measure, different role. -/
abbrev Hp (n : ℕ) := Lp ℂ 2 (volume : Measure (Rn n))

/-- 2π-normalized Fourier kernel: `exp(-2π i ⟪x, ξ⟫)`. -/
@[simp] def fourierKernel {n : ℕ} (x ξ : Rn n) : ℂ :=
  Complex.exp (-(2 * Real.pi) * Complex.I * Complex.ofReal (⟪x, ξ⟫_ℝ))

/-- Inverse 2π-normalized Fourier kernel: `exp( 2π i ⟪x, ξ⟫)`. -/
@[simp] def invFourierKernel {n : ℕ} (x ξ : Rn n) : ℂ :=
  Complex.exp ((2 * Real.pi) * Complex.I * Complex.ofReal (⟪x, ξ⟫_ℝ))

/-- Fourier integral (forward transform) on functions `f : ℝⁿ → ℂ`. -/
def fourierIntegral {n : ℕ} (f : Rn n → ℂ) : Rn n → ℂ :=
  fun ξ => ∫ x, f x * fourierKernel (x) (ξ)

/-- Inverse Fourier integral on functions `g : ℝⁿ → ℂ`. -/
def invFourierIntegral {n : ℕ} (g : Rn n → ℂ) : Rn n → ℂ :=
  fun x => ∫ ξ, g ξ * invFourierKernel (x) (ξ)

/-! ### Plancherel statements (with `sorry`) -/

/-- **Plancherel (Parseval) on `L¹ ∩ L²` (2π-normalized).**

For any `f : ℝⁿ → ℂ` with `Integrable f` and `f ∈ L²`, the Fourier integral is in `L²`
and preserves the `L²` norm.
-/
theorem plancherel_L1capL2 {n : ℕ} (f : Rn n → ℂ)
    (hfL1 : Integrable f (volume : Measure (Rn n)))
    (hfL2 : Memℒp f 2 (volume : Measure (Rn n))) :
    Memℒp (fourierIntegral (n := n) f) 2 volume
      ∧
    ∫ ξ, ‖fourierIntegral (n := n) f ξ‖^2 = ∫ x, ‖f x‖^2 := by
  -- This is the usual Plancherel identity: ‖F f‖₂ = ‖f‖₂.
  -- Proof would go via: Schwartz → L¹∩L² by density; Fourier on Schwartz isometry; extend.
  sorry

/-- **Inversion on `L¹ ∩ L²`.** For nice `f`, inverse Fourier recovers `f` a.e. -/
theorem inversion_L1capL2 {n : ℕ} (f : Rn n → ℂ)
    (hfL1 : Integrable f (volume : Measure (Rn n)))
    (hfL2 : Memℒp f 2 (volume : Measure (Rn n))) :
    (invFourierIntegral (n := n) (fourierIntegral (n := n) f)) =ᵐ[volume] f := by
  -- Usual Fourier inversion on L¹ ∩ L² under the 2π-normalization.
  sorry

/-- **Plancherel as a unitary on `L²(ℝⁿ)`.**

There exists a linear isometry equivalence `U : L²(ℝⁿ) ≃ₗᵢ L²(ℝⁿ)` such that
for every `f ∈ L¹ ∩ L²`, `U` agrees (a.e., when viewed as functions) with the
Fourier integral, and `U.symm` agrees with the inverse Fourier integral.
-/
theorem plancherel_unitary_exists (n : ℕ) :
  ∃ U : Hx n ≃ₗᵢ[ℂ] Hp n,
    (∀ (f : Rn n → ℂ)
       (hfL1 : Integrable f (volume : Measure (Rn n)))
       (hfL2 : Memℒp f 2 (volume : Measure (Rn n))),
       let fL2 : Hx n := (hfL2.toLp f)
       have hFL2 : Memℒp (fourierIntegral (n := n) f) 2 volume :=
         (plancherel_L1capL2 (n := n) f hfL1 hfL2).left
       let FL2 : Hp n := (hFL2.toLp (fourierIntegral (n := n) f))
       -- `U` sends the L²-class of `f` to the L²-class of its Fourier integral
       U fL2 = FL2
    )
    ∧
    (∀ (g : Rn n → ℂ)
       (hgL1 : Integrable g (volume : Measure (Rn n)))
       (hgL2 : Memℒp g 2 (volume : Measure (Rn n))),
       let gL2 : Hp n := (hgL2.toLp g)
       have hInvL2 : Memℒp (invFourierIntegral (n := n) g) 2 volume := by
         -- Follows from Plancherel applied to `g` (or via symmetry of the kernel)
         sorry
       let InvL2 : Hx n := (hInvL2.toLp (invFourierIntegral (n := n) g))
       -- `U.symm` sends the L²-class of `g` to the L²-class of its inverse Fourier integral
       U.symm gL2 = InvL2
    ) := by
  -- Existence and uniqueness of `U` comes from extending the isometry on a dense subspace.
  -- Uniqueness is implicit in `≃ₗᵢ` (two-sided inverse); the above equalities characterize it.
  sorry

/-- **Parseval identity via the unitary.**
(Immediate corollary of `plancherel_unitary_exists`.)
-/
theorem parseval_via_U {n : ℕ} :
  ∀ U : Hx n ≃ₗᵢ[ℂ] Hp n,  -- any Fourier–Plancherel unitary
    ∀ f g : Hx n, ⟪U f, U g⟫_ℂ = ⟪f, g⟫_ℂ := by
  -- True for the Fourier unitary, via polarization from the isometry property.
  sorry

end PlancherelRn
