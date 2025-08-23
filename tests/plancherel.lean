/-
  Fourier_L2_from_Schwartz.lean
  Build the L²(ℝⁿ) Fourier unitary from the Schwartz-level equivalence.
  Normalization: 2π; ℏ = 1.
-/
import Mathlib/Analysis/Distribution/SchwartzSpace
import Mathlib/Analysis/Distribution/FourierSchwartz
import Mathlib/Analysis/Fourier/FourierTransform
import Mathlib/MeasureTheory/Function/LpSpace

noncomputable section
open Complex MeasureTheory

/-- ℝⁿ with its Euclidean structure. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Schwartz functions `ℝⁿ → ℂ`. -/
abbrev S (n : ℕ) := SchwartzMap (Rn n) ℂ

/-- Position & momentum Hilbert spaces: `L²(ℝⁿ, dx)` (same underlying measure). -/
abbrev Hx (n : ℕ) := Lp ℂ 2 (volume : Measure (Rn n))
abbrev Hp (n : ℕ) := Lp ℂ 2 (volume : Measure (Rn n))

/-- Fourier on Schwartz as a bundled continuous linear equivalence (mathlib). -/
def FT_S (n : ℕ) : S n ≃L[ℂ] S n :=
  SchwartzMap.fourierTransformCLE ℂ

/-- Embed Schwartz into `L²` (p = 2) as a continuous linear map. -/
def toL2_pos (n : ℕ) : S n →L[ℂ] Hx n :=
  (SchwartzMap.toLpCLM (μ := (volume : Measure (Rn n))) (p := (2 : ℝ≥0∞)))

/-- Same embedding but target is the “momentum” copy (same measure). -/
def toL2_mom (n : ℕ) : S n →L[ℂ] Hp n :=
  (SchwartzMap.toLpCLM (μ := (volume : Measure (Rn n))) (p := (2 : ℝ≥0∞)))

/-! ### Dense range & injectivity of the Schwartz embedding into `L²`.

These are standard analysis facts (continuous functions zero a.e. are zero; Schwartz ⊆ L¹∩L² and is dense in L²).
We assume them here; provide proofs later or import lemmas once available in mathlib.
-/

/-- Injectivity: if a Schwartz function is zero a.e., then it is zero (hence the embedding is injective). -/
lemma toL2_pos_injective {n : ℕ} :
  Function.Injective (toL2_pos n) := by
  -- Sketch: `toL2_pos f = 0` means `f = 0` a.e.; since `f` is continuous, this forces `f = 0`.
  -- Fill with the lemma that continuous a.e.-zero implies zero (nontrivial open set has positive measure).
  sorry

/-- Density: the range of the Schwartz embedding is dense in `L²`. -/
lemma denseRange_toL2_pos {n : ℕ} :
  DenseRange (toL2_pos n) := by
  -- Sketch: `C_c^∞` is dense in L² for `1 ≤ p < ∞`; `C_c^∞ ⊆ Schwartz`.
  -- Use the existing density of smooth compact support or a direct Schwartz density lemma.
  sorry

/-- Abbreviation: the dense subspace `Kx = range (toL2_pos n) ⊆ Hx`. -/
abbrev Kx (n : ℕ) : Submodule ℂ (Hx n) := (toL2_pos n).range

/-- The subtype inclusion `Kx ↪ Hx` has dense range. -/
lemma denseRange_subtype_Kx {n : ℕ} :
  DenseRange (Subtype.val : Kx n → Hx n) := by
  -- Immediate from `denseRange_toL2_pos` and `range_comp_subtype`.
  sorry

/-! ### Define the isometry on the dense subspace `Kx`.

We set `T_K (toL2_pos f) := toL2_mom (FT_S f)` and show it is well-defined & isometric.
-/

/-- Plancherel-on-Schwartz (2π-normalization): `‖ℱ f‖_{L²} = ‖f‖_{L²}`. -/
lemma plancherel_on_Schwartz {n : ℕ} (f : S n) :
  ‖(toL2_mom n) ((FT_S n) f)‖ = ‖(toL2_pos n) f‖ := by
  -- This is the crucial L² identity on the Schwartz core; prove via standard Plancherel on Schwartz.
  -- (When available in mathlib, replace this `sorry` by the corresponding lemma.)
  sorry

/-- Well-definedness on the range: if `toL2_pos f₁ = toL2_pos f₂`, then
    `toL2_mom (FT_S f₁) = toL2_mom (FT_S f₂)` in `L²`. -/
lemma FT_welldefined_on_range {n : ℕ} {f g : S n}
    (h : (toL2_pos n) f = (toL2_pos n) g) :
    (toL2_mom n) ((FT_S n) f) = (toL2_mom n) ((FT_S n) g) := by
  -- Using injectivity of `toL2_pos` on Schwartz, the a.e.-equality forces `f = g`,
  -- hence equality after applying Fourier + embedding.
  -- Alternatively: combine `h` with `plancherel_on_Schwartz` and norm-0 ⇒ equality in `Lp`.
  sorry

/-- The Fourier map on the dense subspace `Kx` as a *linear isometry*. -/
def FT_on_Kx (n : ℕ) : Kx n →ₗᵢ[ℂ] Hp n :=
by
  -- Each `ψ : Kx` has form `ψ = toL2_pos f`. Define `T ψ := toL2_mom (FT_S f)`.
  -- We must show well-definedness, linearity, and isometry; all reduce to the lemmas above.
  classical
  -- Define T using representatives:
  refine
    { toLinearMap :=
        { toFun := fun ψ =>
            let f : S n := Classical.choose ψ.property
            have hf : (toL2_pos n) f = ψ := Classical.choose_spec ψ.property
            (toL2_mom n) ((FT_S n) f)
          map_add' := ?add
          map_smul' := ?smul },
      isometry_toFun := ?isom } <;> ext ψ <;> try rename_i x y a
  all_goals
    -- fill `?add`, `?smul`, and `?isom` using `FT_welldefined_on_range`, linearity of `FT_S`, and `plancherel_on_Schwartz`.
    -- The representative choice compatibilities require exactly `FT_welldefined_on_range`.
  sorry

/-! ### Extend uniquely to all of `L²` via `LinearIsometry.extend`. -/

/-- The extended linear isometry `U : L² → L²` (position → momentum). -/
def U_L2 (n : ℕ) : Hx n →ₗᵢ[ℂ] Hp n :=
  (FT_on_Kx n).extend (denseRange_subtype_Kx (n := n))

/-- The inverse map on the dense subspace, using the inverse Fourier on Schwartz. -/
def FTinv_on_Kx (n : ℕ) : (LinearMap.range (toL2_mom n)) →ₗᵢ[ℂ] Hx n :=
by
  -- Same construction but with `(FT_S n).symm`.
  classical
  -- analogous to `FT_on_Kx`:
  sorry

/-- Dense range of the momentum-side subtype. -/
lemma denseRange_subtype_Kp {n : ℕ} :
  DenseRange (Subtype.val : (LinearMap.range (toL2_mom n)) → Hp n) := by
  -- same argument as `denseRange_subtype_Kx`
  sorry

/-- The extended inverse `U_L2_symm : L² → L²` (momentum → position). -/
def U_L2_symm (n : ℕ) : Hp n →ₗᵢ[ℂ] Hx n :=
  (FTinv_on_Kx n).extend (denseRange_subtype_Kp (n := n))

/-- The two extensions are inverses (by uniqueness of extension and agreement on the dense cores). -/
lemma U_L2_left_right_inverse {n : ℕ} :
  (U_L2 n).toContinuousLinearMap.comp (U_L2_symm n).toContinuousLinearMap
    = ContinuousLinearMap.id ℂ (Hp n)
  ∧
  (U_L2_symm n).toContinuousLinearMap.comp (U_L2 n).toContinuousLinearMap
    = ContinuousLinearMap.id ℂ (Hx n) := by
  -- Prove equality on the dense subspaces, then use continuity + density to conclude.
  -- (There is a `LinearIsometry.extend_unique`-style lemma you can emulate.)
  sorry

/-- **Fourier–Plancherel unitary on `L²(ℝⁿ)`**, built from the Schwartz layer. -/
def FourierL2_unitary (n : ℕ) : Hx n ≃ₗᵢ[ℂ] Hp n :=
by
  classical
  refine
    { toLinearIsometry := U_L2 n
      inv := U_L2_symm n
      left_inv := ?linv
      right_inv := ?rinv } <;> funext ψ <;> -- use the `left_right_inverse` lemma
  all_goals
    -- turn the `ContinuousLinearMap` equalities into pointwise inverses
    -- (or use `ext`-on-`DenseRange` + continuity).
    sorry

/-- On Schwartz representatives, `FourierL2_unitary` agrees with the integral Fourier. -/
@[simp] lemma FourierL2_unitary_on_Schwartz {n : ℕ} (f : S n) :
  FourierL2_unitary n ((toL2_pos n) f) = (toL2_mom n) ((FT_S n) f) := by
  -- By construction of `U_L2` as the extension of `FT_on_Kx`.
  sorry

/-- And the inverse agrees with the inverse Fourier on Schwartz. -/
@[simp] lemma FourierL2_unitary_symm_on_Schwartz {n : ℕ} (g : S n) :
  (FourierL2_unitary n).symm ((toL2_mom n) g) = (toL2_pos n) ((FT_S n).symm g) := by
  sorry
