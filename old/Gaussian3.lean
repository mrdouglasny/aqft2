import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Density
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Aqft2.SCV

open MeasureTheory Matrix Complex MvPolynomial

noncomputable section

universe u
variable {k : Type u} [Fintype k] [DecidableEq k]

/-- The PDF of a multivariate normal distribution -/
def multivariateNormalPDF
    (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef) : (k → ℝ) → ℝ :=
  fun x =>
    have h_is_unit_det : IsUnit C.det := by
      simpa using ne_of_gt (Matrix.PosDef.det_pos hC)
    letI := invertibleOfIsUnitDet C h_is_unit_det
    let d := Fintype.card k
    let diff := x - m
    let quadForm := dotProduct diff (C⁻¹ *ᵥ diff)
    (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ * Real.exp (-1 / 2 * quadForm)

/-- The multivariate normal distribution as a probability measure -/
def multivariateNormal
    (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef) : Measure (k → ℝ) :=
  volume.withDensity (fun vec => ENNReal.ofReal (multivariateNormalPDF m C hC vec))

/-- Complex extension of the multivariate Gaussian -/
def multivariateComplexGaussian
    (m : k → ℂ) (C : Matrix k k ℂ) (hC_invertible : IsUnit C.det) : (k → ℂ) → ℂ :=
  fun x =>
    letI := invertibleOfIsUnitDet C hC_invertible
    let diff := x - m
    let quadForm := dotProduct diff (C⁻¹ *ᵥ diff)
    Complex.exp (-1 / 2 * quadForm)

/-- The moment generating function of a multivariate Gaussian -/
def multivariateGaussianMGF
    (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef) : (k → ℂ) → ℂ :=
  fun t =>
    let m_complex : k → ℂ := fun i => (m i : ℂ)
    let C_complex : Matrix k k ℂ := C.map (fun x => (x : ℂ))
    let quadForm := dotProduct t (C_complex *ᵥ t)
    let linearForm := dotProduct t m_complex
    Complex.exp (linearForm + 1 / 2 * quadForm)

/-- Analyticity building blocks for quadratic forms -/

lemma analyticOn_coord_proj {k : Type*} [Fintype k] (i : k) :
  AnalyticOn ℂ (fun t : k → ℂ => t i) Set.univ := by
  let proj : (k → ℂ) →L[ℂ] ℂ := {
    toFun := fun t => t i
    map_add' := fun x y => by simp [Pi.add_apply]
    map_smul' := fun c x => by simp [Pi.smul_apply]
  }
  exact ContinuousLinearMap.analyticOn proj Set.univ

lemma analyticOn_const_complex {k : Type*} [Fintype k] (c : ℂ) :
  AnalyticOn ℂ (fun _ : k → ℂ => c) Set.univ := by
  exact analyticOn_const

lemma analyticOn_product {k : Type*} [Fintype k] {f g : (k → ℂ) → ℂ} {s : Set (k → ℂ)}
  (hf : AnalyticOn ℂ f s) (hg : AnalyticOn ℂ g s) :
  AnalyticOn ℂ (fun t => f t * g t) s := by
  exact AnalyticOn.mul hf hg

lemma analyticOn_monomial {k : Type*} [Fintype k] (i j : k) :
  AnalyticOn ℂ (fun t : k → ℂ => t i * t j) Set.univ := by
  apply analyticOn_product
  · exact analyticOn_coord_proj i
  · exact analyticOn_coord_proj j

lemma analyticOn_quadratic_term {k : Type*} [Fintype k] (C : Matrix k k ℂ) (i j : k) :
  AnalyticOn ℂ (fun t : k → ℂ => (C i j) * t i * t j) Set.univ := by
  have h_rearrange : (fun t : k → ℂ => (C i j) * t i * t j) =
                     (fun t => (C i j) * (t i * t j)) := by
    funext t
    ring
  rw [h_rearrange]
  apply analyticOn_product
  · exact analyticOn_const_complex (C i j)
  · exact analyticOn_monomial i j

lemma analyticOn_finsum {k : Type*} [Fintype k] {α : Type*} [Fintype α]
  {f : α → (k → ℂ) → ℂ} {s : Set (k → ℂ)}
  (h : ∀ a, AnalyticOn ℂ (f a) s) :
  AnalyticOn ℂ (fun t => ∑ a, f a t) s := by
  have h_eq : (fun t => ∑ a, f a t) = (∑ a, f a) := by
    funext t
    simp [Finset.sum_apply]
  rw [h_eq]
  exact Finset.analyticOn_sum Finset.univ (fun a _ => h a)

lemma analyticOn_inner_sum {k : Type*} [Fintype k] (C : Matrix k k ℂ) (i : k) :
  AnalyticOn ℂ (fun t : k → ℂ => ∑ j, (C i j) * t i * t j) Set.univ := by
  apply analyticOn_finsum
  intro j
  exact analyticOn_quadratic_term C i j

lemma analyticOn_quadratic_form {k : Type*} [Fintype k] (C : Matrix k k ℂ) :
  AnalyticOn ℂ (fun t : k → ℂ => ∑ i, ∑ j, (C i j) * t i * t j) Set.univ := by
  apply analyticOn_finsum
  intro i
  exact analyticOn_inner_sum C i

/-- The quadratic form t ⬝ᵥ (C *ᵥ t) is analytic -/
theorem quadratic_form_analytic {k : Type*} [Fintype k] (C : Matrix k k ℂ) :
  AnalyticOn ℂ (fun t : k → ℂ => t ⬝ᵥ (C *ᵥ t)) Set.univ := by
  have h_eq : (fun t : k → ℂ => t ⬝ᵥ (C *ᵥ t)) =
              (fun t => ∑ i, ∑ j, (C i j) * t i * t j) := by
    funext t
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [h_eq]
  exact analyticOn_quadratic_form C

/-- Analyticity theorems -/

theorem multivariateComplexGaussian_analytic_in_each_variable
    (m : k → ℂ) (C : Matrix k k ℂ) (hC : IsUnit C.det) :
    ∀ (j : k), AnalyticOn ℂ (fun z : ℂ =>
      let x : k → ℂ := Function.update (fun _ => 0) j z
      multivariateComplexGaussian m C hC x) Set.univ := by
  intro j
  unfold multivariateComplexGaussian
  letI := invertibleOfIsUnitDet C hC
  sorry

theorem multivariateComplexGaussian_entire
    (m : k → ℂ) (C : Matrix k k ℂ) (hC : IsUnit C.det) :
    AnalyticOn ℂ (multivariateComplexGaussian m C hC) Set.univ := by
  unfold multivariateComplexGaussian
  letI := invertibleOfIsUnitDet C hC
  sorry

theorem multivariateGaussianMGF_entire
    (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef) :
    AnalyticOn ℂ (multivariateGaussianMGF m C hC) Set.univ := by
  sorry

/-- The key theorem: MGF is entire in complex linear combinations -/
theorem multivariateGaussianMGF_complex_combinations_entire
    (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef)
    (n : ℕ) (f : Fin n → (k → ℂ)) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      multivariateGaussianMGF m C hC (∑ i, z i • f i)) Set.univ := by
  unfold multivariateGaussianMGF
  apply AnalyticOn.cexp
  apply AnalyticOn.add

  · -- Linear part is analytic
    let a : Fin n → ℂ := fun i => f i ⬝ᵥ (fun j => (m j : ℂ))
    have h_rewrite : (fun z => (∑ i, z i • f i) ⬝ᵥ (fun j => (m j : ℂ))) =
                     (fun z => z ⬝ᵥ a) := by
      funext z
      simp only [a, dotProduct]
      calc ∑ x, (∑ i, z i • f i) x * ↑(m x)
        = ∑ x, (∑ i, z i * f i x) * ↑(m x) := by simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      _ = ∑ x, ∑ i, z i * f i x * ↑(m x) := by simp only [Finset.sum_mul]
      _ = ∑ i, ∑ x, z i * f i x * ↑(m x) := by rw [Finset.sum_comm]
      _ = ∑ i, z i * ∑ x, f i x * ↑(m x) := by
        congr 1; ext i; simp only [← Finset.mul_sum, mul_assoc]
      _ = ∑ x, z x * ∑ x_1, f x x_1 * ↑(m x_1) := rfl
    rw [h_rewrite]
    have h_as_linear : (fun z => z ⬝ᵥ a) = fun z => ∑ i, a i * z i := by
      funext z; simp only [dotProduct, mul_comm]
    rw [h_as_linear]
    have h_linear_analytic : AnalyticOn ℂ (fun z : Fin n → ℂ => ∑ i, a i * z i) Set.univ := by
      let f_linear : (Fin n → ℂ) →L[ℂ] ℂ := {
        toFun := fun z => ∑ i, a i * z i,
        map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          change ∑ i, a i * (c * x i) = c * ∑ i, a i * x i
          rw [Finset.mul_sum]; congr 1; ext i; ring
      }
      exact ContinuousLinearMap.analyticOn f_linear Set.univ
    exact h_linear_analytic

  · -- Quadratic part is analytic
    apply AnalyticOn.mul
    · exact analyticOn_const
    · let g : (Fin n → ℂ) → (k → ℂ) := fun z => ∑ i, z i • f i
      let h : (k → ℂ) → ℂ := fun t => t ⬝ᵥ ((C.map (fun x => (x : ℂ))) *ᵥ t)
      have h_g_analytic : AnalyticOn ℂ g Set.univ := by
        let g_linear : (Fin n → ℂ) →L[ℂ] (k → ℂ) := {
          toFun := g,
          map_add' := fun x y => by
            simp only [g, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          map_smul' := fun c x => by
            simp only [g, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]
        }
        exact ContinuousLinearMap.analyticOn g_linear Set.univ
      have h_h_analytic : AnalyticOn ℂ h Set.univ := by
        exact quadratic_form_analytic (C.map (fun x => (x : ℂ)))
      have h_composition : (fun z => (∑ i, z i • f i) ⬝ᵥ ((C.map (fun x => (x : ℂ))) *ᵥ ∑ i, z i • f i)) = h ∘ g := by
        rfl
      rw [h_composition]
      exact AnalyticOn.comp h_h_analytic h_g_analytic (Set.mapsTo_univ g Set.univ)

theorem gaussian_satisfies_OS0_pattern
    (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef)
    (n : ℕ) (J : Fin n → (k → ℂ)) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      multivariateGaussianMGF m C hC (∑ i, z i • J i)) Set.univ :=
  multivariateGaussianMGF_complex_combinations_entire m C hC n J

example (m : k → ℝ) (C : Matrix k k ℝ) (hC : C.PosDef) (n : ℕ) (J : Fin n → (k → ℂ)) :
  ∃ f : (Fin n → ℂ) → ℂ, AnalyticOn ℂ f Set.univ ∧
    f = (fun z => multivariateGaussianMGF m C hC (∑ i, z i • J i)) := by
  use (fun z => multivariateGaussianMGF m C hC (∑ i, z i • J i))
  constructor
  · exact gaussian_satisfies_OS0_pattern m C hC n J
  · rfl

/-- Example: Quadratic form as ContinuousMultilinearMap -/
example (C : Matrix k k ℝ) :
  ∃ (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => k → ℂ) ℂ),
    (fun t : k → ℂ => t ⬝ᵥ ((C.map (fun x => (x : ℂ))) *ᵥ t)) =
    (fun t => B fun i => t) := by
  sorry

end
