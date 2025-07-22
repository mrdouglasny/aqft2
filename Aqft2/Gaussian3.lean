import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Density

open MeasureTheory Matrix

noncomputable section

-- We work over a finite-dimensional space indexed by `k`
universe u
variable {k : Type u} [Fintype k] [DecidableEq k]

/--
The probability density function (PDF) of a multivariate normal distribution.

The PDF is given by:
f(x) = (1 / sqrt((2π)^d * det(C))) * exp(-1/2 * (x - m)ᵀ * C⁻¹ * (x - m))
-/
def multivariateNormalPDF
    (m : k → ℝ) -- Mean vector
    (C : Matrix k k ℝ) -- Covariance matrix
    (hC : C.PosDef) : -- Proof that the covariance matrix is positive-definite
    (k → ℝ) → ℝ :=
  fun x =>
    have h_is_unit_det : IsUnit C.det := by
      simpa using ne_of_gt (Matrix.PosDef.det_pos hC)
    letI := invertibleOfIsUnitDet C h_is_unit_det
    let d := Fintype.card k
    let diff := x - m
    let quadForm := dotProduct diff (C⁻¹ *ᵥ diff)
    (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ * Real.exp (-1 / 2 * quadForm)

/--
The multivariate normal distribution as a probability measure.

This measure is defined by its density (`multivariateNormalPDF`) with respect
to the Lebesgue measure (`volume`) on the space of vectors `k → ℝ`.
-/
def multivariateNormal
    (m : k → ℝ) -- Mean vector
    (C : Matrix k k ℝ) -- Covariance matrix
    (hC : C.PosDef) : -- Proof of positive-definiteness
    Measure (k → ℝ) :=
  volume.withDensity (fun vec => ENNReal.ofReal (multivariateNormalPDF m C hC vec))

end
