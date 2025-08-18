import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory

-- Key findings:

-- 1. BilinForm is defined as LinearMap.BilinMap R M R
#check LinearMap.BilinForm ℂ
-- This is: M →L[ℂ] M →L[ℂ] ℂ  (bilinear form)

-- 2. Inner product on L2 is sesquilinear (conjugate-linear in first argument)
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

-- 3. We can construct bilinear forms on Lp spaces:
#check LinearMap.BilinForm ℂ (Lp ℂ 2 μ)
-- This is: Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ →L[ℂ] ℂ  (bilinear)

-- 4. The type we use in MVGaussianAbstract.lean:
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
#check E →L[ℂ] E →L[ℂ] ℂ
-- This is exactly LinearMap.BilinForm ℂ E

-- 5. So we can define a bilinear form that agrees with inner product for appropriate cases
variable (B : LinearMap.BilinForm ℂ (Lp ℂ 2 μ))
-- This would be: (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) →L[ℂ] ℂ

-- For real test functions f, we might have: B f g = ⟪f, g⟫_ℂ
-- But for complex linear combinations: B (z • f) g = z * B f g (linear, not conjugate-linear)

-- 6. Check if Lp spaces have inner product structure with the right import
section LpInner
variable [Fact (1 ≤ (2 : ℝ≥0∞))]
#check InnerProductSpace ℂ (Lp ℂ 2 μ)
