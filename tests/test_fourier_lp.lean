/-
Test file to understand the Fourier and L² tools in Mathlib
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Distribution.SchwartzSpace

open MeasureTheory Complex Real

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

-- Check type of fourierIntegral again
#check fourierIntegral

-- Look for isometry properties
#check_failure Real.fourierIntegral_isometry
#check_failure fourier_isometry

-- Check SchwartzMap for Fourier transforms on test functions
#check SchwartzMap.fourierTransformCLM

-- Try to find L² related Fourier material
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

-- See if we can construct something on L²
#check Lp ℂ 2 (volume : Measure V)

end
