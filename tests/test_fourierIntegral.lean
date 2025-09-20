/-
Test file to explore fourierIntegral from Mathlib
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Complex Real

noncomputable section

-- Check the type of fourierIntegral
#check fourierIntegral

-- Check if there's a Plancherel theorem
#check_failure Plancherel
#check_failure plancherel

-- Let's see what's available in the Fourier namespace
open Fourier in
#check_failure Plancherel

-- Check available theorems about fourierIntegral
#check fourierIntegral_comp_linearIsometry

-- See what we can find about L² and Fourier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

-- Check if we can apply fourierIntegral to L² functions
example (f : E → ℂ) : E → ℂ := fourierIntegral f

end
