import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

variable {d : ℕ} [NeZero d] [Fintype (Fin d)]

-- Check what is needed for fourierTransformCLE
#check @SchwartzMap.fourierTransformCLE

-- Check if EuclideanSpace already has complex module structure somewhere
#synth NormedSpace ℂ (EuclideanSpace ℝ (Fin d))