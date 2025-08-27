import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace

#check Complex.re
#check Complex.im
#check Complex.reCLM
#check Complex.imCLM
#check SchwartzMap.compCLM

open Complex SchwartzMap

-- Test if we can access re and im as continuous linear maps
#check @reCLM
#check @imCLM

-- Alternative: check if we can create them
variable (f : ℂ →L[ℝ] ℝ)
#check f
