/-
Test file to understand IsIsometry and LinearIsometryEquiv construction
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Complex Real

noncomputable section

-- Check what's available for IsIsometry
#check IsIsometry
#check_failure LinearIsometry.IsIsometry
#check_failure ContinuousLinearMap.IsIsometry

-- Check LinearIsometryEquiv construction methods
#check LinearIsometryEquiv.mk
#check_failure LinearIsometryEquiv.ofSurjectiveIsometry
#check_failure LinearIsometryEquiv.ofBijective

-- Check what methods exist for making LinearIsometryEquiv
open LinearIsometryEquiv in
#print LinearIsometryEquiv

end
