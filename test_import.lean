import Aqft2.OS_Axioms

open MeasureTheory SCV QFT

#check OS0_Analyticity

def test_usage (dμ : ProbabilityMeasure FieldSpace) : Prop := OS0_Analyticity dμ
