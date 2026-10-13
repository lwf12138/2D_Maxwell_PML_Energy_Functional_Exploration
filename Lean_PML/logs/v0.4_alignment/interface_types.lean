import LeanPML

-- 类型复核不替代人工检查；此处展开普通结构字段，防止目标混入输入。
#print LeanPML.Rectangle.RegionalAbsorption
#print LeanPML.PML.Concrete.OriginalClassicalOn
#print LeanPML.PML.Concrete.PrimitiveClassicalOn
#print LeanPML.Rectangle.SmoothTimeJet
#print LeanPML.Rectangle.UniformTimeJet
#print LeanPML.Rectangle.WeightedJetRegular
#print LeanPML.Rectangle.SmoothStateRegular
#print LeanPML.PML.Concrete.OriginalLiftRegular
#print LeanPML.PML.Concrete.LiftIdentified
#check LeanPML.Rectangle.RegionalAbsorption.originalRegionalFiniteIntervalProblem
#check LeanPML.Rectangle.RegionalAbsorption.originalRegionalFiniteIntervalProblem_second_R_continuous
#check LeanPML.PML.Concrete.original_to_primitive_classical_rectangle
#check LeanPML.PML.Concrete.primitive_to_original_classical_rectangle
#check LeanPML.Rectangle.ParameterCertificate.unitSquare_parameter_certificate
