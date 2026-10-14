import LeanPML.Analysis.OperatorMemory
import LeanPML.PML.WeakPathAssembly
open MeasureTheory LeanPML.Analysis LeanPML.PML
variable {α : Type*} [MeasurableSpace α] (ν : Measure α) (C : SpatialAbsorption α)
#synth NormedAddCommGroup (WeightedL2 ν C.wx)
#synth NormedSpace ℝ (WeightedL2 ν C.wx)
#synth NormedRing (WeightedL2 ν C.wx →L[ℝ] WeightedL2 ν C.wx)
#synth IsTopologicalRing (WeightedL2 ν C.wx →L[ℝ] WeightedL2 ν C.wx)
