import Mathlib

#check MeasureTheory.IsSetSemiring
#check MeasureTheory.IsSetRing
#check MeasurableSpace.generateFrom
#check MeasureTheory.Measure
#check MeasureTheory.ProbabilityMeasure
#check MeasureTheory.IsProbabilityMeasure
#check MeasureTheory.Measure.restrict
#check MeasureTheory.Measure.map
#check MeasureTheory.Measure.prod
#check MeasureTheory.MemLp
#check MeasureTheory.Lp
#check MeasureTheory.condExp
#check ContinuousMap
#check TopologicalSpace.generateFrom
#check Homeomorph
#check IsConnected
#check IsPreconnected
#check IsTotallyDisconnected
#check IsClopen
#check MeasureTheory.Measure.IsHaarMeasure
#check @inner
#check MeasureTheory.volume
#check MeasureTheory.Measure.haar
#check MeasureTheory.Measure.addHaar
#check MeasureTheory.Measure.IsAddHaarMeasure
#check MeasurableEquiv
#check MeasureTheory.MeasurePreserving
#check dense_iff_closure_eq
#check Function.Semiconj
#check EReal
#check MeasureTheory.SignedMeasure
#check MeasureTheory.SimpleFunc
#check MeasureTheory.Integrable
#check MeasureTheory.eLpNorm
#check borel
#check MeasurableSpace.comap
#check MeasurableSpace.map
#check IsCompact
#check Metric.diam
#check MeasureTheory.Measure.withDensity
#check MeasureTheory.Measure.restrict
#check MeasureTheory.volume
#check MeasureTheory.Measure.restrict_apply

structure TestProbabilitySpace where
  X : Type
  measurableSpace : MeasurableSpace X
  measure : @MeasureTheory.Measure X measurableSpace
  isProbability : @MeasureTheory.IsProbabilityMeasure X measurableSpace measure

attribute [instance] TestProbabilitySpace.measurableSpace TestProbabilitySpace.isProbability

#check fun (P : TestProbabilitySpace) => P.measure Set.univ
#check MeasurableSpace.CountablyGenerated
#check TopologicalSpace.SeparableSpace
#check cantorSet
#check TopologicalSpace.MetrizableSpace
#check TopologicalSpace.PseudoMetrizableSpace
#synth TopologicalSpace C(ℝ, ℝ)
#check TopologicalSpace.coinduced
#check Quotient.mk'
#check IsOpenMap
#check TopologicalSpace.induced
#synth TopologicalSpace (ℕ → ℝ)
#check UniformSpace.ofFun
#check MetricSpace.ofT0PseudoMetricSpace
#check EReal.toENNReal
#check EReal.toReal
#check MeasureTheory.Measure.dirac
#check MeasureTheory.Measure.count
#check MeasureTheory.Measure.AbsolutelyContinuous
#check MeasureTheory.Measure.MutuallySingular
#check ENNReal.log
#check ENNReal.rpow
#check ENNReal.ofReal
#check ContinuousMonoidHom
#check MonoidHom
#check AddCircle
#check Circle
#check MeasureTheory.Measure.IsHaarMeasure
