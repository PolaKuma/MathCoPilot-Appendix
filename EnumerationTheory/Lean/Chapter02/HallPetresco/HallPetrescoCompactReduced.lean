import Chapter02.HallPetresco.HallPetrescoCompactQuotient
import Chapter02.HallPetresco.HallPetrescoReducedQuotient

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoCompactReduced

open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoReducedQuotient

universe u v

/-- A genuine quotient presentation supplies compactness of the reduced
Hall--Petresco nilmanifold.  The full Hall--Petresco quotient is compact by
the Hall normal form and the compact fundamental domain; compactness then
descends along the canonical continuous surjection to the reduced quotient. -/
noncomputable def reducedQuotientCompactSpaceOfPresentation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    CompactSpace (ReducedQuotient N P.lattice) := by
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  exact reducedQuotientCompactSpace N P.lattice

end Chapter02.HallPetrescoCompactReduced
