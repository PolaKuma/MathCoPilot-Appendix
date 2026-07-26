import Chapter09.Section02

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section03

universe u

/-- Source: Theorem 9.3.1, Chapter 9, Section 3. -/
theorem vanDerCorputLemma :
    VdCStatement := by
  sorry

/-- Source: Theorem 9.3.2, Chapter 9, Section 3. -/
theorem furstenbergWeakMixingMultipleErgodicAverages
    (M : MeasurableSystem.{u}) (k : ℕ) :
    Chapter02.IsWeakMixing M -> 1 ≤ k -> WeakMixingMultipleAverageStatement M k := by
  sorry

end Section03
end Chapter09
