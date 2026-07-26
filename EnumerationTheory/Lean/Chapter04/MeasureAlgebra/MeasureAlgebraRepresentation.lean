import Chapter04.Common

noncomputable section

namespace Chapter04.MeasureAlgebraRepresentation

universe u

variable {A : MeasureAlgebraData.{u}}

theorem equiv_refl (hA : IsMeasureAlgebra A) (a : A.carrier) :
    A.equiv a a :=
  hA.1.1 a

theorem equiv_symm (hA : IsMeasureAlgebra A) {a b : A.carrier}
    (hab : A.equiv a b) : A.equiv b a :=
  hA.1.2 hab

theorem equiv_trans (hA : IsMeasureAlgebra A) {a b c : A.carrier}
    (hab : A.equiv a b) (hbc : A.equiv b c) : A.equiv a c :=
  hA.1.3 hab hbc

theorem measure_eq_of_equiv (hA : IsMeasureAlgebra A) {a b : A.carrier}
    (hab : A.equiv a b) : A.measure a = A.measure b :=
  hA.2.2.2.1 a b hab

/-- Boolean partition identity in the abstract measure algebra. -/
theorem union_inter_compl_equiv
    (hA : IsMeasureAlgebra A) (a b : A.carrier) :
    A.equiv
      (A.union (A.inter a b) (A.inter a (A.compl b))) a := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  have hdist : A.equiv
      (A.inter a (A.union b (A.compl b)))
      (A.union (A.inter a b) (A.inter a (A.compl b))) :=
    (hdistrib a b (A.compl b)).1
  have htop : A.equiv
      (A.inter a (A.union b (A.compl b))) (A.inter a A.top) :=
    (hcongr a (A.union b (A.compl b)) a A.top
      (heq.1 a) (hcomplUnion b)).2
  exact heq.3 (heq.2 hdist) (heq.3 htop (hbotId a).2)

theorem measure_union_inter_compl
    (hA : IsMeasureAlgebra A) (a b : A.carrier) :
    A.measure (A.union (A.inter a b) (A.inter a (A.compl b))) =
      A.measure a :=
  measure_eq_of_equiv hA (union_inter_compl_equiv hA a b)

/-- The two pieces in the Boolean partition are disjoint modulo the algebra
equivalence relation. -/
theorem inter_partition_pieces_equiv_bot
    (hA : IsMeasureAlgebra A) (a b : A.carrier) :
    A.equiv
      (A.inter (A.inter a b) (A.inter a (A.compl b))) A.bot := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  have h1 : A.equiv
      (A.inter (A.inter a b) (A.inter a (A.compl b)))
      (A.inter (A.inter (A.inter a b) a) (A.compl b)) :=
    heq.2 (hassoc (A.inter a b) a (A.compl b)).2
  have h2 : A.equiv
      (A.inter (A.inter (A.inter a b) a) (A.compl b))
      (A.inter (A.inter a (A.inter a b)) (A.compl b)) :=
    (hcongr (A.inter (A.inter a b) a) (A.compl b)
      (A.inter a (A.inter a b)) (A.compl b)
      (hcomm (A.inter a b) a).2 (heq.1 (A.compl b))).2
  have h3 : A.equiv
      (A.inter (A.inter a (A.inter a b)) (A.compl b))
      (A.inter (A.inter (A.inter a a) b) (A.compl b)) :=
    (hcongr (A.inter a (A.inter a b)) (A.compl b)
      (A.inter (A.inter a a) b) (A.compl b)
      (heq.2 (hassoc a a b).2) (heq.1 (A.compl b))).2
  have h4 : A.equiv
      (A.inter (A.inter (A.inter a a) b) (A.compl b))
      (A.inter (A.inter a a) (A.inter b (A.compl b))) :=
    (hassoc (A.inter a a) b (A.compl b)).2
  have h5 : A.equiv
      (A.inter (A.inter a a) (A.inter b (A.compl b)))
      (A.inter (A.inter a a) A.bot) :=
    (hcongr (A.inter a a) (A.inter b (A.compl b))
      (A.inter a a) A.bot (heq.1 (A.inter a a)) (hcomplInter b)).2
  exact heq.3 h1 (heq.3 h2 (heq.3 h3 (heq.3 h4 (heq.3 h5 (htopAbs _).1))))

theorem inter_self_equiv (hA : IsMeasureAlgebra A) (a : A.carrier) :
    A.equiv (A.inter a a) a := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  let p := A.union (A.inter a a) (A.inter a (A.compl a))
  have hp_a : A.equiv p a := union_inter_compl_equiv
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩ a a
  have hp_bot : A.equiv p (A.union (A.inter a a) A.bot) :=
    hcongr (A.inter a a) (A.inter a (A.compl a))
      (A.inter a a) A.bot (heq.1 _) (hcomplInter a) |>.1
  have hp_self : A.equiv p (A.inter a a) :=
    heq.3 hp_bot (hbotId (A.inter a a)).1
  exact heq.3 (heq.2 hp_self) hp_a

/-- Complements are unique after passing to the measure-algebra equivalence. -/
theorem complement_unique
    (hA : IsMeasureAlgebra A) (a b c : A.carrier)
    (habU : A.equiv (A.union a b) A.top)
    (habI : A.equiv (A.inter a b) A.bot)
    (hacU : A.equiv (A.union a c) A.top)
    (hacI : A.equiv (A.inter a c) A.bot) :
    A.equiv b c := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  have hbot_union (x : A.carrier) : A.equiv (A.union A.bot x) x :=
    heq.3 (hcomm A.bot x).1 (hbotId x).1
  have hbmeet : A.equiv b (A.inter b c) := by
    have h1 : A.equiv b (A.inter b A.top) := heq.2 (hbotId b).2
    have h2 : A.equiv (A.inter b A.top) (A.inter b (A.union a c)) :=
      (hcongr b A.top b (A.union a c) (heq.1 b) (heq.2 hacU)).2
    have h3 : A.equiv (A.inter b (A.union a c))
        (A.union (A.inter b a) (A.inter b c)) :=
      (hdistrib b a c).1
    have hba : A.equiv (A.inter b a) A.bot :=
      heq.3 (hcomm b a).2 habI
    have h4 : A.equiv (A.union (A.inter b a) (A.inter b c))
        (A.union A.bot (A.inter b c)) :=
      (hcongr (A.inter b a) (A.inter b c) A.bot (A.inter b c)
        hba (heq.1 _)).1
    exact heq.3 h1 (heq.3 h2 (heq.3 h3 (heq.3 h4 (hbot_union _))))
  have hcmeet : A.equiv c (A.inter c b) := by
    have h1 : A.equiv c (A.inter c A.top) := heq.2 (hbotId c).2
    have h2 : A.equiv (A.inter c A.top) (A.inter c (A.union a b)) :=
      (hcongr c A.top c (A.union a b) (heq.1 c) (heq.2 habU)).2
    have h3 : A.equiv (A.inter c (A.union a b))
        (A.union (A.inter c a) (A.inter c b)) :=
      (hdistrib c a b).1
    have hca : A.equiv (A.inter c a) A.bot :=
      heq.3 (hcomm c a).2 hacI
    have h4 : A.equiv (A.union (A.inter c a) (A.inter c b))
        (A.union A.bot (A.inter c b)) :=
      (hcongr (A.inter c a) (A.inter c b) A.bot (A.inter c b)
        hca (heq.1 _)).1
    exact heq.3 h1 (heq.3 h2 (heq.3 h3 (heq.3 h4 (hbot_union _))))
  exact heq.3 hbmeet (heq.3 (hcomm b c).2 (heq.2 hcmeet))

theorem union_self_equiv (hA : IsMeasureAlgebra A) (a : A.carrier) :
    A.equiv (A.union a a) a := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  let hA' : IsMeasureAlgebra A :=
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  have hxU : A.equiv (A.union (A.compl a) (A.union a a)) A.top := by
    have h1 : A.equiv (A.union (A.compl a) (A.union a a))
        (A.union (A.union (A.compl a) a) a) :=
      heq.2 (hassoc (A.compl a) a a).1
    have hca : A.equiv (A.union (A.compl a) a) A.top :=
      heq.3 (hcomm (A.compl a) a).1 (hcomplUnion a)
    have h2 : A.equiv (A.union (A.union (A.compl a) a) a)
        (A.union A.top a) :=
      (hcongr (A.union (A.compl a) a) a A.top a hca (heq.1 a)).1
    have h3 : A.equiv (A.union A.top a) A.top :=
      heq.3 (hcomm A.top a).1 (htopAbs a).2
    exact heq.3 h1 (heq.3 h2 h3)
  have hxI : A.equiv (A.inter (A.compl a) (A.union a a)) A.bot := by
    have h1 := (hdistrib (A.compl a) a a).1
    have hca : A.equiv (A.inter (A.compl a) a) A.bot :=
      heq.3 (hcomm (A.compl a) a).2 (hcomplInter a)
    have h2 : A.equiv
        (A.union (A.inter (A.compl a) a) (A.inter (A.compl a) a))
        (A.union A.bot A.bot) :=
      (hcongr _ _ A.bot A.bot hca hca).1
    exact heq.3 h1 (heq.3 h2 (hbotId A.bot).1)
  have haU : A.equiv (A.union (A.compl a) a) A.top :=
    heq.3 (hcomm (A.compl a) a).1 (hcomplUnion a)
  have haI : A.equiv (A.inter (A.compl a) a) A.bot :=
    heq.3 (hcomm (A.compl a) a).2 (hcomplInter a)
  exact complement_unique hA' (A.compl a) (A.union a a) a hxU hxI haU haI

theorem union_inter_absorb
    (hA : IsMeasureAlgebra A) (a b : A.carrier) :
    A.equiv (A.union a (A.inter a b)) a := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  let hA' : IsMeasureAlgebra A :=
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  let x := A.union a (A.inter a b)
  have hxU : A.equiv (A.union (A.compl a) x) A.top := by
    have h1 : A.equiv (A.union (A.compl a) x)
        (A.union x (A.compl a)) := (hcomm _ _).1
    have h2 : A.equiv (A.union x (A.compl a))
        (A.union a (A.union (A.inter a b) (A.compl a))) :=
      (hassoc a (A.inter a b) (A.compl a)).1
    have h3 : A.equiv
        (A.union a (A.union (A.inter a b) (A.compl a)))
        (A.union a (A.union (A.compl a) (A.inter a b))) :=
      (hcongr a (A.union (A.inter a b) (A.compl a)) a
        (A.union (A.compl a) (A.inter a b)) (heq.1 a)
        (hcomm (A.inter a b) (A.compl a)).1).1
    have h4 : A.equiv
        (A.union a (A.union (A.compl a) (A.inter a b)))
        (A.union (A.union a (A.compl a)) (A.inter a b)) :=
      heq.2 (hassoc a (A.compl a) (A.inter a b)).1
    have h5 : A.equiv
        (A.union (A.union a (A.compl a)) (A.inter a b))
        (A.union A.top (A.inter a b)) :=
      (hcongr _ _ A.top _ (hcomplUnion a) (heq.1 _)).1
    have h6 : A.equiv (A.union A.top (A.inter a b)) A.top :=
      heq.3 (hcomm A.top (A.inter a b)).1 (htopAbs _).2
    exact heq.3 h1 (heq.3 h2 (heq.3 h3 (heq.3 h4 (heq.3 h5 h6))))
  have hca : A.equiv (A.inter (A.compl a) a) A.bot :=
    heq.3 (hcomm (A.compl a) a).2 (hcomplInter a)
  have hcab : A.equiv (A.inter (A.compl a) (A.inter a b)) A.bot := by
    have h1 : A.equiv (A.inter (A.compl a) (A.inter a b))
        (A.inter (A.inter (A.compl a) a) b) :=
      heq.2 (hassoc (A.compl a) a b).2
    have h2 : A.equiv (A.inter (A.inter (A.compl a) a) b)
        (A.inter A.bot b) :=
      (hcongr _ b A.bot b hca (heq.1 b)).2
    have h3 : A.equiv (A.inter A.bot b) A.bot :=
      heq.3 (hcomm A.bot b).2 (htopAbs b).1
    exact heq.3 h1 (heq.3 h2 h3)
  have hxI : A.equiv (A.inter (A.compl a) x) A.bot := by
    have h1 : A.equiv (A.inter (A.compl a) x)
        (A.union (A.inter (A.compl a) a)
          (A.inter (A.compl a) (A.inter a b))) :=
      (hdistrib (A.compl a) a (A.inter a b)).1
    have h2 : A.equiv
        (A.union (A.inter (A.compl a) a)
          (A.inter (A.compl a) (A.inter a b)))
        (A.union A.bot A.bot) :=
      (hcongr _ _ A.bot A.bot hca hcab).1
    exact heq.3 h1 (heq.3 h2 (hbotId A.bot).1)
  have haU : A.equiv (A.union (A.compl a) a) A.top :=
    heq.3 (hcomm (A.compl a) a).1 (hcomplUnion a)
  have haI : A.equiv (A.inter (A.compl a) a) A.bot := hca
  exact complement_unique hA' (A.compl a) x a hxU hxI haU haI

theorem inter_union_absorb
    (hA : IsMeasureAlgebra A) (a b : A.carrier) :
    A.equiv (A.inter a (A.union a b)) a := by
  rcases hA with
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  let hA' : IsMeasureAlgebra A :=
    ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
      hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
      hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
      hmeasureFaithful, hmeasureIUnion⟩
  have h1 := (hdistrib a a b).1
  have h2 : A.equiv
      (A.union (A.inter a a) (A.inter a b))
      (A.union a (A.inter a b)) :=
    (hcongr _ _ a _ (inter_self_equiv hA' a) (heq.1 _)).1
  exact heq.3 h1 (heq.3 h2 (union_inter_absorb hA' a b))

def algebraSetoid (A : MeasureAlgebraData.{u}) (hA : IsMeasureAlgebra A) :
    Setoid A.carrier :=
  ⟨A.equiv, hA.1⟩

abbrev AlgebraQuotient (A : MeasureAlgebraData.{u})
    (hA : IsMeasureAlgebra A) := Quotient (algebraSetoid A hA)

instance quotientMax (hA : IsMeasureAlgebra A) : Max (AlgebraQuotient A hA) :=
  ⟨Quotient.map₂ A.union (fun {a₁ a₂} ha {b₁ b₂} hb =>
    (hA.2.1 a₁ b₁ a₂ b₂ ha hb).1)⟩

instance quotientMin (hA : IsMeasureAlgebra A) : Min (AlgebraQuotient A hA) :=
  ⟨Quotient.map₂ A.inter (fun {a₁ a₂} ha {b₁ b₂} hb =>
    (hA.2.1 a₁ b₁ a₂ b₂ ha hb).2)⟩

instance quotientLattice (hA : IsMeasureAlgebra A) :
    Lattice (AlgebraQuotient A hA) :=
  Lattice.mk'
    (by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro a b
      exact Quotient.sound (hA.2.2.2.2.2.2.2.2.2.1 a b).1)
    (by
      intro x y z
      refine Quotient.inductionOn₃ x y z ?_
      intro a b c
      exact Quotient.sound (hA.2.2.2.2.2.2.2.2.2.2.1 a b c).1)
    (by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro a b
      exact Quotient.sound (hA.2.2.2.2.2.2.2.2.2.1 a b).2)
    (by
      intro x y z
      refine Quotient.inductionOn₃ x y z ?_
      intro a b c
      exact Quotient.sound (hA.2.2.2.2.2.2.2.2.2.2.1 a b c).2)
    (by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro a b
      exact Quotient.sound (union_inter_absorb hA a b))
    (by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro a b
      exact Quotient.sound (inter_union_absorb hA a b))

instance quotientDistribLattice (hA : IsMeasureAlgebra A) :
    DistribLattice (AlgebraQuotient A hA) :=
  DistribLattice.mk (by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    apply le_of_eq
    rcases hA with
      ⟨heq, hcongr, hcomplCongr, hmeasureCongr, hbotId, htopAbs,
        hcomplUnion, hcomplInter, hinvol, hcomm, hassoc, hdistrib,
        hiUnionUpper, hiUnionLeast, hmeasureBot, hmeasureNonneg,
        hmeasureFaithful, hmeasureIUnion⟩
    exact Quotient.sound (heq.2 (hdistrib a b c).2))

instance quotientOrderTop (hA : IsMeasureAlgebra A) :
    OrderTop (AlgebraQuotient A hA) where
  top := Quotient.mk _ A.top
  le_top := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk _ (A.union a A.top) = Quotient.mk _ A.top
    exact Quotient.sound (hA.2.2.2.2.2.1 a).2

instance quotientOrderBot (hA : IsMeasureAlgebra A) :
    OrderBot (AlgebraQuotient A hA) where
  bot := Quotient.mk _ A.bot
  bot_le := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk _ (A.union A.bot a) = Quotient.mk _ a
    exact Quotient.sound (equiv_trans hA
      (hA.2.2.2.2.2.2.2.2.2.1 A.bot a).1
      (hA.2.2.2.2.1 a).1)

instance quotientBoundedOrder (hA : IsMeasureAlgebra A) :
    BoundedOrder (AlgebraQuotient A hA) := BoundedOrder.mk

instance quotientComplementedLattice (hA : IsMeasureAlgebra A) :
    ComplementedLattice (AlgebraQuotient A hA) where
  exists_isCompl := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    refine ⟨Quotient.mk _ (A.compl a), IsCompl.mk ?_ ?_⟩
    · rw [disjoint_iff_inf_le]
      apply le_of_eq
      exact Quotient.sound (hA.2.2.2.2.2.2.2.1 a)
    · rw [codisjoint_iff_le_sup]
      apply le_of_eq
      exact (Quotient.sound (hA.2.2.2.2.2.2.1 a)).symm

noncomputable instance quotientBooleanAlgebra (hA : IsMeasureAlgebra A) :
    BooleanAlgebra (AlgebraQuotient A hA) :=
  DistribLattice.booleanAlgebraOfComplemented _

theorem quotientCompl_mk (hA : IsMeasureAlgebra A) (a : A.carrier) :
    (Quotient.mk _ (A.compl a) : AlgebraQuotient A hA) =
      (Quotient.mk _ a)ᶜ := by
  rw [← Quotient.out_eq ((Quotient.mk _ a : AlgebraQuotient A hA)ᶜ)]
  apply Quotient.sound
  apply complement_unique hA a (A.compl a)
    (Quotient.out ((Quotient.mk _ a : AlgebraQuotient A hA)ᶜ))
  · exact hA.2.2.2.2.2.2.1 a
  · exact hA.2.2.2.2.2.2.2.1 a
  · have hU : (Quotient.mk _
        (A.union a (Quotient.out ((Quotient.mk _ a : AlgebraQuotient A hA)ᶜ))) :
          AlgebraQuotient A hA) = Quotient.mk _ A.top := by
      change (Quotient.mk _ a : AlgebraQuotient A hA) ⊔
          Quotient.mk _ (Quotient.out ((Quotient.mk _ a : AlgebraQuotient A hA)ᶜ)) = ⊤
      rw [Quotient.out_eq]
      exact sup_compl_eq_top
    exact Quotient.exact hU
  · have hI : (Quotient.mk _
        (A.inter a (Quotient.out ((Quotient.mk _ a : AlgebraQuotient A hA)ᶜ))) :
          AlgebraQuotient A hA) = Quotient.mk _ A.bot := by
      change (Quotient.mk _ a : AlgebraQuotient A hA) ⊓
          Quotient.mk _ (Quotient.out ((Quotient.mk _ a : AlgebraQuotient A hA)ᶜ)) = ⊥
      rw [Quotient.out_eq]
      exact inf_compl_eq_bot
    exact Quotient.exact hI

def quotientMeasure (hA : IsMeasureAlgebra A) :
    AlgebraQuotient A hA → ℝ :=
  Quotient.lift A.measure (fun _ _ hab => measure_eq_of_equiv hA hab)

@[simp] theorem quotientMeasure_mk (hA : IsMeasureAlgebra A) (a : A.carrier) :
    quotientMeasure hA (Quotient.mk _ a) = A.measure a := rfl

theorem quotientMeasure_nonneg (hA : IsMeasureAlgebra A)
    (q : AlgebraQuotient A hA) : 0 ≤ quotientMeasure hA q := by
  refine Quotient.inductionOn q ?_
  intro a
  rcases hA with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmeasureNonneg, _, _⟩
  exact hmeasureNonneg a

@[simp] theorem quotientMeasure_bot (hA : IsMeasureAlgebra A) :
    quotientMeasure hA (⊥ : AlgebraQuotient A hA) = 0 := by
  rcases hA with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmeasureBot, _, _, _⟩
  exact hmeasureBot

theorem quotientMeasure_top (hA : IsMeasureAlgebra A)
    (htop : A.measure A.top = 1) :
    quotientMeasure hA (⊤ : AlgebraQuotient A hA) = 1 := htop

noncomputable def quotientIUnion (hA : IsMeasureAlgebra A)
    (f : ℕ → AlgebraQuotient A hA) : AlgebraQuotient A hA :=
  Quotient.mk _ (A.iUnion fun n => Quotient.out (f n))

theorem le_quotientIUnion (hA : IsMeasureAlgebra A)
    (f : ℕ → AlgebraQuotient A hA) (n : ℕ) :
    f n ≤ quotientIUnion hA f := by
  rw [← inf_eq_left]
  rw [← Quotient.out_eq (f n)]
  exact Quotient.sound (hA.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun k => Quotient.out (f k)) n)

theorem quotientIUnion_le (hA : IsMeasureAlgebra A)
    (f : ℕ → AlgebraQuotient A hA) (b : AlgebraQuotient A hA)
    (hb : ∀ n, f n ≤ b) : quotientIUnion hA f ≤ b := by
  rw [← inf_eq_left]
  rw [← Quotient.out_eq b]
  apply Quotient.sound
  apply hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro n
  have hn := hb n
  rw [← inf_eq_left] at hn
  rw [← Quotient.out_eq (f n), ← Quotient.out_eq b] at hn
  exact Quotient.exact hn

theorem quotientIUnion_mk (hA : IsMeasureAlgebra A) (f : ℕ → A.carrier) :
    quotientIUnion hA (fun n => Quotient.mk _ (f n)) =
      Quotient.mk _ (A.iUnion f) := by
  apply le_antisymm
  · apply quotientIUnion_le
    intro n
    rw [← inf_eq_left]
    exact Quotient.sound
      (hA.2.2.2.2.2.2.2.2.2.2.2.2.1 f n)
  · rw [← inf_eq_left]
    rw [← Quotient.out_eq (quotientIUnion hA (fun n => Quotient.mk _ (f n)))]
    apply Quotient.sound
    apply hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    intro n
    have hn := le_quotientIUnion hA
      (fun k => Quotient.mk (algebraSetoid A hA) (f k)) n
    rw [← inf_eq_left, ← Quotient.out_eq
      (quotientIUnion hA (fun k => Quotient.mk _ (f k)))] at hn
    exact Quotient.exact hn

theorem quotientMeasure_eq_zero (hA : IsMeasureAlgebra A)
    (q : AlgebraQuotient A hA) :
    quotientMeasure hA q = 0 ↔ q = ⊥ := by
  refine Quotient.inductionOn q ?_
  intro a
  have hA' := hA
  rcases hA' with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfaithful, _⟩
  change A.measure a = 0 ↔ (Quotient.mk _ a : AlgebraQuotient A hA) = ⊥
  rw [hfaithful]
  constructor
  · intro ha
    change (Quotient.mk _ a : AlgebraQuotient A hA) = Quotient.mk _ A.bot
    exact Quotient.sound ha
  · intro ha
    change (Quotient.mk _ a : AlgebraQuotient A hA) = Quotient.mk _ A.bot at ha
    exact Quotient.exact ha

theorem quotientMeasure_iUnion (hA : IsMeasureAlgebra A)
    (f : ℕ → AlgebraQuotient A hA)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    quotientMeasure hA (quotientIUnion hA f) =
      ∑' n, quotientMeasure hA (f n) := by
  have hA' := hA
  rcases hA' with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcountable⟩
  rw [show quotientMeasure hA (quotientIUnion hA f) =
      A.measure (A.iUnion fun n => Quotient.out (f n)) by rfl]
  rw [hcountable]
  · congr 1
    funext n
    calc
      A.measure (Quotient.out (f n)) =
          quotientMeasure hA (Quotient.mk _ (Quotient.out (f n))) := rfl
      _ = quotientMeasure hA (f n) :=
        congrArg (quotientMeasure hA) (Quotient.out_eq (f n))
  · intro i j hij
    have hd := hdisjoint i j hij
    rw [disjoint_iff_inf_le] at hd
    have heq : f i ⊓ f j = ⊥ := le_antisymm hd bot_le
    rw [← Quotient.out_eq (f i), ← Quotient.out_eq (f j)] at heq
    exact Quotient.exact heq

theorem summable_quotientMeasure_iUnion (hA : IsMeasureAlgebra A)
    (f : ℕ → AlgebraQuotient A hA)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    Summable (fun n => quotientMeasure hA (f n)) := by
  by_cases hsum : Summable (fun n => quotientMeasure hA (f n))
  · exact hsum
  · have htsum : ∑' n, quotientMeasure hA (f n) = 0 :=
      tsum_eq_zero_of_not_summable hsum
    have hzero : quotientIUnion hA f = ⊥ := by
      apply (quotientMeasure_eq_zero hA _).1
      rw [quotientMeasure_iUnion hA f hdisjoint, htsum]
    have hfzero : ∀ n, f n = ⊥ := by
      intro n
      apply le_antisymm
      · rw [← hzero]
        exact le_quotientIUnion hA f n
      · exact bot_le
    simp [hfzero]

theorem quotientMeasure_sup_of_disjoint (hA : IsMeasureAlgebra A)
    (q r : AlgebraQuotient A hA) (hqr : Disjoint q r) :
    quotientMeasure hA (q ⊔ r) =
      quotientMeasure hA q + quotientMeasure hA r := by
  let f : ℕ → AlgebraQuotient A hA := fun n =>
    if n = 0 then q else if n = 1 then r else ⊥
  have hf0 : f 0 = q := by simp [f]
  have hf1 : f 1 = r := by simp [f]
  have hfge : ∀ n, 2 ≤ n → f n = ⊥ := by
    intro n hn
    simp [f, Nat.ne_of_gt (by omega : 0 < n), Nat.ne_of_gt (by omega : 1 < n)]
  have hfdis : ∀ i j, i ≠ j → Disjoint (f i) (f j) := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      by_cases hj1 : j = 1
      · subst j
        simpa [hf0, hf1] using hqr
      · have hj2 : 2 ≤ j := by omega
        rw [hf0, hfge j hj2]
        exact disjoint_bot_right
    · by_cases hi1 : i = 1
      · subst i
        by_cases hj0 : j = 0
        · subst j
          simpa [hf0, hf1] using hqr.symm
        · have hj2 : 2 ≤ j := by omega
          rw [hf1, hfge j hj2]
          exact disjoint_bot_right
      · have hi2 : 2 ≤ i := by omega
        rw [hfge i hi2]
        exact disjoint_bot_left
  have hsup : quotientIUnion hA f = q ⊔ r := by
    apply le_antisymm
    · apply quotientIUnion_le
      intro n
      by_cases hn0 : n = 0
      · subst n
        rw [hf0]
        exact le_sup_left
      · by_cases hn1 : n = 1
        · subst n
          rw [hf1]
          exact le_sup_right
        · have hn2 : 2 ≤ n := by omega
          rw [hfge n hn2]
          exact bot_le
    · exact sup_le
        (hf0 ▸ le_quotientIUnion hA f 0)
        (hf1 ▸ le_quotientIUnion hA f 1)
  rw [← hsup, quotientMeasure_iUnion hA f hfdis]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [hf0, hf1]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    have hn2 : 2 ≤ n := by omega
    rw [hfge n hn2, quotientMeasure_bot]

end Chapter04.MeasureAlgebraRepresentation
