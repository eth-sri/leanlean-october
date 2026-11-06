import RequestProject.CylinderPoset
import RequestProject.ConeAdjPoset



namespace FiniteChains.Comb

instance cylP_partialOrder {X S} [PartialOrder X] [PartialOrder S]
    (a : S →o X) : PartialOrder (CylP a) :=
  { (inferInstance : Preorder (CylP a)) with
    le_antisymm := by
      intro p q hpq hqp
      cases p <;> cases q
      · exact congrArg Sum.inl (le_antisymm hpq hqp)
      · exact hpq.elim
      · exact hqp.elim
      · exact congrArg Sum.inr (le_antisymm hpq hqp) }

instance coneAdj_partialOrder {P T} [PartialOrder P] (S : T → P → Prop) :
    PartialOrder (ConeAdj S) :=
  { (inferInstance : Preorder (ConeAdj S)) with
    le_antisymm := by
      intro p q hpq hqp
      cases p <;> cases q
      · exact congrArg Sum.inl (le_antisymm hpq hqp)
      · exact hqp.elim
      · exact hpq.elim
      · exact congrArg Sum.inr hpq }
