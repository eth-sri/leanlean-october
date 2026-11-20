module

public import RequestProject.OrderConstructionPartialOrder
public import RequestProject.OrderNerveContiguousHomotopy
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-! An actual homotopy equivalence from the realization of a poset mapping
cylinder to its base when the outer poset has height at most one. Collapsing
outer edge vertices first and outer zero vertices second gives two genuine
contiguous homotopies; pointwise order comparison is not mistaken for
cross-comparability. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory
open scoped unitInterval Topology Classical

theorem orderNerveRealizationMap_congr {P Q : Type} [PartialOrder P] [PartialOrder Q]
    {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (he : f = g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf x = orderNerveRealizationMap g hg x := by
  simp_all

variable {X S : Type} [PartialOrder X] [PartialOrder S]
  (a : S →o X) (d : S → ℕ) (hd : StrictMono d) (hd₁ : ∀ s, d s ≤ 1)

variable {s t : S}

include hd hd₁ in
theorem rankOne_maximal (hs : d s = 1) (h : s ≤ t) : s = t := by
  by_contra hne
  have hh := hd (lt_of_le_of_ne h hne)
  grind

include hd in
theorem rankOne_minimal (ht : d t = 0) (h : s ≤ t) : s = t := by
  by_contra hne
  have hh := hd (lt_of_le_of_ne h hne)
  omega

def cylinderHalfCollapse : CylP a → CylP a
  | .inl x => .inl x
  | .inr s => if d s = 1 then .inl (a s) else .inr s

include hd hd₁ in
theorem cylinderHalfCollapse_monotone : Monotone (cylinderHalfCollapse a d) := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · exact hpq.elim
  · change a s ≤ y at hpq
    change CylP.le a _ _
    by_cases hs : d s = 1 <;> simpa only [cylinderHalfCollapse, hs, ↓reduceIte, CylP.le] using hpq
  · change s ≤ t at hpq
    by_cases hs : d s = 1
    · grind [rankOne_maximal]
    · by_cases ht : d t = 1
      · change ((if d s = 1 then Sum.inl _ else Sum.inr s) : CylP a) ≤
          (if d t = 1 then Sum.inl _ else Sum.inr t)
        rw [if_neg hs, if_pos ht]
        exact a.monotone hpq
      · change CylP.le a _ _
        simp_all [cylinderHalfCollapse, if_neg, CylP.le]

include hd hd₁ in
theorem cylinderHalfCollapse_cross :
    ∀ p q : CylP a, p ≤ q ∨ q ≤ p →
      p ≤ cylinderHalfCollapse a d q ∨ cylinderHalfCollapse a d q ≤ p := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · by_cases ht : d t = 1
    · rw [cylinderHalfCollapse, if_pos ht]
      rcases hpq with h | h
      · exact h.elim
      · exact Or.inr h
    · simp_all [cylinderHalfCollapse, CylP.le, if_neg]
  · exact hpq
  · by_cases ht : d t = 1
    · rw [cylinderHalfCollapse, if_pos ht]
      rcases hpq with h | h
      · exact Or.inl (a.monotone h)
      · have he := rankOne_maximal d hd hd₁ ht h
        subst s
        exact Or.inl (le_refl (a t))
    · simp_all [cylinderHalfCollapse, CylP.le, if_neg]

include hd hd₁ in
theorem cylinderCollapse_half_cross :
    ∀ p q : CylP a, p ≤ q ∨ q ≤ p →
      cylinderHalfCollapse a d p ≤ cylCollapse a q ∨
        cylCollapse a q ≤ cylinderHalfCollapse a d p := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · rcases hpq with h | h
    · exact h.elim
    · exact Or.inr h
  · rcases hpq with h | h
    · by_cases hs : d s = 1
      · change CylP.le a _ _ ∨
          CylP.le a _ _
        simpa only [cylinderHalfCollapse, if_pos hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq, CylP.le] using
          (Or.inl h : a s ≤ y ∨ y ≤ a s)
      · simp_all [cylinderHalfCollapse, CylP.le, if_neg, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq]
    · exact h.elim
  · by_cases hs : d s = 1
    · simp only [cylinderHalfCollapse, CylP.le, if_pos hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq]
      exact hpq.elim (fun h => Or.inl (a.monotone h)) (fun h => Or.inr (a.monotone h))
    · apply Or.inl
      change ((if d s = 1 then Sum.inl _ else Sum.inr s) : CylP a) ≤ Sum.inl _
      rw [if_neg hs]
      rcases hpq with h | h
      · exact a.monotone h
      · have he := rankOne_minimal d hd (by have := hd₁ s; omega) h
        subst t
        exact le_rfl

def cylinderRealizationInclusion :
    C(orderNerveRealization X, orderNerveRealization (CylP a)) :=
  ⟨orderNerveRealizationMap _ (cylIn_monotone a),
    (orderNerveRealizationMap _ (cylIn_monotone a)).hom.continuous⟩

def cylinderRealizationRetraction :
    C(orderNerveRealization (CylP a), orderNerveRealization X) :=
  ⟨orderNerveRealizationMap _ (cylRetr_monotone a),
    (orderNerveRealizationMap _ (cylRetr_monotone a)).hom.continuous⟩

theorem cylinderRealization_section :
    (cylinderRealizationRetraction a).comp (cylinderRealizationInclusion a) =
      ContinuousMap.id (orderNerveRealization X) := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap _ (cylRetr_monotone a)
    (orderNerveRealizationMap (cylIn a) (cylIn_monotone a) x) = x
  rw [orderNerveRealizationMap_comp]
  solve_by_elim [orderNerveRealizationMap_congr, orderNerveRealizationMap_id]

def rankOneCylinderRealizationDeformation : ContinuousMap.Homotopy
    (ContinuousMap.id (orderNerveRealization (CylP a)))
    ((cylinderRealizationInclusion a).comp (cylinderRealizationRetraction a)) := by
  let H₀ := orderNerveRealizationContiguousHomotopy id monotone_id
    _ (cylinderHalfCollapse_monotone a d hd hd₁)
    (cylinderHalfCollapse_cross a d hd hd₁)
  let H₁ := orderNerveRealizationContiguousHomotopy
    _ (cylinderHalfCollapse_monotone a d hd hd₁)
    _ (cylCollapse_monotone a) (cylinderCollapse_half_cross a d hd hd₁)
  have hzero :
      (⟨orderNerveRealizationMap id monotone_id,
        (orderNerveRealizationMap id monotone_id).hom.continuous⟩ :
          C(orderNerveRealization (CylP a), orderNerveRealization (CylP a))) =
        ContinuousMap.id _ := by
    apply ContinuousMap.ext
    apply orderNerveRealizationMap_id
  have hone :
      (⟨orderNerveRealizationMap _ (cylCollapse_monotone a),
        (orderNerveRealizationMap _ (cylCollapse_monotone a)).hom.continuous⟩) =
      (cylinderRealizationInclusion a).comp (cylinderRealizationRetraction a) := by
    apply ContinuousMap.ext
    intro x
    exact (orderNerveRealizationMap_comp _ _
      _ (cylIn_monotone a) x).symm
  exact (hzero ▸ hone ▸ H₀.trans H₁)

def rankOneCylinderRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (CylP a)) (orderNerveRealization X) where
  toFun := cylinderRealizationRetraction a
  invFun := cylinderRealizationInclusion a
  left_inv := ⟨(rankOneCylinderRealizationDeformation a d hd hd₁).symm⟩
  right_inv := by rw [cylinderRealization_section]

end FiniteChains.Comb
