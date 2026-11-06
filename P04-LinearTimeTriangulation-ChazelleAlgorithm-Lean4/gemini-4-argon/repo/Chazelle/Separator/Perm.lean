module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Logic.Relation

/-!
# Permutation and equivalence-class toolkit (planar separators, part 0)

Pure combinatorics used by the combinatorial-map development of `Chazelle.Separator`:

* orbit transfer between two permutations (`sameCycle_follow`, `sameCycle_of_step`): if a
  permutation `ψ` follows `π` along a `π`-orbit segment, the endpoints are in the same `ψ`-cycle;
* invariance (`eq_of_sameCycle`): a function constant along `π` is constant on `π`-cycles;
* closed sets (`mem_of_sameCycle`);
* merging two cycles with a transposition (`sameCycle_mul_swap_iff`);
* the first-return permutation of `π` on a subtype (`firstReturn`), whose cycles are the traces
  of the `π`-cycles (`sameCycle_firstReturn_iff`);
* equivalence closures: adding one pair to a relation (`eqvGen_or_pair_iff`), counting the classes
  `Nat.card (Quot R)` (`card_quot_le_or_pair_add_one`, `card_quot_or_pair_eq`,
  `card_quot_bot`, `card_quot_le_one`, `card_quot_eq_of_eqvGen_iff`), closed sets
  (`mem_of_eqvGen`), and localisation of a closure to a class (`eqvGen_of_class`).
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Relation

section PermLemmas

variable {X Y Z : Type*}


/-- **Stepwise transfer.**  If each point `ι x` is in the same `ψ`-cycle as `ι (π x)`, then
`π`-cycles map into `ψ`-cycles. -/
theorem sameCycle_of_step [Finite X] (π : Perm X) (ψ : Perm Y) (ι : X → Y)
    (h : ∀ x, ψ.SameCycle (ι x) (ι (π x))) {x y : X} (hxy : π.SameCycle x y) :
    ψ.SameCycle (ι x) (ι y) := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction k with
  | zero => simpa using Perm.SameCycle.refl ψ (ι x)
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact ih.trans (h _)


/-- A set closed under `π` is closed under `π.SameCycle`. -/
theorem mem_of_sameCycle [Finite X] (π : Perm X) (S : Set X) (hS : ∀ x ∈ S, π x ∈ S)
    {x y : X} (h : π.SameCycle x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact hS _ ih

/-- A set closed under `π` is closed under `π⁻¹` (finite case). -/
theorem mem_of_inv_mem [Finite X] (π : Perm X) (S : Set X) (hS : ∀ x ∈ S, π x ∈ S)
    {x : X} (hx : x ∈ S) : π⁻¹ x ∈ S :=
  mem_of_sameCycle π S hS ⟨-1, by simp⟩ hx

end PermLemmas

section Merge

variable {X : Type*} [Finite X] [DecidableEq X]


end Merge

section EqvGenLemmas

variable {X : Type*}

/-- The equivalence closure of `R` with one extra pair `(u, w)`. -/
theorem eqvGen_or_pair_iff (R : X → X → Prop) (u w x y : X) :
    EqvGen (fun a b => R a b ∨ (a = u ∧ b = w)) x y ↔
      EqvGen R x y ∨ (EqvGen R x u ∧ EqvGen R w y) ∨ (EqvGen R x w ∧ EqvGen R u y) := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      rcases hab with hab | ⟨rfl, rfl⟩
      · exact Or.inl (EqvGen.rel _ _ hab)
      · exact Or.inr (Or.inl ⟨EqvGen.refl _, EqvGen.refl _⟩)
    | refl a => exact Or.inl (EqvGen.refl _)
    | symm a b _ ih =>
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (EqvGen.symm _ _ h)
      · exact Or.inr (Or.inr ⟨EqvGen.symm _ _ h2, EqvGen.symm _ _ h1⟩)
      · exact Or.inr (Or.inl ⟨EqvGen.symm _ _ h2, EqvGen.symm _ _ h1⟩)
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ih2 with k | ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact Or.inl (EqvGen.trans _ _ _ h k)
      · exact Or.inr (Or.inl ⟨EqvGen.trans _ _ _ h k1, k2⟩)
      · exact Or.inr (Or.inr ⟨EqvGen.trans _ _ _ h k1, k2⟩)
      · exact Or.inr (Or.inl ⟨h1, EqvGen.trans _ _ _ h2 k⟩)
      · exact Or.inl (EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _
          (EqvGen.symm _ _ (EqvGen.trans _ _ _ h2 k1)) k2))
      · exact Or.inl (EqvGen.trans _ _ _ h1 k2)
      · exact Or.inr (Or.inr ⟨h1, EqvGen.trans _ _ _ h2 k⟩)
      · exact Or.inl (EqvGen.trans _ _ _ h1 k2)
      · exact Or.inl (EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _
          (EqvGen.symm _ _ (EqvGen.trans _ _ _ h2 k1)) k2))
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact EqvGen.mono (fun a b hab => Or.inl hab) _ _ h
    · have hm := fun a b (h : EqvGen R a b) =>
        EqvGen.mono (r := R) (p := fun a b => R a b ∨ (a = u ∧ b = w))
          (fun a b hab => Or.inl hab) a b h
      exact EqvGen.trans _ _ _ (hm _ _ h1)
        (EqvGen.trans _ _ _ (EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)) (hm _ _ h2))
    · have hm := fun a b (h : EqvGen R a b) =>
        EqvGen.mono (r := R) (p := fun a b => R a b ∨ (a = u ∧ b = w))
          (fun a b hab => Or.inl hab) a b h
      exact EqvGen.trans _ _ _ (hm _ _ h1)
        (EqvGen.trans _ _ _ (EqvGen.symm _ _ (EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩))) (hm _ _ h2))

/-- Two relations with the same equivalence closure. -/
theorem eqvGen_iff_of_le (R R' : X → X → Prop) (h1 : ∀ a b, R a b → EqvGen R' a b)
    (h2 : ∀ a b, R' a b → EqvGen R a b) {x y : X} : EqvGen R x y ↔ EqvGen R' x y := by
  have key : ∀ (S S' : X → X → Prop), (∀ a b, S a b → EqvGen S' a b) →
      ∀ x y, EqvGen S x y → EqvGen S' x y := by
    intro S S' h x y hxy
    induction hxy with
    | rel a b hab => exact h a b hab
    | refl a => exact EqvGen.refl _
    | symm a b _ ih => exact EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2
  exact ⟨key R R' h1 x y, key R' R h2 x y⟩

/-- Classes of the empty relation: `Quot` by an empty relation has the cardinality of the type. -/
theorem card_quot_bot (R : X → X → Prop) (hR : ∀ a b, ¬ R a b) :
    Nat.card (Quot R) = Nat.card X := by
  symm
  refine Nat.card_eq_of_bijective (Quot.mk R) ⟨fun a b hab => ?_, Quot.mk_surjective⟩
  have h := Quot.eqvGen_exact hab
  clear hab
  induction h with
  | rel a b hab => exact absurd hab (hR a b)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- Adding one pair to a relation merges at most two classes: the number of classes drops by
at most one. -/
theorem card_quot_le_or_pair_add_one [Finite X] (R : X → X → Prop) (u w : X) :
    Nat.card (Quot R) ≤ Nat.card (Quot (fun a b => R a b ∨ (a = u ∧ b = w))) + 1 := by
  classical
  set R' : X → X → Prop := fun a b => R a b ∨ (a = u ∧ b = w)
  let g : Quot R → Quot R' := Quot.lift (Quot.mk R') (fun a b h => Quot.sound (Or.inl h))
  let G : Quot R → Option (Quot R') := fun q => if q = Quot.mk R w then none else some (g q)
  have hG : Function.Injective G := by
    intro q q' hqq
    induction q using Quot.ind with
    | mk a =>
    induction q' using Quot.ind with
    | mk b =>
    by_cases ha : Quot.mk R a = Quot.mk R w <;> by_cases hb : Quot.mk R b = Quot.mk R w
    · rw [ha, hb]
    · simp [G, ha, hb] at hqq
    · simp [G, ha, hb] at hqq
    · simp only [G, ha, hb, ite_false, Option.some.injEq] at hqq
      have h := Quot.eqvGen_exact hqq
      rw [eqvGen_or_pair_iff] at h
      rcases h with h | ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Quot.eqvGen_sound h
      · exact absurd (Quot.eqvGen_sound (EqvGen.symm _ _ h2)) hb
      · exact absurd (Quot.eqvGen_sound h1) ha
  have := Nat.card_le_card_of_injective G hG
  rwa [Finite.card_option] at this

/-- Adding a pair that is already related does not change the classes. -/
theorem card_quot_or_pair_eq [Finite X] (R : X → X → Prop) (u w : X) (huw : EqvGen R u w) :
    Nat.card (Quot (fun a b => R a b ∨ (a = u ∧ b = w))) = Nat.card (Quot R) := by
  set R' : X → X → Prop := fun a b => R a b ∨ (a = u ∧ b = w)
  let g : Quot R → Quot R' := Quot.lift (Quot.mk R') (fun a b h => Quot.sound (Or.inl h))
  symm
  refine Nat.card_eq_of_bijective g ⟨fun q q' hqq => ?_, ?_⟩
  · induction q using Quot.ind with
    | mk a =>
    induction q' using Quot.ind with
    | mk b =>
    have h := Quot.eqvGen_exact hqq
    rw [eqvGen_or_pair_iff] at h
    apply Quot.eqvGen_sound
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _ huw h2)
    · exact EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _ (EqvGen.symm _ _ huw) h2)
  · intro q
    induction q using Quot.ind with
    | mk a => exact ⟨Quot.mk R a, rfl⟩

/-- **Localisation.**  Inside a class of `EqvGen R` all of whose outgoing `R`-edges are
`R'`-edges, `EqvGen R` implies `EqvGen R'`. -/
theorem eqvGen_of_class (R R' : X → X → Prop) (a : X)
    (h : ∀ x y, EqvGen R a x → R x y → R' x y) {x y : X} (hx : EqvGen R a x)
    (hxy : EqvGen R x y) : EqvGen R' x y := by
  induction hxy with
  | rel x y hr => exact EqvGen.rel _ _ (h x y hx hr)
  | refl x => exact EqvGen.refl _
  | symm x y hyx ih =>
    exact EqvGen.symm _ _ (ih (EqvGen.trans _ _ _ hx (EqvGen.symm _ _ hyx)))
  | trans x z y hxz _ ih1 ih2 =>
    exact EqvGen.trans _ _ _ (ih1 hx) (ih2 (EqvGen.trans _ _ _ hx hxz))

/-- Relations with the same equivalence closure have the same number of classes. -/
theorem card_quot_eq_of_eqvGen_iff (R R' : X → X → Prop)
    (h : ∀ x y, EqvGen R x y ↔ EqvGen R' x y) : Nat.card (Quot R) = Nat.card (Quot R') := by
  let g : Quot R → Quot R' := Quot.lift (Quot.mk R')
    (fun a b hab => Quot.eqvGen_sound ((h a b).mp (EqvGen.rel _ _ hab)))
  refine Nat.card_eq_of_bijective g ⟨fun q q' hqq => ?_, fun q => ?_⟩
  · induction q using Quot.ind with
    | mk a =>
    induction q' using Quot.ind with
    | mk b => exact Quot.eqvGen_sound ((h a b).mpr (Quot.eqvGen_exact hqq))
  · induction q using Quot.ind with
    | mk a => exact ⟨Quot.mk R a, rfl⟩

/-- A set closed under a relation in both directions is closed under its equivalence closure. -/
theorem mem_of_eqvGen (R : X → X → Prop) (U : Set X) (h1 : ∀ x y, R x y → x ∈ U → y ∈ U)
    (h2 : ∀ x y, R x y → y ∈ U → x ∈ U) {x y : X} (hxy : EqvGen R x y) (hx : x ∈ U) : y ∈ U := by
  have key : ∀ x y, EqvGen R x y → (x ∈ U ↔ y ∈ U) := by
    intro x y hxy
    induction hxy with
    | rel a b hab => exact ⟨h1 a b hab, h2 a b hab⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key x y hxy).mp hx

/-- A relation all of whose elements are related has at most one class. -/
theorem card_quot_le_one [Finite X] (R : X → X → Prop) (h : ∀ x y, EqvGen R x y) :
    Nat.card (Quot R) ≤ 1 := by
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun q q' => ?_⟩
  induction q using Quot.ind with
  | mk a =>
  induction q' using Quot.ind with
  | mk b => exact Quot.eqvGen_sound (h a b)

end EqvGenLemmas

end

end Chazelle.Separator
