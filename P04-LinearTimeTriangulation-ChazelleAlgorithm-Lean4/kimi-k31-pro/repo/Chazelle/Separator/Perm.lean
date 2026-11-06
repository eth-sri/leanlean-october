module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Logic.Relation
public import Chazelle.Rwx

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

/-- **Following an orbit.**  Let `P` be a region and `t` a target in the `π`-cycle of `z ∈ P`.
If, at every point `y ∈ P` other than `t`, the permutation `ψ` acts (through `ι`) like `π` and
`π y` stays in `P`, then `ι z` and `ι t` lie in the same `ψ`-cycle. -/
theorem sameCycle_follow [Finite X] (π : Perm X) (ψ : Perm Y) (ι : X → Y) (P : X → Prop)
    {z t : X} (hz : P z) (hzt : π.SameCycle z t)
    (h : ∀ y, P y → y ≠ t → ψ (ι y) = ι (π y) ∧ P (π y)) : ψ.SameCycle (ι z) (ι t) := by
  classical
  have hex  := hzt.exists_nat_pow_eq
  have hmin : ∀ j < Nat.find hex, (π ^ j) z ≠ t := fun j hj => Nat.find_min hex hj
  have key : ∀ j ≤ Nat.find hex, P ((π ^ j) z) ∧ (ψ ^ j) (ι z) = ι ((π ^ j) z) := by
    intro j
    induction j with
    | zero => intro _; simp [hz]
    | succ j ih =>
      intro hj
      obtain ⟨hP, hψ⟩ := ih (by omega)
      obtain ⟨h1, h2⟩ := h _ hP (hmin j (by omega))
      refine ⟨?_, ?_⟩
      · rwx [pow_succ', Perm.mul_apply]
      · rw [pow_succ', Perm.mul_apply, hψ, h1, pow_succ', Perm.mul_apply]
  refine ⟨(Nat.find hex : ℤ), ?_⟩
  rw [zpow_natCast, (key _ le_rfl).2, Nat.find_spec hex]

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

/-- A function invariant under `π` is constant on `π`-cycles. -/
theorem eq_of_sameCycle [Finite X] (π : Perm X) (f : X → Z) (hf : ∀ x, f (π x) = f x)
    {x y : X} (h : π.SameCycle x y) : f x = f y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, hf, ih]

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

/-- **Merging two cycles.**  If `a` and `b` lie in different cycles of `π`, the cycles of
`π * swap a b` are those of `π`, except that the cycles of `a` and `b` are merged. -/
theorem sameCycle_mul_swap_iff (π : Perm X) {a b : X} (hab : ¬ π.SameCycle a b) (x y : X) :
    (π * swap a b).SameCycle x y ↔ π.SameCycle x y ∨
      ((π.SameCycle x a ∨ π.SameCycle x b) ∧ (π.SameCycle y a ∨ π.SameCycle y b)) := by
  set ψ := π * swap a b with hψ
  have hne : a ≠ b := fun h => hab (h ▸ Perm.SameCycle.refl π a)
  have hψa : ψ a = π b := by simp [hψ]
  have hψb : ψ b = π a := by simp [hψ]
  have hψz : ∀ z, z ≠ a → z ≠ b → ψ z = π z := by
    intro z h1 h2; simp [hψ, swap_apply_of_ne_of_ne h1 h2]
  set U : X → Prop := fun z => π.SameCycle z a ∨ π.SameCycle z b
  -- `U` is `ψ`-invariant
  have hU : ∀ z, U z → U (ψ z) := by
    intro z hz
    by_cases h1 : z = a
    · subst h1; rw [hψa]; exact Or.inr (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _))
    · by_cases h2 : z = b
      · subst h2; rw [hψb]; exact Or.inl (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _))
      · rw [hψz z h1 h2]
        rcases hz with hz | hz
        · exact Or.inl (Perm.sameCycle_apply_left.mpr hz)
        · exact Or.inr (Perm.sameCycle_apply_left.mpr hz)
  have hUc : ∀ z, ¬ U z → ¬ U (ψ z) ∧ ψ z = π z := by
    intro z hz
    have h1 : z ≠ a := fun h => hz (Or.inl (h ▸ Perm.SameCycle.refl _ _))
    have h2 : z ≠ b := fun h => hz (Or.inr (h ▸ Perm.SameCycle.refl _ _))
    rw [hψz z h1 h2]
    refine ⟨fun h => hz ?_, rfl⟩
    rcases h with h | h
    · exact Or.inl (Perm.sameCycle_apply_left.mp h)
    · exact Or.inr (Perm.sameCycle_apply_left.mp h)
  -- all of `U` is one `ψ`-cycle
  have hcycA : ∀ z, π.SameCycle z a → ψ.SameCycle z a := by
    intro z hz
    refine sameCycle_follow π ψ id (fun w => π.SameCycle w a) hz hz ?_
    intro w hw hwa
    have hwb : w ≠ b := fun h => hab (h ▸ hw).symm
    exact ⟨hψz w hwa hwb, Perm.sameCycle_apply_left.mpr hw⟩
  have hcycB : ∀ z, π.SameCycle z b → ψ.SameCycle z b := by
    intro z hz
    refine sameCycle_follow π ψ id (fun w => π.SameCycle w b) hz hz ?_
    intro w hw hwb
    have hwa : w ≠ a := fun h => hab (h ▸ hw)
    exact ⟨hψz w hwa hwb, Perm.sameCycle_apply_left.mpr hw⟩
  have hAB : ψ.SameCycle a b := by
    have : ψ.SameCycle (π b) b := hcycB _ (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _))
    rw [← hψa] at this
    exact (Perm.sameCycle_apply_left.mp this)
  have hUall : ∀ z, U z → ψ.SameCycle z a := by
    intro z hz
    rcases hz with hz | hz
    · exact hcycA z hz
    · exact (hcycB z hz).trans hAB.symm
  constructor
  · intro h
    by_cases hx : U x
    · have hy : U y := mem_of_sameCycle ψ {z | U z} hU h hx
      exact Or.inr ⟨hx, hy⟩
    · left
      obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
      clear h
      have key : ∀ k, ¬ U ((ψ ^ k) x) ∧ (ψ ^ k) x = (π ^ k) x := by
        intro k
        induction k with
        | zero => exact ⟨hx, rfl⟩
        | succ k ih =>
          obtain ⟨h1, h2⟩ := hUc _ ih.1
          refine ⟨by rwx [pow_succ', Perm.mul_apply], ?_⟩
          rw [pow_succ', Perm.mul_apply, h2, ih.2, pow_succ', Perm.mul_apply]
      rw [(key k).2]
      exact ⟨k, by simp⟩
  · rintro (h | ⟨hx, hy⟩)
    · by_cases hx : U x
      · have hy : U y := by
          rcases hx with hx | hx
          · exact Or.inl (h.symm.trans hx)
          · exact Or.inr (h.symm.trans hx)
        exact (hUall x hx).trans (hUall y hy).symm
      · refine sameCycle_follow π ψ id (fun w => ¬ U w) hx h ?_
        intro w hw _
        exact ⟨(hUc w hw).2, fun h' => hw (by
          rcases h' with h' | h'
          · exact Or.inl (Perm.sameCycle_apply_left.mp h')
          · exact Or.inr (Perm.sameCycle_apply_left.mp h'))⟩
    · exact (hUall x hx).trans (hUall y hy).symm

end Merge

section FirstReturn

variable {X : Type*} [Finite X] (π : Perm X) (p : X → Prop)

/-- The orbit of a point of `{p}` returns to `{p}`. -/
theorem exists_return {x : X} (hx : p x) : ∃ m, 0 < m ∧ p ((π ^ m) x) :=
  ⟨orderOf π, orderOf_pos π, by rwx [pow_orderOf_eq_one]⟩

open Classical in
/-- The first time the `π`-orbit of `x` returns to `{p}`. -/
noncomputable def returnTime (x : {x // p x}) : ℕ := Nat.find (exists_return π p x.2)

/-- The return time is positive. -/
theorem returnTime_pos (x : {x // p x}) : 0 < returnTime π p x := by
  classical exact (Nat.find_spec (exists_return π p x.2)).1

/-- At the return time the orbit is back in `{p}`. -/
theorem pow_returnTime (x : {x // p x}) : p ((π ^ returnTime π p x) x.1) := by
  classical exact (Nat.find_spec (exists_return π p x.2)).2

/-- Before the return time the orbit avoids `{p}`. -/
theorem not_pow_of_lt_returnTime (x : {x // p x}) {j : ℕ} (hj0 : 0 < j)
    (hj : j < returnTime π p x) : ¬ p ((π ^ j) x.1) := by
  classical
  intro h
  exact Nat.find_min (exists_return π p x.2) hj ⟨hj0, h⟩

/-- Characterisation of the return time. -/
theorem returnTime_eq (x : {x // p x}) {m : ℕ} (hm0 : 0 < m) (hm : p ((π ^ m) x.1))
    (hmin : ∀ j, 0 < j → j < m → ¬ p ((π ^ j) x.1)) : returnTime π p x = m := by
  classical
  refine le_antisymm (Nat.find_min' _ ⟨hm0, hm⟩) ?_
  by_contra h
  push Not at h
  exact hmin _ (returnTime_pos π p x) h (pow_returnTime π p x)

/-- The first-return map to `{p}`. -/
noncomputable def returnFun (x : {x // p x}) : {x // p x} :=
  ⟨(π ^ returnTime π p x) x.1, pow_returnTime π p x⟩

/-- The first-return map is injective. -/
theorem returnFun_injective : Function.Injective (returnFun π p) := by
  intro x y hxy
  have h  := congrArg Subtype.val hxy
  -- the smaller return time forces equality
  have key : ∀ (x y : {x // p x}), returnTime π p x ≤ returnTime π p y →
      (π ^ returnTime π p x) x.1 = (π ^ returnTime π p y) y.1 → x = y := by
    intro x y hle h
    have h' : x.1 = (π ^ (returnTime π p y - returnTime π p x)) y.1 := by
      apply (π ^ returnTime π p x).injective
      rw [h, ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · apply Subtype.ext
      rw [h', heq, Nat.sub_self, pow_zero, Perm.one_apply]
    · have := returnTime_pos π p x
      exact absurd (h' ▸ x.2) (not_pow_of_lt_returnTime π p y (by omega) (by omega))
  rcases le_total (returnTime π p x) (returnTime π p y) with hle | hle
  · exact key x y hle h
  · exact (key y x hle h.symm).symm

/-- **The first-return permutation** of `π` on the subtype `{x // p x}`. -/
noncomputable def firstReturn : Perm {x // p x} :=
  Equiv.ofBijective (returnFun π p) (Finite.injective_iff_bijective.mp (returnFun_injective π p))

/-- The first-return permutation. -/
theorem firstReturn_apply (x : {x // p x}) :
    (firstReturn π p x).1 = (π ^ returnTime π p x) x.1 := rfl

/-- If the first `m - 1` iterates after `x` avoid `{p}` and the `m`-th is in it, the first return
of `x` is the `m`-th iterate. -/
theorem firstReturn_eq (x : {x // p x}) {m : ℕ} (hm0 : 0 < m) (hm : p ((π ^ m) x.1))
    (hmin : ∀ j, 0 < j → j < m → ¬ p ((π ^ j) x.1)) :
    (firstReturn π p x).1 = (π ^ m) x.1 := by
  rw [firstReturn_apply, returnTime_eq π p x hm0 hm hmin]

/-- The cycles of the first-return map are the traces of the cycles of `π`. -/
theorem sameCycle_firstReturn_iff (x y : {x // p x}) :
    (firstReturn π p).SameCycle x y ↔ π.SameCycle x.1 y.1 := by
  classical
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction k with
    | zero => exact Perm.SameCycle.refl _ _
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, firstReturn_apply]
      exact ih.trans ⟨(returnTime π p _ : ℤ), by rw [zpow_natCast]⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    have key : ∀ k (hk : p ((π ^ k) x.1)),
        (firstReturn π p).SameCycle x ⟨(π ^ k) x.1, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        exact ⟨0, by simp⟩
      · set j := Nat.findGreatest (fun j => p ((π ^ j) x.1)) (k - 1)
        have hj : p ((π ^ j) x.1) := Nat.findGreatest_spec (P := fun j => p ((π ^ j) x.1))
          (Nat.zero_le _) (by simpa using x.2)
        have hjk : j < k := by
          have := Nat.findGreatest_le (P := fun j => p ((π ^ j) x.1)) (k - 1)
          omega
        have hret : (firstReturn π p ⟨(π ^ j) x.1, hj⟩).1 = (π ^ k) x.1 := by
          rw [firstReturn_eq π p _ (m := k - j) (by omega)]
          · rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk.le]
          · rwx [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk.le]
          · intro i hi0 hi
            rw [← Perm.mul_apply, ← pow_add]
            exact Nat.findGreatest_is_greatest (P := fun j => p ((π ^ j) x.1)) (n := k - 1)
              (by omega) (by omega)
        refine (ih j hjk hj).trans ⟨1, ?_⟩
        rw [zpow_one]
        exact Subtype.ext hret
    have := key k (hk ▸ y.2)
    simp [hk] at this
    exact this

end FirstReturn

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
    · simp [G, ha, hb, ite_false, Option.some.injEq] at hqq
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
