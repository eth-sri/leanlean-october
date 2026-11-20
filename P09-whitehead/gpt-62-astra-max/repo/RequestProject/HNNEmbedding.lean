module

public import Mathlib

@[expose] public section

/-!
# The HNN input of Section 3.4 (rule 1)

Rule 1 of the replacement operation `T` adjoins, for each extra generator `z`, a free
generator `b_z` and a stable letter `a_z` with `a_z b_z a_z⁻¹ = z b_z`.  The paper justifies
the step by two facts:

* in the free product `G(P) * F(b_z)` both `b_z` and `z b_z` have infinite order, "as seen
  by killing `G(P)`";
* the resulting HNN extension, which identifies the two infinite cyclic subgroups, contains
  the old group, by the normal form theorem (Serre, *Trees*, Chapter I, Section 5).

Both statements are verified here.  The second is the external theorem cited in the paper;
Mathlib contains the construction of HNN extensions together with their normal form
(`HNNExtension.of_injective`), so the citation is replaced by a machine-checked proof.
-/

noncomputable section

namespace FiniteChains

/-- Infinite order is detected by any monoid homomorphism. -/
theorem not_isOfFinOrder_of_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {x : M}
    (h : ¬ IsOfFinOrder (f x)) : ¬ IsOfFinOrder x := by
  intro hx
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
  exact h (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hxn, map_one]⟩)

/-- A generator of `ℤ` has infinite order. -/
theorem not_isOfFinOrder_ofAdd_one : ¬ IsOfFinOrder (Multiplicative.ofAdd (1 : ℤ)) := by
  rw [isOfFinOrder_iff_pow_eq_one] <;> simp_all

section FreeProduct

variable {G : Type*} [Group G]

/-- The retraction of `G * ℤ` onto `ℤ` that kills `G`. -/
def killBase : Monoid.Coprod G (Multiplicative ℤ) →* Multiplicative ℤ :=
  Monoid.Coprod.lift 1 (MonoidHom.id _)

@[simp] theorem killBase_inl (g : G) :
    killBase (Monoid.Coprod.inl g) = 1 := rfl

@[simp] theorem killBase_inr (n : Multiplicative ℤ) :
    killBase (Monoid.Coprod.inr n : Monoid.Coprod G (Multiplicative ℤ)) = n := rfl

/-- The adjoined free generator `b` of `G * ℤ`. -/
def freeGen : Monoid.Coprod G (Multiplicative ℤ) :=
  Monoid.Coprod.inr (Multiplicative.ofAdd 1)

/-- **`b` has infinite order in `G * ℤ`.** -/
theorem not_isOfFinOrder_freeGen : ¬ IsOfFinOrder (freeGen (G := G)) := by
  refine not_isOfFinOrder_of_map killBase ?_
  exact not_isOfFinOrder_ofAdd_one

/-- **`z·b` has infinite order in `G * ℤ`**, for every `z` in the old group: kill the old
group, and what is left is a generator of `ℤ`. -/
theorem not_isOfFinOrder_mul_freeGen (z : G) :
    ¬ IsOfFinOrder (Monoid.Coprod.inl z * freeGen) := by
  refine not_isOfFinOrder_of_map killBase ?_
  exact not_isOfFinOrder_ofAdd_one

end FreeProduct

section HNN

variable {G : Type*} [Group G]

/-- An element of infinite order generates an infinite cyclic subgroup. -/
def zpowersEquivInt {x : G} (hx : ¬ IsOfFinOrder x) :
    Multiplicative ℤ ≃* Subgroup.zpowers x := by
  refine MulEquiv.ofBijective ((zpowersHom G x).codRestrict _
    (fun n => Subgroup.zpow_mem_zpowers x _)) ⟨?_, ?_⟩
  · intro a b hab
    exact Multiplicative.toAdd.injective (injective_zpow_iff_not_isOfFinOrder.2 hx (congrArg Subtype.val hab))
  · rintro ⟨g, n, rfl⟩ <;> aesop

variable {x y : G} (hx : ¬ IsOfFinOrder x) (hy : ¬ IsOfFinOrder y)

/-- Two infinite cyclic subgroups are isomorphic. -/
def zpowersEquivZpowers :=
  (zpowersEquivInt hx).symm.trans (zpowersEquivInt hy)

/-- The form in which the paper uses it: an HNN extension identifying two infinite cyclic
subgroups contains the old group. -/
theorem hnn_infiniteCyclic_of_injective :
    Function.Injective (HNNExtension.of :
      G →* HNNExtension G (Subgroup.zpowers x) (Subgroup.zpowers y)
        (zpowersEquivZpowers hx hy)) :=
  HNNExtension.of_injective _

/-- **Rule 1 of Section 3.4.**  Adjoin a free generator `b` to `G`, and then a stable letter
conjugating `b` to `z·b`.  The associated subgroups are infinite cyclic, and the old group
`G` still embeds in the result. -/
theorem rule_one_embedding (z : G) :
    Function.Injective
      ((HNNExtension.of : Monoid.Coprod G (Multiplicative ℤ) →*
          HNNExtension (Monoid.Coprod G (Multiplicative ℤ))
            (Subgroup.zpowers (freeGen (G := G)))
            (Subgroup.zpowers (Monoid.Coprod.inl z * freeGen))
            (zpowersEquivZpowers not_isOfFinOrder_freeGen
              (not_isOfFinOrder_mul_freeGen z))).comp
        Monoid.Coprod.inl) := (hnn_infiniteCyclic_of_injective _ _).comp Monoid.Coprod.inl_injective

end HNN

end FiniteChains
