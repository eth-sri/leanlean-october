/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index

/-!
# Cardinality bounds for `n`-torsion in finite commutative groups

The `n`-torsion subgroup of a commutative group `G` is `(powMonoidHom n : G →* G).ker`.

## Main results

* `MonoidHom.card_powMonoidHom_ker_le_of_surjective`: a surjection does not increase the
  `n`-torsion.
* `MonoidHom.card_powMonoidHom_ker_le_mul`: the `n`-torsion of `G` is bounded by the
  `n`-torsion of the kernel of `φ : G →* H` times the `n`-torsion of `H`.
* `MonoidHom.card_powMonoidHom_ker_le_of_coset_cover`: a subgroup covered by finitely many
  cosets of the image of `φ` has `m`-torsion bounded by the `m`-torsion of the source times the
  number of cosets.
-/

@[expose] public section

namespace MonoidHom

/-- A subgroup covered by finitely many cosets of the image of `φ` has `m`-torsion bounded by the
`m`-torsion of the source times the number of cosets. -/
theorem card_powMonoidHom_ker_le_of_coset_cover
    {A G ι : Type*} [CommGroup A] [CommGroup G] [Finite A] [Finite G] [Fintype ι]
    (φ : A →* G) (S : Subgroup G) (c : ι → G)
    (hcover : ∀ x : S, ∃ a : A, ∃ i : ι, x.val = φ a * c i)
    (m : ℕ) :
    Nat.card (powMonoidHom m : S →* S).ker ≤
      Nat.card (powMonoidHom m : A →* A).ker * Fintype.card ι := by
  /- Power torsion maps functorially under a group homomorphism. -/
  /- A surjective homomorphism does not increase the number of `n`-torsion elements. -/
  /- The torsion of the middle group is bounded by the torsion of a
  homomorphism's kernel and the torsion of its target. -/
  let π := QuotientGroup.mk' φ.range
  let ψ : S →* G ⧸ φ.range := π.comp S.subtype
  let δ := ψ.rangeRestrict
  have hφ (a : A) : π (φ a) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hex (r : ψ.range) : ∃ i : ι, r.val = π (c i) := by
    obtain ⟨x, hx⟩ := r.property
    obtain ⟨a, i, he⟩ := hcover x
    exact ⟨i, by rw [← hx]; change π x.val = _; rw [he, map_mul, hφ, one_mul]⟩
  choose i hi using hex
  have hinj : Function.Injective i := fun x y h => Subtype.ext (by rw [hi x, hi y, h])
  have hrange : Nat.card ψ.range ≤ Fintype.card ι := by
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective i hinj
  let j : (powMonoidHom m : S →* S).ker →* (powMonoidHom m : ψ.range →* ψ.range).ker :=
    { toFun := fun x ↦ ⟨δ x, by
        change (δ x.val) ^ m = 1
        rw [← map_pow, show x.val ^ m = 1 from x.property, map_one]⟩
      map_one' := Subtype.ext (map_one δ)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul δ _ _) }
  let k : j.ker → (powMonoidHom m : φ.range →* φ.range).ker :=
    fun x ↦ ⟨⟨x.val.val.val, (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun z : ψ.range ↦ z.val) (congrArg Subtype.val x.property))⟩, by
      apply Subtype.ext
      exact congrArg (Subtype.val : S → G) x.val.property⟩
  have hk : Function.Injective k := fun x y h =>
    Subtype.ext <| Subtype.ext <| Subtype.ext <|
      congrArg (fun z : (powMonoidHom m : φ.range →* φ.range).ker ↦ z.val.val) h
  have hsurj : Nat.card (powMonoidHom m : φ.range →* φ.range).ker ≤
      Nat.card (powMonoidHom m : A →* A).ker := by
    have hpow : (powMonoidHom m : A →* A).range ≤
        ((powMonoidHom m : φ.range →* φ.range).range).comap φ.rangeRestrict := by
      rintro x ⟨y, rfl⟩; exact ⟨φ.rangeRestrict y, (map_pow φ.rangeRestrict y m).symm⟩
    simpa only [← Subgroup.index_eq_card, Subgroup.index_range] using
      Nat.card_le_card_of_surjective _
        (QuotientGroup.map_surjective_of_surjective _ _ φ.rangeRestrict
          (QuotientGroup.mk_surjective.comp φ.rangeRestrict_surjective) hpow)
  calc
    Nat.card (powMonoidHom m : S →* S).ker = Nat.card j.ker * Nat.card j.range :=
      (Subgroup.card_ker_mul_card_range j).symm
    _ ≤ Nat.card (powMonoidHom m : A →* A).ker * Fintype.card ι :=
      Nat.mul_le_mul ((Nat.card_le_card_of_injective k hk).trans hsurj)
        ((Subgroup.card_le_card_group j.range).trans
          ((Subgroup.card_le_card_group _).trans hrange))

end MonoidHom
