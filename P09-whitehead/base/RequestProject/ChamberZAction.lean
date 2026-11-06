module

public import RequestProject.ChamberZPoset
public import RequestProject.CoverLevelComparison

@[expose] public section

/-!
# The construction `Z` is equivariant

The copies of the base are attached in every marked chamber by the *same* marked map `att`,
which depends on the mirror type of a cell only.  Therefore the deck action of the Coxeter group
on the poset of spherical cosets (`FiniteChains.Davis.sphAct`) lifts to the complex `Z` of
modified chambers, for every group element `k` that preserves the set `M` of marked chambers —
in the application, for every element of `Γ`.

* `FiniteChains.Davis.zAct` — the action of such a `k` on `Z`, and `FiniteChains.Davis.zActIso`
  its packaging as an order automorphism;
* `FiniteChains.Davis.inZChamber_zAct` — it carries the chamber of `w` to the chamber of `k w`;
* `FiniteChains.Davis.zAct_zNew` — it carries the copy of the base attached at `w` to the copy
  attached at `k w`, by the identity of `X`: the marked attaching map is the same in every
  chamber.

Only the action on `Z` is built here; the quotient of `Z` by this action and the resulting
covering description are not constructed.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

section Act

variable (k : CayGroup A) (hk : ∀ w : CayGroup A, M (k * w) ↔ M w)

include hk in
theorem not_isMarkedApex_sphAct {p : Sph A} (hp : ¬ IsMarkedApex M p) :
    ¬ IsMarkedApex M (sphAct k p) := by
  rintro ⟨hemp, hrep⟩
  have hspx : p.spx = ∅ := hemp
  refine hp ⟨hspx, ?_⟩
  have h1 : (sphAct k p).rep⁻¹ * (k * p.rep) ∈ specialSub A ((sphAct k p).spx : Set V) :=
    inChamber_sphAct_self k p
  rw [sphAct_spx, hspx, Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
  have hrepeq : (sphAct k p).rep = k * p.rep := inv_mul_eq_one.1 h1
  rw [hrepeq] at hrep
  exact (hk p.rep).1 hrep

/-- **The action on `Z`**: old cells move by the deck action of the poset of spherical cosets,
and the copy of the base attached at `w` is carried to the copy attached at `k w` by the
identity of `X`. -/
noncomputable def zAct (z : Zpos A X M att) : Zpos A X M att :=
  match z with
  | Sum.inl p => Sum.inl ⟨sphAct k p.1, not_isMarkedApex_sphAct k hk p.2⟩
  | Sum.inr wx => Sum.inr (⟨k * wx.1.1, (hk wx.1.1).2 wx.1.2⟩, wx.2)

@[simp] theorem zAct_zNew (w : {w : CayGroup A // M w}) (x : X) :
    zAct (att := att) k hk (zNew w x) = zNew ⟨k * w.1, (hk w.1).2 w.2⟩ x := rfl

end Act

end Davis
end FiniteChains
