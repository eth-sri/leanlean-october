module

public import RequestProject.DavisChamberModel
public import RequestProject.OrderComplexGluing

@[expose] public section

/-!
# One step of the chamber induction in the Davis model

This file feeds the chamber intersection formula of `RequestProject/DavisChamberModel.lean` and
the contractions of `RequestProject/MirrorSimplyConnected.lean` into the combinatorial gluing
lemma of `RequestProject/OrderComplexGluing.lean`.

* `FiniteChains.Davis.inChamber_of_le` — chambers are upward closed in the poset of spherical
  cosets: if a cell of `F_x` is a face of another cell, that cell is in `F_x` too.  This is what
  makes the chamber cover *unmixed*: no comparability inside a union of chambers joins a cell
  that belongs only to the old part with a cell that belongs only to the new chamber.
* `FiniteChains.Davis.nullIn_chamber`, `connectedIn_chamber`, `nullIn_chamberInter`,
  `connectedIn_chamberInter` — the chamber and its attaching subcomplex, as subposets of the
  ambient Davis poset, are connected and kill all their loops.
* `FiniteChains.Davis.nullIn_union_chamber` — **the inductive step**: if the union `Prev` of the
  earlier chambers is upward closed, connected, kills its loops, and meets `F_x` exactly in the
  descending mirrors (which is the intersection formula), then the same three properties hold
  for `Prev ∪ F_x`.

What is *not* done here is the exhaustion: enumerating `W` by nondecreasing length, checking that
`Prev` at each stage satisfies the hypothesis `hinter` above, and passing to the union over all
stages (every finite path lies in finitely many chambers).  That is the remaining link on the way
to simple connectivity of the whole Davis complex.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V}

/-- **Chambers are upward closed**: a cell above a cell of `F_x` lies in `F_x`. -/
theorem inChamber_of_le {x : CayGroup A} {p q : Sph A} (hpq : p ≤ q) (hp : InChamber x p) :
    InChamber x q := by
  have h2 : q.rep⁻¹ * x = (p.rep⁻¹ * q.rep)⁻¹ * (p.rep⁻¹ * x) := by group
  rw [InChamber, h2]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpq.2) (specialSub_mono (by exact_mod_cast hpq.1) hp)

variable (x : CayGroup A)

/-- Every loop of the Davis complex inside one chamber is null-homotopic there. -/
theorem nullIn_chamber : NullIn (InChamber x) :=
  nullIn_of_simplyConnected (chamber_simplyConnected x)

/-- A chamber is connected. -/
theorem connectedIn_chamber : ConnectedIn (InChamber x) :=
  connectedIn_of_isConnected (chamber_isConnected x)

section Inter

variable [Fintype V]

variable {x : CayGroup A} (hx : x ≠ 1)
include hx

/-- The attaching subcomplex of a chamber is connected. -/
theorem connectedIn_chamberInter :
    ConnectedIn (fun p : Sph A => InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) :=
  connectedIn_of_isConnected (chamberInter_isConnected hx)

/-- **The inductive step of the chamber argument.**  If the union `Prev` of the earlier chambers
is upward closed, kills its loops and is connected, and if its intersection with the chamber
`F_x` is the union of the descending mirrors — which is the content of
`FiniteChains.Davis.mem_earlier_chamber_iff` — then `Prev ∪ F_x` again kills its loops and is
connected. -/
theorem nullIn_union_chamber (Prev : Sph A → Prop)
    (hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q)
    (hPrevNull : NullIn Prev) (hPrevConn : ConnectedIn Prev)
    (hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
      (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty)) :
    NullIn (fun p => Prev p ∨ InChamber x p) ∧
      ConnectedIn (fun p => Prev p ∨ InChamber x p) := by
  have hj := (hinter _).2 (interTop hx).2
  have hmix : ∀ a b : Sph A, a ≤ b → (Prev a ∨ InChamber x a) → (Prev b ∨ InChamber x b) →
      ((Prev a ∧ Prev b) ∨ (InChamber x a ∧ InChamber x b)) := by
    grind [inChamber_of_le]
  exact ⟨htpy_nil_of_pathIn_union (fun _ => Iff.rfl) hmix hPrevNull (nullIn_chamber x)
      hPrevConn (connectedIn_chamber x) (connectedIn_congr (fun p => (hinter p).symm) (connectedIn_chamberInter hx)) hj,
    connectedIn_union (fun _ => Iff.rfl) hPrevConn (connectedIn_chamber x) hj⟩

end Inter

end Davis
end FiniteChains
