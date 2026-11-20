module

public import RequestProject.DavisSimplyConnected
public import RequestProject.NerveSupport

@[expose] public section

/-!
# The chamber complex `𝒟` is acyclic: `H_*(𝒟) = 0`, in particular `H₂(𝒟) = 0`

This file carries out, at the level of chains, the exhaustion by chambers that
`RequestProject/DavisSimplyConnected.lean` carries out for `π₁`.  The two ingredients are

* the acyclicity of a chamber and of its attaching subcomplex, already proved inside the model
  (`FiniteChains.Davis.chamber_exists_bdry_eq_of_cycle`,
  `FiniteChains.Davis.chamberInter_exists_bdry_eq_of_cycle`), and
* the chain-level gluing lemma `FiniteChains.Nerve.acyclicIn_union_of_unmixed`, which is proved
  directly through the coefficients: a chain of the union splits on the basis, the boundary of
  the `A`-part is a cycle supported on the intersection, and the filling of that cycle corrects
  the two halves into cycles of the two pieces.

Main results:

* `FiniteChains.Davis.acyclicIn_chamber`, `FiniteChains.Davis.acyclicIn_chamberInter` — the two
  local acyclicity statements, transported from the subposets to the subgroups
  `C_*(A) ⊆ ℤ[List (Sph A)]` of chains supported on them;
* `FiniteChains.Davis.acyclicIn_union_chamber` — adding one chamber to an upward closed union;
* `FiniteChains.Davis.acyclicIn_upto` — the exhaustion by length levels;
* `FiniteChains.Davis.exists_bdry_eq_of_cycle_davis` — **`H_*(𝒟) = 0`**: every increasing cycle
  of the augmented simplicial chain complex of the Davis poset, in every degree, is a boundary
  of an increasing chain.  In particular every two-cycle is `∂₃` of a three-chain: the complex
  `C₃` and the boundary `∂₃` of `RequestProject/NervePrism.lean` are the ones used here, nothing
  is truncated.
-/

namespace FiniteChains.Nerve

/-- Finitely supported chains lie in a bounded stage of any vertex filtration. -/
theorem exists_incOn_bound {P : Type*} [Preorder P] (size : P → ℕ)
    {c : Ch P} (hc : c ∈ Inc P) : ∃ n, c ∈ IncOn (fun p => size p ≤ n) := by
  let L (l : List P) := (l.map size).sum
  refine ⟨c.support.sup L, (mem_incOn_iff c).mpr fun l hl => ⟨(mem_inc_iff _).mp hc l hl, ?_⟩⟩
  intro p hp
  exact (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hp)).trans
    (Finset.le_sup (f := L) hl)

end FiniteChains.Nerve

namespace FiniteChains
namespace Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### Local acyclicity, supported on the subposets -/

omit [Fintype V] in
/-- **The chamber `F_x` is acyclic**, as a subgroup of chains of the ambient complex. -/
theorem acyclicIn_chamber (x : CayGroup A) : AcyclicIn (InChamber (A := A) x) := by
  refine Nerve.acyclicIn_of_subtype _ ?_
  intro c hc hcyc
  exact chamber_exists_bdry_eq_of_cycle x hc hcyc

/-- **The attaching subcomplex of the chamber `F_x` is acyclic**, as a subgroup of chains of the
ambient complex. -/
theorem acyclicIn_chamberInter {x : CayGroup A} (hx : x ≠ 1) :
    AcyclicIn (fun p : Sph A => InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
  refine Nerve.acyclicIn_of_subtype _ ?_
  intro c hc hcyc
  exact chamberInter_exists_bdry_eq_of_cycle hx hc hcyc

/-! ### Adding one chamber -/

/-- **The gluing step for chains.**  Adding one chamber to an upward closed acyclic union whose
intersection with the chamber is the attaching subcomplex keeps the union acyclic. -/
theorem acyclicIn_union_chamber {x : CayGroup A} (hx : x ≠ 1) (Prev : Sph A → Prop)
    (hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q)
    (hPrev : AcyclicIn Prev)
    (hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
      (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty)) :
    AcyclicIn (fun p : Sph A => Prev p ∨ InChamber x p) := by
  refine Nerve.acyclicIn_union_of_unmixed (A := Prev) (B := InChamber (A := A) x)
    (fun _ => Iff.rfl) ?_ hPrev (acyclicIn_chamber x)
    (Nerve.acyclicIn_congr (fun p => (hinter p).symm) (acyclicIn_chamberInter hx))
  rintro a b hab (ha | ha) hb
  · exact Or.inl ⟨ha, hup a b hab ha⟩
  · exact Or.inr ⟨ha, inChamber_of_le hab ha⟩

/-- Every cycle on the first `n` length levels of chambers is a boundary there. -/
theorem acyclicIn_upto (A : CommRel V) : ∀ n : ℕ, AcyclicIn (Upto (A := A) n) := by
  apply chamberInduction A (fun S => AcyclicIn (chamberUnion InChamber S))
  · simpa only [chamberUnion_singleton] using acyclicIn_chamber (A := A) 1
  · intro n S x hx hl hs hne h
    rw [chamberUnion_insert]
    exact acyclicIn_union_chamber hne _ (fun _ _ hpq => chamberUnion_up (C := InChamber) (fun _ _ _ h => inChamber_of_le h) hpq)
      h (upto_overlap hx hl hs)

/-! ### Acyclicity of the whole complex -/

/-- **`H_*(𝒟) = 0`.**  Every increasing cycle of the augmented simplicial chain complex of the
poset of spherical cosets — in every degree, in particular every two-cycle — is the boundary of
an increasing chain.  For `z ∈ C₂(𝒟)` with `∂z = 0` this produces `v ∈ C₃(𝒟)` with `∂₃ v = z`. -/
theorem exists_bdry_eq_of_cycle_davis (A : CommRel V) {z : Nerve.Ch (Sph A)}
    (hz : z ∈ Nerve.Inc (Sph A)) (hcyc : Nerve.bdry z = 0) :
    ∃ v ∈ Nerve.Inc (Sph A), Nerve.bdry v = z := by
  obtain ⟨n, hn⟩ := exists_incOn_bound (fun p : Sph A => RACG.clen A p.rep) hz
  obtain ⟨v, hv, hdv⟩ := acyclicIn_upto A n z
    (incOn_mono (fun p hp => ⟨p.rep, hp, inChamber_rep p⟩) hn) hcyc
  exact ⟨v, Nerve.incOn_le_inc _ hv, hdv⟩

end Davis
end FiniteChains
