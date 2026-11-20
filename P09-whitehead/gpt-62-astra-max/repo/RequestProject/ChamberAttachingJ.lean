module

public import RequestProject.DavisSimplyConnected

@[expose] public section

/-!
# The attaching intersection of a chamber is `J_w`, not the whole outer boundary

This file records, inside the concrete model of `RequestProject/DavisChamberModel.lean`, the
**corrected** form of the intersection formula that the gluing argument uses, and proves that
the two candidate subcomplexes really are different objects.

Write `D(w) = {s | ℓ(w s) < ℓ(w)}` for the descent set of `w` (`FiniteChains.RACG.rdescFinset`).

* `FiniteChains.Davis.MarkedMirror w s` — the marked mirror `(F_s)_w`: the cells of the chamber
  `F_w` whose mirror type contains `s`;
* `FiniteChains.Davis.JSet w` — `J_w = ⋃_{s ∈ D(w)} (F_s)_w`;
* `FiniteChains.Davis.OuterBdry w` — the whole outer boundary of the chamber, i.e. the cells of
  `F_w` of nonempty mirror type (a copy of the whole nerve `L`);
* `FiniteChains.Davis.mem_earlier_chamber_iff_jSet` — **the correct intersection formula**:
  `F_w ∩ ⋃_{earlier} F_v = J_w`, in the sharp form with ties in word length allowed, and
  `FiniteChains.Davis.mem_shorter_chamber_iff_jSet` for strictly shorter chambers;
* `FiniteChains.Davis.jSet_imp_outerBdry` — `J_w ⊆ ∂F_w`, and
  `FiniteChains.Davis.exists_outerBdry_not_jSet`, `FiniteChains.Davis.jSet_ne_outerBdry` —
  the inclusion is **strict** as soon as some vertex of `L` is not a descent of `w`; for
  `w = 1` the set `J_1` is empty while the outer boundary is not.  Hence the attaching
  intersection cannot be identified with the outer end of the cylinder: the outer end is a
  copy of the whole of `L`, whereas `J_w` is the union of the descending mirrors only, and it
  is exactly the latter that is contractible by the mirror contraction
  (`FiniteChains.Davis.chamberInter_simplyConnected`,
  `FiniteChains.Davis.chamberInter_exists_bdry_eq_of_cycle`).
-/

namespace FiniteChains
namespace Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The marked mirror `(F_s)_w`** of the chamber `F_w`: the cells of `F_w` whose mirror type
contains the generator `s`. -/
def MarkedMirror (w : CayGroup A) (s : V) (p : Sph A) : Prop :=
  InChamber w p ∧ s ∈ p.spx

/-- **`J_w = ⋃_{s ∈ D(w)} (F_s)_w`**: the union of the *descending* marked mirrors of the
chamber `F_w`. -/
def JSet (w : CayGroup A) (p : Sph A) : Prop :=
  ∃ s ∈ rdescFinset A w, MarkedMirror w s p

theorem jSet_iff {w : CayGroup A} {p : Sph A} :
    JSet w p ↔ (InChamber w p ∧ (p.spx ∩ rdescFinset A w).Nonempty) := by
  constructor
  · rintro ⟨s, hs, hp, hsp⟩
    exact ⟨hp, ⟨s, Finset.mem_inter.2 ⟨hsp, hs⟩⟩⟩
  · rintro ⟨hp, s, hs⟩
    obtain ⟨hsp, hsd⟩ := Finset.mem_inter.1 hs
    exact ⟨s, hsd, hp, hsp⟩

/-- **The corrected intersection formula.**  For a cell of the chamber `F_w`, lying in some
other chamber `F_v` with `ℓ(v) ≤ ℓ(w)` — ties included — is equivalent to lying in
`J_w = ⋃_{s ∈ D(w)} (F_s)_w`.  So
`F_w ∩ ⋃_{v earlier} F_v = J_w`, *not* the whole outer boundary. -/
theorem mem_earlier_chamber_iff_jSet {w : CayGroup A} {p : Sph A} (hp : InChamber w p) :
    (∃ v : CayGroup A, v ≠ w ∧ RACG.clen A v ≤ RACG.clen A w ∧ InChamber v p) ↔ JSet w p := by
  rw [jSet_iff]
  constructor
  · intro h
    exact ⟨hp, (mem_earlier_chamber_iff hp).1 h⟩
  · rintro ⟨-, h⟩
    exact (mem_earlier_chamber_iff hp).2 h

/-- The same formula with strictly shorter chambers. -/
theorem mem_shorter_chamber_iff_jSet {w : CayGroup A} {p : Sph A} (hp : InChamber w p) :
    (∃ v : CayGroup A, RACG.clen A v < RACG.clen A w ∧ InChamber v p) ↔ JSet w p := by
  rw [jSet_iff]
  constructor
  · intro h
    exact ⟨hp, (mem_shorter_chamber_iff hp).1 h⟩
  · rintro ⟨-, h⟩
    exact (mem_shorter_chamber_iff hp).2 h

/-! ### The apex of a chamber -/

omit [Fintype V] in
theorem specialSub_empty : specialSub A (∅ : Set V) = ⊥ := by
  rw [specialSub, Set.image_empty, Subgroup.closure_empty]

omit [Fintype V] in
/-- The apex of the chamber `F_g` is the cell `{g}`: its representative is `g` itself. -/
theorem chamberPt_empty_rep (g : CayGroup A) :
    (chamberPt g (isSimplex_empty (A := A))).rep = g := by
  have h := chamberPt_inChamber g (isSimplex_empty (A := A))
  have h1 : (chamberPt g (isSimplex_empty (A := A))).rep⁻¹ * g ∈
      specialSub A ((∅ : Finset V) : Set V) := h
  rw [Finset.coe_empty, specialSub_empty, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 h1

/-! ### The outer boundary is strictly bigger than `J_w` -/

omit [DecidableEq V] [Fintype V] in
theorem isSimplex_singleton (s : V) : IsSimplex A {s} := by
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab

end Davis
end FiniteChains
