import RequestProject.MirrorSimplyConnected
noncomputable section


/-!
# The concrete chamber model of the Davis complex, and its chamber intersections

This file builds the complex `𝒟` of the chamber argument *as an explicit poset*, so that the
chamber intersection formula becomes a statement about actual subcomplexes rather than an
interface hypothesis.

The model is the poset of **spherical cosets**: pairs `(w W_T, T)` where `T` is a simplex of `L`
(a clique of the commutation graph) and `w W_T` is a coset of the special subgroup `W_T`, ordered
by inclusion of cosets.  Each coset is represented by its unique shortest element
(`FiniteChains.RACG.existsUnique_shortest_coset`), so no quotient construction is needed:

* `FiniteChains.Davis.Sph A` — the poset; `Sph.rep` is the shortest element, `Sph.spx` the
  simplex; the order is `p ≤ q ↔ p.spx ⊆ q.spx ∧ p.rep⁻¹ q.rep ∈ W_{q.spx}`.

The order complex of this poset is `𝒟`: its vertices are the spherical cosets, i.e. exactly the
cells `w W_T` of the Davis complex, and a chain of the poset is a simplex of the barycentric
subdivision.  Two functors of the project are available on any poset and are used here:
`FiniteChains.Comb.orderCx` (the two-skeleton, for `π₁`) and `FiniteChains.Nerve.Ch`
(the simplicial chain complex in *all* degrees, so that `∂₃` is kept and `H₂` is not disturbed
by truncation).

* `FiniteChains.Davis.Chamber A x` — the chamber `F_x`: the subposet of cosets containing `x`.
  It is isomorphic to the poset of all simplices of `L` (`FiniteChains.Davis.chamberOrderIso`),
  is a cone on its minimum `{x} = x W_∅`, hence its order complex is connected, simply connected
  (`chamber_simplyConnected`) and acyclic in all degrees (`chamber_exists_bdry_eq_of_cycle`).
* `FiniteChains.Davis.mem_earlier_chamber_iff` — **the chamber intersection formula for the
  actual subcomplexes**: a coset of the chamber `F_x` lies in some chamber `F_y` with `y ≠ x`
  and `ℓ(y) ≤ ℓ(x)` if and only if its simplex meets the descent set `D(x)`.  So
  `F_x ∩ ⋃_{earlier} F_y` is the subposet `ChamberInter A x`.
* `FiniteChains.Davis.chamberInterOrderIso` — that intersection is isomorphic to the poset
  `𝒫_{D(x)} = {σ ∈ L : σ ∩ D(x) ≠ ∅}` of `RequestProject/MirrorContraction.lean`; hence
  (`chamberInter_simplyConnected`, `chamberInter_exists_bdry_eq_of_cycle`,
  `chamberInter_isConnected`) it is nonempty, connected, simply connected and acyclic, by the
  contraction `ρ(σ) = σ ∩ D(x)` of the text, applied here directly inside the model.
-/

namespace FiniteChains.Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-! ### The poset of spherical cosets -/

/-- **A spherical coset** of the right-angled Coxeter group: a simplex `T` of `L` together with
a coset of `W_T`, represented by its unique shortest element. -/
def Sph (A : CommRel V) :=
  {p : CayGroup A × Finset V // IsSimplex A p.2 ∧ ∀ s ∈ p.2, ¬ IsRDesc A p.1 s}

variable {A : CommRel V}

/-- The shortest element of the coset. -/
def Sph.rep (p : Sph A) := p.1.1

/-- The simplex of `L` carried by the coset: its mirror type. -/
def Sph.spx (p : Sph A) := p.1.2

theorem Sph.isSimplex (p : Sph A) : IsSimplex A p.spx := p.2.1

theorem Sph.no_rdesc (p : Sph A) : ∀ s ∈ p.spx, ¬ IsRDesc A p.rep s := p.2.2

theorem Sph.ext' {p q : Sph A} (hr : p.rep = q.rep) (hs : p.spx = q.spx) : p = q := by
  obtain ⟨⟨a, s⟩, hp⟩ := p
  aesop

omit [DecidableEq V] in
/-- A simplex of `L` is a commuting set of generators. -/
theorem commuting_of_isSimplex {σ : Finset V} (h : IsSimplex A σ) : Commuting A (σ : Set V) :=
  by tauto

theorem specialSub_mono (h : S ⊆ T) : specialSub A S ≤ specialSub A T :=
  Subgroup.closure_mono (Set.image_mono h)

/-- **The order of the Davis poset**: inclusion of cosets. -/
instance : PartialOrder (Sph A) where
  le p q := p.spx ⊆ q.spx ∧ p.rep⁻¹ * q.rep ∈ specialSub A (q.spx : Set V)
  le_refl p := ⟨Finset.Subset.refl _, by simp⟩
  le_trans p q r hpq hqr := by
    refine ⟨hpq.1.trans hqr.1, ?_⟩
    have h1 :=
      specialSub_mono (by exact_mod_cast hqr.1) hpq.2
    have h2 : p.rep⁻¹ * r.rep = (p.rep⁻¹ * q.rep) * (q.rep⁻¹ * r.rep) := by group
    rw [h2]
    exact Subgroup.mul_mem _ h1 hqr.2
  le_antisymm p q hpq hqp := by
    have hspx := Finset.Subset.antisymm hpq.1 hqp.1
    have hT := commuting_of_isSimplex p.isSimplex
    have huniq := existsUnique_shortest_coset A hT p.rep
    have hp : p.rep⁻¹ * p.rep ∈ specialSub A (p.spx : Set V) ∧
        ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A p.rep s := by
      refine ⟨by simp, ?_⟩
      intro s hs
      exact p.no_rdesc s (Finset.mem_coe.1 hs)
    have hq : p.rep⁻¹ * q.rep ∈ specialSub A (p.spx : Set V) ∧
        ∀ s ∈ (p.spx : Set V), ¬ IsRDesc A q.rep s := by
      refine ⟨by simp_all, ?_⟩
      intro s hs
      exact q.no_rdesc s (hspx ▸ Finset.mem_coe.1 hs)
    have h1 := huniq.unique hp hq
    exact Sph.ext' h1 hspx

/-! ### Chambers -/

/-- The coset `p` contains the group element `x`: the corresponding cell of the Davis complex
lies in the chamber `F_x`. -/
def InChamber (x : CayGroup A) (p : Sph A) :=
  p.rep⁻¹ * x ∈ specialSub A (p.spx : Set V)

/-- **The chamber `F_x`** as a subposet of the Davis poset. -/
def Chamber (A : CommRel V) (x : CayGroup A) := {p : Sph A // InChamber x p}

instance (x : CayGroup A) : PartialOrder (Chamber A x) := Subtype.partialOrder _


/-- Inside one chamber the order is just inclusion of simplices. -/
theorem le_of_inChamber {p q : Sph A} (hp : InChamber x p) (hq : InChamber x q)
    (h : p.spx ⊆ q.spx) : p ≤ q := by
  refine ⟨h, ?_⟩
  have h1 :=
    specialSub_mono (by exact_mod_cast h) hp
  have h2 : x⁻¹ * q.rep ∈ specialSub A q.spx := by
    have := Subgroup.inv_mem _ hq
    simp_all
  have h3 : p.rep⁻¹ * q.rep = (p.rep⁻¹ * x) * (x⁻¹ * q.rep) := by group
  rw [h3]
  exact Subgroup.mul_mem _ h1 h2

/-- The unique cell of the chamber `F_x` with a given mirror type. -/
def chamberPt (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) : Sph A :=
  ⟨((existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose, σ),
    hσ, by grind⟩

@[simp] theorem chamberPt_spx x {σ : Finset V} (hσ : IsSimplex A σ) :
    (chamberPt x hσ).spx = σ := rfl

theorem chamberPt_inChamber x {σ : Finset V} (hσ : IsSimplex A σ) :
    InChamber x (chamberPt x hσ) := by
  have h := (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.1
  have := Subgroup.inv_mem _ h
  tauto


/-! ### The chamber is a cone -/

omit [DecidableEq V] in
theorem isSimplex_empty : IsSimplex A (∅ : Finset V) := by
  tauto

/-- The apex of the chamber `F_x`: the cell `x W_∅ = {x}`. -/
def chamberApex x : Chamber A x :=
  ⟨chamberPt x (isSimplex_empty (A := A)), chamberPt_inChamber x _⟩

theorem chamberApex_le (p : Chamber A x) : chamberApex x ≤ p :=
  le_of_inChamber (chamberApex x).2 p.2 (Finset.empty_subset _)

/-- **The chamber is simply connected**: its order complex is a cone on the apex. -/
theorem chamber_simplyConnected x :
    Comb.SimplyConnected (Comb.orderCx (Chamber A x)) :=
  Comb.simplyConnected_orderCx (chamberApex x) _
    chamberApex_le (by simp) (by simp)

/-- The chamber is connected. -/
theorem chamber_isConnected x :
    Comb.IsConnected (Comb.orderCx (Chamber A x)) :=
  Comb.isConnected_orderCx (chamberApex x) _
    chamberApex_le (by simp)

/-- **The chamber is acyclic in all degrees**: every increasing cycle of its simplicial chain
complex, in every degree including the augmentation degree, is a boundary. -/
theorem chamber_exists_bdry_eq_of_cycle x {c}
    (hc : c ∈ Nerve.Inc (Chamber A x)) (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (Chamber A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle _ (chamberApex x)
    (by tauto) chamberApex_le (by simp) hc hcyc

/-! ### The intersection with the earlier chambers -/

section Inter

variable [Fintype V]

/-- **The chamber intersection formula for the actual subcomplexes.**  A cell of the chamber
`F_x` lies in some strictly earlier chamber (`y ≠ x`, `ℓ(y) ≤ ℓ(x)`) exactly when its mirror
type meets the descent set `D(x)`; that is,
`F_x ∩ ⋃_{earlier} F_y = ⋃_{s ∈ D(x)} (F_s)_x`. -/
theorem mem_earlier_chamber_iff (hp : InChamber x p) :
    (∃ y, y ≠ x ∧ RACG.clen A y ≤ RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  have hT := commuting_of_isSimplex p.isSimplex
  have hkey := exists_rdesc_iff_exists_earlier A hT x
  constructor
  · rintro ⟨y, hne, hlen, hy⟩
    have hxy : x⁻¹ * y ∈ specialSub A p.spx := by
      have h1 : x⁻¹ * p.rep ∈ specialSub A p.spx := by
        have := Subgroup.inv_mem _ hp
        simp_all
      have h2 : x⁻¹ * y = (x⁻¹ * p.rep) * (p.rep⁻¹ * y) := by group
      rw [h2]
      exact Subgroup.mul_mem _ h1 hy
    obtain ⟨s, hs, hsd⟩ := hkey.1 (by tauto)
    exact ⟨s, Finset.mem_inter.2 ⟨Finset.mem_coe.1 hs, (mem_rdescFinset A).2 hsd⟩⟩
  · rintro ⟨s, hs⟩
    cases' Finset.mem_inter.1 hs with hsσ hsd
    obtain ⟨y, hxy, hne, hlen⟩ := hkey.2 ⟨s, Finset.mem_coe.2 hsσ, (mem_rdescFinset A).1 hsd⟩
    refine ⟨y, hne, hlen, ?_⟩
    have h1 : p.rep⁻¹ * y = (p.rep⁻¹ * x) * (x⁻¹ * y) := by group
    rw [InChamber, h1]
    exact Subgroup.mul_mem _ hp hxy

/-- **The attaching subcomplex of the chamber `F_x`**: the part of `F_x` contained in the union
of the earlier chambers, by `FiniteChains.Davis.mem_earlier_chamber_iff`. -/
def ChamberInter (A : CommRel V) (x : CayGroup A) :=
  {p : Sph A // InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty}

instance (x : CayGroup A) : PartialOrder (ChamberInter A x) := Subtype.partialOrder _

variable {x : CayGroup A}

/-- The descent set itself is a cell of the attaching subcomplex: the top vertex `D(x)`. -/
def interTop (hx : x ≠ 1) : ChamberInter A x :=
  ⟨chamberPt x (isSimplex_rdescFinset A x), chamberPt_inChamber x _, by
    simp [chamberPt_spx, Finset.inter_self]
    exact rdescFinset_nonempty A hx⟩


/-- The contraction `ρ(σ) = σ ∩ D(x)` of the text, inside the model. -/
def interRho (p : ChamberInter A x) : ChamberInter A x :=
  let hsubset : p.1.spx ∩ rdescFinset A x ⊆ p.1.spx := Finset.inter_subset_left
  let hsimplex := isSimplex_subset A hsubset p.1.isSimplex
  ⟨chamberPt x hsimplex,
    chamberPt_inChamber x hsimplex, by
      have hspx :=
        chamberPt_spx x hsimplex
      rw [hspx]
      grind [Finset.inter_assoc, Finset.inter_self]⟩

theorem interRho_spx (p : ChamberInter A x) :
    (interRho p).1.spx = p.1.spx ∩ rdescFinset A x := by
  rfl

theorem interRho_le (p : ChamberInter A x) : interRho p ≤ p := by
  refine le_of_inChamber (interRho p).2.1 p.2.1 ?_
  exact Finset.inter_subset_left

theorem interRho_le_top hx (p : ChamberInter A x) : interRho p ≤ interTop hx := by
  refine le_of_inChamber (interRho p).2.1 (interTop hx).2.1 ?_
  exact Finset.inter_subset_right

theorem interRho_mono {p q : ChamberInter A x} (h : p ≤ q) : interRho p ≤ interRho q := by
  have h1 := h.1
  refine le_of_inChamber (interRho p).2.1 (interRho q).2.1 ?_
  grind [interRho_spx]

/-- **The attaching subcomplex of a chamber is simply connected**, proved inside the model by
the path contraction of `RequestProject/MirrorSimplyConnected.lean`. -/
theorem chamberInter_simplyConnected (hx : x ≠ 1) :
    Comb.SimplyConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.simplyConnected_orderCx _ interRho interRho_le (interRho_le_top hx)
    interRho_mono

/-- The attaching subcomplex is connected. -/
theorem chamberInter_isConnected (hx : x ≠ 1) :
    Comb.IsConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.isConnected_orderCx _ interRho interRho_le (interRho_le_top hx)

/-- **The attaching subcomplex is acyclic in all degrees.** -/
theorem chamberInter_exists_bdry_eq_of_cycle (hx : x ≠ 1)
    {c} (hc : c ∈ Nerve.Inc (ChamberInter A x))
    (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (ChamberInter A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle interRho _ (fun _ _ h => interRho_mono h)
    interRho_le (interRho_le_top hx) hc hcyc
