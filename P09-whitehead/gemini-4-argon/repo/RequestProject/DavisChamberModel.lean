module

public import RequestProject.MirrorSimplyConnected

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror

universe u

variable {V : Type u} [DecidableEq V]

def Sph (A : CommRel V) : Type u :=
  {p : CayGroup A × Finset V // IsSimplex A p.2 ∧ ∀ s ∈ p.2, ¬ IsRDesc A p.1 s}

variable {A : CommRel V}

def Sph.rep (p : Sph A) : CayGroup A := p.1.1

def Sph.spx (p : Sph A) : Finset V := p.1.2

theorem Sph.isSimplex (p : Sph A) : IsSimplex A p.spx := p.2.1

theorem Sph.no_rdesc (p : Sph A) : ∀ s ∈ p.spx, ¬ IsRDesc A p.rep s := p.2.2

theorem Sph.ext' {p q : Sph A} (hr : p.rep = q.rep) (hs : p.spx = q.spx) : p = q := by
  rcases p with ⟨⟨_, _⟩, _⟩; rcases q with ⟨⟨_, _⟩, _⟩
  cases hr; cases hs; rfl

omit [DecidableEq V] in
theorem commuting_of_isSimplex {σ : Finset V} (h : IsSimplex A σ) : Commuting A (σ : Set V) :=
  fun _ hs _ hr hne => h _ (Finset.mem_coe.1 hs) _ (Finset.mem_coe.1 hr) hne

theorem specialSub_mono {S T : Set V} (h : S ⊆ T) : specialSub A S ≤ specialSub A T :=
  Subgroup.closure_mono (Set.image_mono h)

instance : PartialOrder (Sph A) where
  le p q := p.spx ⊆ q.spx ∧ p.rep⁻¹ * q.rep ∈ specialSub A (q.spx : Set V)
  le_refl p := ⟨Finset.Subset.refl _, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, by
    rw [show p.rep⁻¹ * r.rep = (p.rep⁻¹ * q.rep) * (q.rep⁻¹ * r.rep) by group]
    exact Subgroup.mul_mem _ (specialSub_mono (by exact_mod_cast hqr.1) hpq.2) hqr.2⟩
  le_antisymm p q hpq hqp := by
    have hspx : p.spx = q.spx := Finset.Subset.antisymm hpq.1 hqp.1
    exact Sph.ext' ((existsUnique_shortest_coset A (commuting_of_isSimplex p.isSimplex) p.rep).unique
      ⟨by rw [inv_mul_cancel]; exact Subgroup.one_mem _, fun s hs => p.no_rdesc s (Finset.mem_coe.1 hs)⟩
      ⟨hspx ▸ hpq.2, fun s hs => q.no_rdesc s (hspx ▸ Finset.mem_coe.1 hs)⟩) hspx

def InChamber (x : CayGroup A) (p : Sph A) : Prop :=
  p.rep⁻¹ * x ∈ specialSub A (p.spx : Set V)

def Chamber (A : CommRel V) (x : CayGroup A) : Type u := {p : Sph A // InChamber x p}

instance (x : CayGroup A) : PartialOrder (Chamber A x) := Subtype.partialOrder _

theorem le_of_inChamber {x : CayGroup A} {p q : Sph A} (hp : InChamber x p) (hq : InChamber x q)
    (h : p.spx ⊆ q.spx) : p ≤ q :=
  ⟨h, by
    rw [show p.rep⁻¹ * q.rep = (p.rep⁻¹ * x) * (q.rep⁻¹ * x)⁻¹ by group]
    exact Subgroup.mul_mem _ (specialSub_mono (by exact_mod_cast h) hp) (Subgroup.inv_mem _ hq)⟩

noncomputable def chamberPt (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) : Sph A :=
  ⟨((existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose, σ),
    hσ, fun s hs => (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.2
      s (Finset.mem_coe.2 hs)⟩

@[simp] theorem chamberPt_spx (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) :
    (chamberPt x hσ).spx = σ := rfl

theorem chamberPt_inChamber (x : CayGroup A) {σ : Finset V} (hσ : IsSimplex A σ) :
    InChamber x (chamberPt x hσ) := by
  simpa [InChamber, chamberPt, Sph.rep, Sph.spx, mul_inv_rev] using
    Subgroup.inv_mem _ (existsUnique_shortest_coset A (commuting_of_isSimplex hσ) x).choose_spec.1.1

omit [DecidableEq V] in
theorem isSimplex_empty : IsSimplex A (∅ : Finset V) := fun _ hs => absurd hs (by simp)

noncomputable def chamberApex (x : CayGroup A) : Chamber A x :=
  ⟨chamberPt x (isSimplex_empty (A := A)), chamberPt_inChamber x _⟩

theorem chamber_simplyConnected (x : CayGroup A) :
    Comb.SimplyConnected (Comb.orderCx (Chamber A x)) :=
  Comb.simplyConnected_orderCx (chamberApex x) (fun _ => chamberApex x)
    (fun p => le_of_inChamber (chamberApex x).2 p.2 (by simp [chamberApex]))
    (fun _ => le_rfl) (fun _ => le_rfl)

theorem chamber_isConnected (x : CayGroup A) :
    Comb.IsConnected (Comb.orderCx (Chamber A x)) :=
  Comb.isConnected_orderCx (chamberApex x) (fun _ => chamberApex x)
    (fun p => le_of_inChamber (chamberApex x).2 p.2 (by simp [chamberApex])) (fun _ => le_rfl)

theorem chamber_exists_bdry_eq_of_cycle (x : CayGroup A) {c : Nerve.Ch (Chamber A x)}
    (hc : c ∈ Nerve.Inc (Chamber A x)) (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (Chamber A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle (fun _ => chamberApex x) (chamberApex x)
    (fun _ _ _ => le_rfl) (fun p => le_of_inChamber (chamberApex x).2 p.2 (by simp [chamberApex]))
    (fun _ => le_rfl) hc hcyc

variable [Fintype V]

theorem mem_earlier_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, y ≠ x ∧ RACG.clen A y ≤ RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  have hkey := exists_rdesc_iff_exists_earlier A (commuting_of_isSimplex p.isSimplex) x
  constructor
  · rintro ⟨y, hne, hlen, hy⟩
    obtain ⟨s, hs, hsd⟩ := hkey.1 ⟨y, by
      rw [show x⁻¹ * y = (p.rep⁻¹ * x)⁻¹ * (p.rep⁻¹ * y) by group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hp) hy, hne, hlen⟩
    exact ⟨s, Finset.mem_inter.2 ⟨Finset.mem_coe.1 hs, (mem_rdescFinset A).2 hsd⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
    obtain ⟨y, hxy, hne, hlen⟩ := hkey.2 ⟨s, Finset.mem_coe.2 hsσ, (mem_rdescFinset A).1 hsd⟩
    exact ⟨y, hne, hlen, by
      rw [InChamber, show p.rep⁻¹ * y = (p.rep⁻¹ * x) * (x⁻¹ * y) by group]
      exact Subgroup.mul_mem _ hp hxy⟩

def ChamberInter (A : CommRel V) (x : CayGroup A) : Type u :=
  {p : Sph A // InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty}

instance (x : CayGroup A) : PartialOrder (ChamberInter A x) := Subtype.partialOrder _

variable {x : CayGroup A}

noncomputable def interTop (hx : x ≠ 1) : ChamberInter A x :=
  ⟨chamberPt x (isSimplex_rdescFinset A x), chamberPt_inChamber x _, by
    simpa using rdescFinset_nonempty A hx⟩

noncomputable def interRho (p : ChamberInter A x) : ChamberInter A x :=
  let hsimplex := isSimplex_subset A (Finset.inter_subset_left : p.1.spx ∩ rdescFinset A x ⊆ p.1.spx) p.1.isSimplex
  ⟨chamberPt x hsimplex, chamberPt_inChamber x hsimplex, by
    simpa [Finset.inter_assoc] using p.2.2⟩

theorem interRho_le (p : ChamberInter A x) : interRho p ≤ p :=
  le_of_inChamber (interRho p).2.1 p.2.1 (by simp [interRho])

theorem interRho_le_top (hx : x ≠ 1) (p : ChamberInter A x) : interRho p ≤ interTop hx :=
  le_of_inChamber (interRho p).2.1 (interTop hx).2.1 (by simp [interRho, interTop])

theorem interRho_mono {p q : ChamberInter A x} (h : p ≤ q) : interRho p ≤ interRho q :=
  le_of_inChamber (interRho p).2.1 (interRho q).2.1 (by
    simp only [interRho, chamberPt_spx]
    exact fun _ ha => Finset.mem_inter.2 ⟨h.1 (Finset.mem_inter.1 ha).1, (Finset.mem_inter.1 ha).2⟩)

theorem chamberInter_simplyConnected (hx : x ≠ 1) :
    Comb.SimplyConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.simplyConnected_orderCx (interTop hx) interRho interRho_le (interRho_le_top hx)
    fun h => interRho_mono h

theorem chamberInter_isConnected (hx : x ≠ 1) :
    Comb.IsConnected (Comb.orderCx (ChamberInter A x)) :=
  Comb.isConnected_orderCx (interTop hx) interRho interRho_le (interRho_le_top hx)

theorem chamberInter_exists_bdry_eq_of_cycle (hx : x ≠ 1)
    {c : Nerve.Ch (ChamberInter A x)} (hc : c ∈ Nerve.Inc (ChamberInter A x))
    (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc (ChamberInter A x), Nerve.bdry y = c :=
  Nerve.exists_bdry_eq_of_cycle interRho (interTop hx) (fun _ _ h => interRho_mono h)
    interRho_le (interRho_le_top hx) hc hcyc

end FiniteChains.Davis
