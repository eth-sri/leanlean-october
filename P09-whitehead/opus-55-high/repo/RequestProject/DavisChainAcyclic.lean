import RequestProject.DavisSimplyConnected
import RequestProject.NerveSupport


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

namespace FiniteChains.Davis

open RACG Mirror Comb Nerve

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### Local acyclicity, supported on the subposets -/

omit [Fintype V] in
/-- **The chamber `F_x` is acyclic**, as a subgroup of chains of the ambient complex. -/
theorem acyclicIn_chamber (x : CayGroup A) : AcyclicIn (InChamber (A := A) x) := by
  refine Nerve.acyclicIn_of_subtype _ ⟨(chamberApex x).1, (chamberApex x).2⟩ ?_
  intro c hc hcyc
  exact chamber_exists_bdry_eq_of_cycle x hc hcyc

/-- **The attaching subcomplex of the chamber `F_x` is acyclic**, as a subgroup of chains of the
ambient complex. -/
theorem acyclicIn_chamberInter (hx : x ≠ 1) :
    AcyclicIn (fun p => InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
  refine Nerve.acyclicIn_of_subtype _ ⟨(interTop hx).1, (interTop hx).2⟩ ?_
  intro c hc hcyc
  exact chamberInter_exists_bdry_eq_of_cycle hx hc hcyc

/-! ### Adding one chamber -/

/-- **The gluing step for chains.**  Adding one chamber to an upward closed acyclic union whose
intersection with the chamber is the attaching subcomplex keeps the union acyclic. -/
theorem acyclicIn_union_chamber (hx : x ≠ 1) Prev
    (hup : ∀ p q, p ≤ q → Prev p → Prev q)
    (hPrev : AcyclicIn Prev)
    (hinter : ∀ p, (Prev p ∧ InChamber x p) ↔
      (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty)) :
    AcyclicIn (fun p => Prev p ∨ InChamber x p) := by
  refine Nerve.acyclicIn_union_of_unmixed (A := Prev) (B := InChamber (A := A) x)
    (by simp) ?_ hPrev (acyclicIn_chamber x)
    (Nerve.acyclicIn_congr (by simp_all) (acyclicIn_chamberInter hx))
  rintro a b hab (ha | ha) hb
  · tauto
  · exact Or.inr ⟨ha, inChamber_of_le hab ha⟩

/-- Adding, one at a time, finitely many chambers of length `n + 1`. -/
theorem acyclicIn_upto_insert n (hprev : AcyclicIn (Upto (A := A) n)) :
    ∀ (S : Set (CayGroup A)), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      AcyclicIn (fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen
      have hPrevAcyc := ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))
      have hxlen : RACG.clen A x = n + 1 := by simp_all
      have hx1 : x ≠ 1 := by
        intro h
        simp_all
      set Prev : Sph A → Prop := fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p with hPrev
      have hup : ∀ p q, p ≤ q → Prev p → Prev q := by
        rintro p q hpq (h | ⟨y, hy, hyp⟩)
        · exact Or.inl (upto_up hpq h)
        · exact Or.inr ⟨y, hy, inChamber_of_le hpq hyp⟩
      have hinter : ∀ p, (Prev p ∧ InChamber x p) ↔
          (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
        intro p
        constructor
        · rintro ⟨hprev', hpx⟩
          refine ⟨hpx, ?_⟩
          rcases hprev' with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
          · exact (mem_shorter_chamber_iff hpx).1 ⟨y, by omega, hyp⟩
          · refine (mem_earlier_chamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
            · grind
            simp_all
        · rintro ⟨hpx, hne⟩
          obtain ⟨y, hylt, hyp⟩ := (mem_shorter_chamber_iff hpx).2 hne
          exact ⟨Or.inl ⟨y, by omega, hyp⟩, hpx⟩
      have hmain := acyclicIn_union_chamber hx1 Prev hup hPrevAcyc hinter
      grind

/-- **Every cycle supported on the first `n` length levels of chambers is a boundary there.** -/
theorem acyclicIn_upto (A : CommRel V) : ∀ n, AcyclicIn (Upto (A := A) n) := by
  intro n
  induction n with
  | zero =>
      exact Nerve.acyclicIn_congr (fun p => (upto_zero_iff p).symm) (acyclicIn_chamber 1)
  | succ n ih =>
      have h := acyclicIn_upto_insert n ih _
        (level_finite A (n + 1)) (by simp)
      refine Nerve.acyclicIn_congr (fun p => ?_) h
      constructor
      · rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩)
        · exact ⟨y, by omega, hyp⟩
        · exact ⟨y, le_of_eq hy, hyp⟩
      · rintro ⟨y, hy, hyp⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyp⟩
        grind

/-! ### Acyclicity of the whole complex -/

/-- A bound on the lengths of the representatives of the vertices occurring in a chain. -/
noncomputable def chainBound (z : Nerve.Ch (Sph A)) :=
  z.support.sup (fun l => (l.map (RACG.clen A ·.rep)).sum)

omit [Fintype V] in
theorem mem_incOn_upto_chainBound {z : Nerve.Ch (Sph A)} (hz : z ∈ Nerve.Inc (Sph A)) :
    z ∈ Nerve.IncOn (Upto (A := A) (chainBound z)) := by
  rw [Nerve.mem_incOn_iff]
  intro l hl
  refine ⟨(Nerve.mem_inc_iff z).1 hz l hl, ?_⟩
  intro p hp
  refine ⟨p.rep, ?_, inChamber_rep p⟩
  have h1 : RACG.clen A p.rep ≤ (l.map (RACG.clen A ·.rep)).sum :=
    List.single_le_sum (by omega) _ (List.mem_map_of_mem hp)
  refine le_trans h1 ?_
  exact Finset.le_sup (f := fun l => (l.map (RACG.clen A ·.rep)).sum) hl

/-- **`H_*(𝒟) = 0`.**  Every increasing cycle of the augmented simplicial chain complex of the
poset of spherical cosets — in every degree, in particular every two-cycle — is the boundary of
an increasing chain.  For `z ∈ C₂(𝒟)` with `∂z = 0` this produces `v ∈ C₃(𝒟)` with `∂₃ v = z`. -/
theorem exists_bdry_eq_of_cycle_davis (A : CommRel V) {z}
    (hz : z ∈ Nerve.Inc (Sph A)) (hcyc : Nerve.bdry z = 0) :
    ∃ v ∈ Nerve.Inc (Sph A), Nerve.bdry v = z := by
  obtain ⟨v, hv, hdv⟩ :=
    acyclicIn_upto A _ z (mem_incOn_upto_chainBound hz) hcyc
  exact ⟨v, Nerve.incOn_le_inc _ hv, hdv⟩
