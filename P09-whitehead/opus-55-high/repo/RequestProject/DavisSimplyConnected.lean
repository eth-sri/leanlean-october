import RequestProject.DavisChamberGluing


/-!
# The Davis complex of a right-angled Coxeter group is simply connected

This file carries out the exhaustion by chambers in the concrete model of
`RequestProject/DavisChamberModel.lean`, using the gluing step of
`RequestProject/DavisChamberGluing.lean`.

* `FiniteChains.Davis.mem_shorter_chamber_iff` — the sharp form of the intersection formula: a
  cell of the chamber `F_x` lies in a *strictly shorter* chamber exactly when its mirror type
  meets the descent set `D(x)`.  (The backward direction produces `y = x s` with `s ∈ D(x)`,
  which is strictly shorter, so ties never have to be broken.)
* `FiniteChains.Davis.Upto n` — the union of the chambers `F_y` with `ℓ(y) ≤ n`.
* `FiniteChains.Davis.nullIn_upto`, `connectedIn_upto` — by induction on `n`, and inside each
  length level by induction on the finite set of elements of that length, every loop inside
  `Upto n` is null-homotopic and `Upto n` is connected.
* `FiniteChains.Davis.simplyConnected_davis` and `isConnected_davis` — the order complex of the
  poset of spherical cosets, i.e. the Davis complex, is connected and simply connected.  Every
  finite edge path meets only finitely many chambers, so it lies in some `Upto n`.
-/

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### The sharp intersection formula -/

omit [Fintype V] in
/-- Every coset contains its own representative, so every cell lies in a chamber. -/
theorem inChamber_rep (p : Sph A) : InChamber p.rep p := by
  simp [InChamber, inv_mul_cancel]

/-- **The intersection formula with strict length.**  A cell of `F_x` lies in a strictly shorter
chamber exactly when its mirror type meets `D(x)`. -/
theorem mem_shorter_chamber_iff (hp : InChamber x p) :
    (∃ y, RACG.clen A y < RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  constructor
  · rintro ⟨y, hlt, hy⟩
    refine (mem_earlier_chamber_iff hp).1 ⟨y, ?_, le_of_lt hlt, hy⟩
    grind
  · rintro ⟨s, hs⟩
    cases' Finset.mem_inter.1 hs with hsσ hsd
    obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A (T := p.spx) (Finset.mem_coe.2 hsσ)
      ((mem_rdescFinset A).1 hsd)
    refine ⟨x * gen A s, h3, ?_⟩
    have h2 : p.rep⁻¹ * (x * gen A s) = (p.rep⁻¹ * x) * (x⁻¹ * (x * gen A s)) := by group
    rw [InChamber, h2]
    aesop

/-! ### The filtration by length -/

/-- The union of the chambers `F_y` with `ℓ(y) ≤ n`. -/
def Upto (n : ℕ) (p : Sph A) := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InChamber y p

omit [Fintype V] in
theorem upto_up {n : ℕ} {p q : Sph A} (hpq : p ≤ q) (hp : Upto n p) : Upto n q := by
  obtain ⟨y, hy, hyp⟩ := hp
  exact ⟨y, hy, inChamber_of_le hpq hyp⟩

omit [Fintype V] in
theorem upto_zero_iff (p : Sph A) : Upto 0 p ↔ InChamber 1 p := by
  constructor
  · rintro ⟨y, hy, hyp⟩
    have := (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 hy)
    simp_all
  · intro h
    exact ⟨1, by simp, h⟩

/-- The ball of radius `n` in the word metric is finite. -/
theorem ball_finite (A : CommRel V) n : {x | RACG.clen A x ≤ n}.Finite := by
  refine Set.Finite.subset ((List.finite_length_le V n).image (cword A)) ?_
  intro x hx
  obtain ⟨l, hl, hlx⟩ := exists_cword A x
  refine ⟨l, ?_, hlx⟩
  have : l.length = RACG.clen A x := by rw [← hlx, clen_cword A hl]
  simp_all

/-- The elements of length exactly `n` form a finite set. -/
theorem level_finite (A : CommRel V) n : {x | RACG.clen A x = n}.Finite :=
  (ball_finite A n).subset (by simp_all)

/-! ### Adding the chambers of one length level -/

/-- Adding, one at a time, finitely many chambers of length `n + 1` to the union of the chambers
of length at most `n`. -/
theorem nullIn_upto_insert n (hnull : NullIn (Upto (A := A) n))
    (hconn : ConnectedIn (Upto (A := A) n)) :
    ∀ (S : Set (CayGroup A)), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      NullIn (fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p) ∧
        ConnectedIn (fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen
      cases' ih (by simp_all) with hprevNull hprevConn
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
        · rintro ⟨hprev, hpx⟩
          refine ⟨hpx, ?_⟩
          rcases hprev with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
          · exact (mem_shorter_chamber_iff hpx).1 ⟨y, by omega, hyp⟩
          · refine (mem_earlier_chamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
            · grind
            simp_all
        · rintro ⟨hpx, hne⟩
          obtain ⟨y, hylt, hyp⟩ := (mem_shorter_chamber_iff hpx).2 hne
          refine ⟨Or.inl ⟨y, ?_, hyp⟩, hpx⟩
          omega
      cases' nullIn_union_chamber hx1 Prev hup hprevNull hprevConn hinter with hN hC
      grind

/-- **Every loop inside the first `n` length levels of chambers is null-homotopic, and these
unions are connected.** -/
theorem nullIn_upto (A : CommRel V) : ∀ n,
    NullIn (Upto (A := A) n) ∧ ConnectedIn (Upto (A := A) n) := by
  intro n
  induction n with
  | zero =>
      constructor
      · exact nullIn_congr (fun p => (upto_zero_iff p).symm) (nullIn_chamber 1)
      · exact connectedIn_congr (fun p => (upto_zero_iff p).symm) (connectedIn_chamber 1)
  | succ n ih =>
      obtain ⟨hN, hC⟩ :=
        nullIn_upto_insert n ih.1 ih.2 _ (level_finite A (n + 1))
          (by simp)
      have hiff : ∀ p,
          (Upto n p ∨ ∃ y ∈ {x : CayGroup A | RACG.clen A x = n + 1}, InChamber y p) ↔ Upto (n + 1) p := by
        intro p
        constructor
        · rintro (⟨y, hy, hyp⟩ | ⟨y, hy, hyp⟩)
          · exact ⟨y, by omega, hyp⟩
          · exact ⟨y, le_of_eq hy, hyp⟩
        · rintro ⟨y, hy, hyp⟩
          rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h | h
          · exact Or.inl ⟨y, by omega, hyp⟩
          grind
      simp_all

/-! ### Simple connectivity of the whole complex -/

/-- A bound on the lengths of the representatives occurring along an edge path. -/
noncomputable def pathBound (l : List ((orderCx (Sph A)).E × Bool)) :=
  (l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep)).sum

omit [Fintype V] in
theorem pathIn_upto_pathBound (l : List ((orderCx (Sph A)).E × Bool)) :
    PathIn (Upto (A := A) (pathBound l)) l := by
  intro e he
  have hmem : RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep ∈
      l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep) := List.mem_map_of_mem he
  have hle : RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep ≤ pathBound l :=
    List.single_le_sum (by omega) _ hmem
  exact ⟨⟨(e.1.1.1).rep, by omega, inChamber_rep _⟩,
    ⟨(e.1.1.2).rep, by omega, inChamber_rep _⟩⟩

/-- **The Davis complex is simply connected.** -/
theorem simplyConnected_davis (A : CommRel V) : SimplyConnected (orderCx (Sph A)) := by
  intro v l hp
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      have hin := pathIn_upto_pathBound (A := A) (e :: t)
      have hv : Upto (pathBound (e :: t)) v := by
        obtain ⟨hstart, -⟩ := hp
        obtain ⟨he, -⟩ := pathIn_of_cons hin
        cases' e with ee tag
        cases tag <;> aesop
      exact (nullIn_upto A _).1 v _ hv hp hin

/-- The Davis complex is connected. -/
theorem isConnected_davis (A : CommRel V) : IsConnected (orderCx (Sph A)) := by
  intro p q
  obtain ⟨l, hl, -⟩ :=
    (nullIn_upto A (RACG.clen A p.rep + RACG.clen A q.rep)).2 p q
      ⟨p.rep, by omega, inChamber_rep _⟩ ⟨q.rep, by omega, inChamber_rep _⟩
  tauto
