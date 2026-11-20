module

public import RequestProject.DavisChamberGluing

@[expose] public section

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

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### The sharp intersection formula -/

omit [Fintype V] in
/-- Every coset contains its own representative, so every cell lies in a chamber. -/
theorem inChamber_rep (p : Sph A) : InChamber p.rep p := by
  rw [InChamber, inv_mul_cancel]
  exact Subgroup.one_mem _

/-- **The intersection formula with strict length.**  A cell of `F_x` lies in a strictly shorter
chamber exactly when its mirror type meets `D(x)`. -/
theorem mem_shorter_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, RACG.clen A y < RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  constructor
  · rintro ⟨y, hlt, hy⟩
    refine (mem_earlier_chamber_iff hp).1 ⟨y, ?_, le_of_lt hlt, hy⟩
    intro hxy
    simp_all
  · rintro ⟨s, hs⟩
    obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
    obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A (T := p.spx) (Finset.mem_coe.2 hsσ)
      ((mem_rdescFinset A).1 hsd)
    refine ⟨x * gen A s, h3, ?_⟩
    have h2 : p.rep⁻¹ * (x * gen A s) = (p.rep⁻¹ * x) * (x⁻¹ * (x * gen A s)) := by group
    rw [InChamber, h2]
    exact Subgroup.mul_mem _ hp h1

/-! ### The filtration by length -/

/-- Union of chambers indexed by a set. -/
abbrev chamberUnion {G P : Type*} (C : G → P → Prop) (S : Set G) (p : P) :=
  ∃ y ∈ S, C y p

/-- Chambers of length at most `n`. -/
abbrev chamberBall (A : CommRel V) (n : ℕ) : Set (CayGroup A) := {y | RACG.clen A y ≤ n}

/-- The union of the chambers `F_y` with `ℓ(y) ≤ n`. -/
def Upto (n : ℕ) (p : Sph A) : Prop := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InChamber y p

@[simp] theorem chamberUnion_singleton {G P : Type*} (C : G → P → Prop) (x : G) :
    chamberUnion C {x} = C x := by funext p; simp [chamberUnion]

theorem chamberUnion_insert {G P : Type*} (C : G → P → Prop) (x : G) (S : Set G) :
    chamberUnion C (insert x S) = fun p => chamberUnion C S p ∨ C x p := by
  funext p
  simp [chamberUnion, Set.mem_insert_iff, or_and_right, exists_or, or_comm]

theorem chamberUnion_up {G P : Type*} [Preorder P] {C : G → P → Prop}
    (hC : ∀ y, IsUpperSet (C y : Set P)) {S : Set G} : IsUpperSet (chamberUnion C S : Set P) := by
  rintro p q hpq ⟨y, hy, hp⟩
  exact ⟨y, hy, hC y hpq hp⟩

theorem unmixed_of_upper {P : Type*} [Preorder P] {B C : Set P}
    (hB : IsUpperSet B) (hC : IsUpperSet C) {p q : P} (h : p ≤ q)
    (hp : B p ∨ C p) : (B p ∧ B q) ∨ (C p ∧ C q) :=
  hp.elim (fun hb => Or.inl ⟨hb, hB h hb⟩) (fun hc => Or.inr ⟨hc, hC h hc⟩)

/-- The ball of radius `n` in the word metric is finite. -/
theorem ball_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x ≤ n}.Finite := by
  refine Set.Finite.subset ((List.finite_length_le V n).image (cword A)) ?_
  intro x hx
  obtain ⟨l, hl, hlx⟩ := exists_cword A x
  refine ⟨l, ?_, hlx⟩
  have : l.length = RACG.clen A x := by rw [← hlx, clen_cword A hl]
  simp_all

/-- The elements of length exactly `n` form a finite set. -/
theorem level_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x = n}.Finite :=
  (ball_finite A n).subset (fun _ hx => le_of_eq hx)

/-! ### Adding the chambers of one length level -/

/-- Induction on word-length balls, adjoining a finite layer one chamber at a time. -/
theorem chamberInduction (A : CommRel V) (F : Set (CayGroup A) → Prop)
    (base : F {1})
    (step : ∀ (n : ℕ) (S : Set (CayGroup A)) (x : CayGroup A), x ∉ S →
      RACG.clen A x = n + 1 → (∀ y ∈ S, RACG.clen A y ≤ RACG.clen A x) →
      x ≠ 1 → F (chamberBall A n ∪ S) → F (insert x (chamberBall A n ∪ S))) :
    ∀ n, F (chamberBall A n) := by
  intro n
  induction n with
  | zero => simpa [chamberBall, RACG.clen_eq_zero_iff A] using base
  | succ n ih =>
    have layer (S : Set (CayGroup A)) (hS : S.Finite) (h : ∀ y ∈ S, RACG.clen A y = n + 1) :
        F (chamberBall A n ∪ S) := by
      induction S, hS using Set.Finite.induction_on with
      | empty => simpa using ih
      | @insert x S hxS hS ihS =>
        have hlen := h x (Set.mem_insert _ _)
        have hs  := fun y hy => h y (Set.mem_insert_of_mem _ hy)
        rw [Set.union_insert]
        exact step n S x hxS hlen (fun y hy => (hs y hy).le.trans hlen.ge)
          (by rintro rfl; simp at hlen) (ihS hs)
    have he : chamberBall A (n + 1) = chamberBall A n ∪ {x | RACG.clen A x = n + 1} := by
      ext x
      change RACG.clen A x ≤ n + 1 ↔ RACG.clen A x ≤ n ∨ RACG.clen A x = n + 1
      omega
    rw [he]
    exact layer _ (level_finite A (n + 1)) fun _ hy => hy

/-- An intersection with the next chamber is already present at a strictly shorter level. -/
theorem chamber_overlap {G : Type*} {L : G → ℕ} {C : G → Prop} {J : Prop}
    {x : G} {S : Set G} {n : ℕ} (hx : x ∉ S) (hl : L x = n + 1)
    (hlen : ∀ y ∈ S, L y ≤ L x)
    (hshort : C x → ((∃ y, L y < L x ∧ C y) ↔ J))
    (hearlier : C x → (∃ y, y ≠ x ∧ L y ≤ L x ∧ C y) → J) (hJ : J → C x) :
    (((∃ y, L y ≤ n ∧ C y) ∨ ∃ y ∈ S, C y) ∧ C x) ↔ J := by
  constructor
  · rintro ⟨⟨y, hy, hcy⟩ | ⟨y, hy, hcy⟩, hcx⟩
    · exact (hshort hcx).mp ⟨y, by omega, hcy⟩
    · exact hearlier hcx ⟨y, fun h => hx (h ▸ hy), hlen y hy, hcy⟩
  · intro h
    obtain ⟨y, hy, hcy⟩ := (hshort (hJ h)).mpr h
    exact ⟨Or.inl ⟨y, by omega, hcy⟩, hJ h⟩

theorem upto_overlap {n : ℕ} {S : Set (CayGroup A)} {x : CayGroup A}
    (hx : x ∉ S) (hl : RACG.clen A x = n + 1) (hs : ∀ y ∈ S, RACG.clen A y ≤ RACG.clen A x)
    (p : Sph A) :
    (chamberUnion InChamber (chamberBall A n ∪ S) p ∧ InChamber x p) ↔
      (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
  simpa only [chamberUnion, chamberBall, Set.mem_union, Set.mem_ofPred_eq, or_and_right, exists_or] using
    chamber_overlap (C := fun y => InChamber y p) hx hl hs
    (fun h => (mem_shorter_chamber_iff h).trans (and_iff_right h).symm)
    (fun h hy => ⟨h, (mem_earlier_chamber_iff h).mp hy⟩) And.left

/-- The unions of the first `n` length levels are simply connected. -/
theorem nullIn_upto (A : CommRel V) : ∀ n : ℕ,
    NullIn (Upto (A := A) n) ∧ ConnectedIn (Upto (A := A) n) := by
  apply chamberInduction A (fun S => NullIn (chamberUnion InChamber S) ∧
    ConnectedIn (chamberUnion InChamber S))
  · simpa only [chamberUnion_singleton] using And.intro (nullIn_chamber (A := A) 1) (connectedIn_chamber 1)
  · intro n S x hx hl hs hne h
    rw [chamberUnion_insert]
    exact nullIn_union_chamber hne _ (fun _ _ hpq => chamberUnion_up (C := InChamber) (fun _ _ _ h => inChamber_of_le h) hpq)
      h.1 h.2 (upto_overlap hx hl hs)

/-! ### Simple connectivity of the whole complex -/

/-- A bound on the lengths of the representatives occurring along an edge path. -/
noncomputable def pathBound (l : List ((orderCx (Sph A)).E × Bool)) : ℕ :=
  (l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep)).sum

omit [Fintype V] in
theorem pathIn_upto_pathBound (l : List ((orderCx (Sph A)).E × Bool)) :
    PathIn (Upto (A := A) (pathBound l)) l := by
  intro e he
  have hmem : RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep ∈
      l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep) := List.mem_map_of_mem he
  have hle : RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep ≤ pathBound l :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
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
        obtain ⟨ee, tag⟩ := e
        cases tag with
        | false => rw [hstart]; exact he.2
        | true => rw [hstart]; exact he.1
      exact (nullIn_upto A (pathBound (e :: t))).1 v (e :: t) hv hp hin

/-- The Davis complex is connected. -/
theorem isConnected_davis (A : CommRel V) : IsConnected (orderCx (Sph A)) := by
  intro p q
  obtain ⟨l, hl, -⟩ :=
    (nullIn_upto A (RACG.clen A p.rep + RACG.clen A q.rep)).2 p q
      ⟨p.rep, by omega, inChamber_rep _⟩ ⟨q.rep, by omega, inChamber_rep _⟩
  exact ⟨l, hl⟩

end Davis
end FiniteChains
