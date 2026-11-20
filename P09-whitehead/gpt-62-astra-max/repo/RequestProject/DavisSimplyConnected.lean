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
  simp [InChamber, inv_mul_cancel]

/-- **The intersection formula with strict length.**  A cell of `F_x` lies in a strictly shorter
chamber exactly when its mirror type meets `D(x)`. -/
theorem mem_shorter_chamber_iff {x : CayGroup A} {p : Sph A} (hp : InChamber x p) :
    (∃ y : CayGroup A, RACG.clen A y < RACG.clen A x ∧ InChamber y p) ↔
      (p.spx ∩ rdescFinset A x).Nonempty := by
  constructor
  · grind [mem_earlier_chamber_iff]
  · rintro ⟨s, hs⟩
    obtain ⟨hsσ, hsd⟩ := Finset.mem_inter.1 hs
    obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A (Finset.mem_coe.2 hsσ)
      ((mem_rdescFinset A).1 hsd)
    refine ⟨x * gen A s, h3, ?_⟩
    have h2 : p.rep⁻¹ * (x * gen A s) = (p.rep⁻¹ * x) * (x⁻¹ * (x * gen A s)) := by group
    rw [InChamber, h2]
    apply Subgroup.mul_mem <;> assumption

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
    simp_all [RACG.clen_eq_zero_iff]
  · intro h
    exact ⟨1, by simp, h⟩

/-- The ball of radius `n` in the word metric is finite. -/
theorem ball_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x ≤ n}.Finite := by
  refine Set.Finite.subset ((List.finite_length_le V n).image (cword A)) ?_
  intro x hx
  obtain ⟨l, hl, hlx⟩ := exists_cword A x
  grind [clen_cword]

/-- The elements of length exactly `n` form a finite set. -/
theorem level_finite (A : CommRel V) (n : ℕ) : {x : CayGroup A | RACG.clen A x = n}.Finite :=
  (ball_finite A n).subset (fun _ hx => le_of_eq hx)

/-! ### Adding the chambers of one length level -/

/-- Induction over the length filtration. At each successor level attach its
finitely many chambers in any order; the intersection with the chambers so
far is exactly the descent mirror. This works for homological properties as
well as for simple connectivity. -/
theorem chamber_induction (C : (Sph A → Prop) → Prop) (base : C (InChamber 1))
    (attach : ∀ {x : CayGroup A}, x ≠ 1 → ∀ Prev : Sph A → Prop,
      (∀ p q, p ≤ q → Prev p → Prev q) → C Prev →
      (∀ p, Prev p ∧ InChamber x p ↔ InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) →
      C (fun p => Prev p ∨ InChamber x p)) (n : ℕ) : C (Upto n) := by
  induction n with
  | zero => rwa [show Upto (A := A) 0 = InChamber 1 from funext fun p => propext (upto_zero_iff p)]
  | succ n ih =>
    have addLevel (S : Set (CayGroup A)) (hS : S.Finite) (hlen : ∀ y ∈ S, RACG.clen A y = n + 1) :
        C (fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p) := by
      induction S, hS using Set.Finite.induction_on with
      | empty => simpa using ih
      | @insert x S hxS _ ihS =>
          have hxlen := hlen x (Set.mem_insert _ _)
          have hx1 : x ≠ 1 := by
            intro h
            rw [h] at hxlen
            simp at hxlen
          set Prev : Sph A → Prop := fun p => Upto n p ∨ ∃ y ∈ S, InChamber y p with hPrev
          have hup : ∀ p q : Sph A, p ≤ q → Prev p → Prev q := by
            rintro p q hpq (h | ⟨y, hy, hyp⟩)
            · solve_by_elim [upto_up]
            · exact Or.inr ⟨y, hy, inChamber_of_le hpq hyp⟩
          have hinter : ∀ p : Sph A, (Prev p ∧ InChamber x p) ↔
              (InChamber x p ∧ (p.spx ∩ rdescFinset A x).Nonempty) := by
            intro p
            constructor
            · rintro ⟨hprev, hpx⟩
              refine ⟨hpx, ?_⟩
              rcases hprev with ⟨y, hy, hyp⟩ | ⟨y, hyS, hyp⟩
              · exact (mem_shorter_chamber_iff hpx).1 ⟨y, by omega, hyp⟩
              · refine (mem_earlier_chamber_iff hpx).1 ⟨y, ?_, ?_, hyp⟩
                · grind
                · grind
            · rintro ⟨hpx, hne⟩
              obtain ⟨y, hylt, hyp⟩ := (mem_shorter_chamber_iff hpx).2 hne
              refine ⟨Or.inl ⟨y, ?_, hyp⟩, hpx⟩
              omega
          have h := attach hx1 Prev hup (ihS (fun y hy => hlen y (Set.mem_insert_of_mem _ hy))) hinter
          convert h using 1
          funext p
          simp [Prev, or_assoc, or_left_comm, or_comm]
    have h := addLevel _ (level_finite A (n + 1)) (fun _ hy => hy)
    convert h using 1
    funext p
    simp only [Upto, Set.mem_ofPred_eq, Nat.le_succ_iff]
    grind

/-- Each length sublevel is connected and every loop in it is null. -/
theorem nullIn_upto (A : CommRel V) (n : ℕ) :
    NullIn (Upto (A := A) n) ∧ ConnectedIn (Upto (A := A) n) :=
  chamber_induction (fun S => NullIn S ∧ ConnectedIn S) ⟨nullIn_chamber 1, connectedIn_chamber 1⟩
    (fun hx S hup h => nullIn_union_chamber hx S hup h.1 h.2) n

/-! ### Simple connectivity of the whole complex -/

variable (l : List ((orderCx (Sph A)).E × Bool))

/-- A bound on the lengths of the representatives occurring along an edge path. -/
noncomputable def pathBound :=
  (l.map (fun e => RACG.clen A (e.1.1.1).rep + RACG.clen A (e.1.1.2).rep)).sum

omit [Fintype V] in
theorem pathIn_upto_pathBound :
    PathIn (Upto (A := A) (pathBound l)) l := by
  intro e he
  have hle : RACG.clen A _ + RACG.clen A _ ≤ pathBound l :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem he)
  exact ⟨⟨(e.1.1.1).rep, by omega, inChamber_rep _⟩,
    ⟨(e.1.1.2).rep, by omega, inChamber_rep _⟩⟩

variable (A : CommRel V)

/-- **The Davis complex is simply connected.** -/
theorem simplyConnected_davis : SimplyConnected (orderCx (Sph A)) := by
  intro v l hp
  cases l with
  | nil => exact Htpy.refl _
  | cons e t =>
      have hin := pathIn_upto_pathBound (e :: t)
      have hv : Upto (pathBound (e :: t)) v := by
        obtain ⟨hstart, -⟩ := hp
        obtain ⟨he, -⟩ := pathIn_of_cons hin
        obtain ⟨ee, tag⟩ := e
        cases tag with
        | false => aesop
        | true => aesop
      exact (nullIn_upto A _).1 v _ hv hp hin

/-- The Davis complex is connected. -/
theorem isConnected_davis : IsConnected (orderCx (Sph A)) := by
  intro p q
  obtain ⟨l, hl, -⟩ :=
    (nullIn_upto A (RACG.clen A p.rep + RACG.clen A q.rep)).2 p q
      ⟨p.rep, by omega, inChamber_rep _⟩ ⟨q.rep, by omega, inChamber_rep _⟩
  solve_by_elim

end Davis
end FiniteChains
