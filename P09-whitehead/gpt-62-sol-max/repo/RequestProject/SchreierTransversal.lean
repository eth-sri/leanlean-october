module

public import Mathlib

@[expose] public section

/-!
# Schreier transversals for a normal subgroup of a free group

Let `F` be the free group on `α` and let `Ñ ◁ F` be a normal subgroup, with quotient
`Q = F/Ñ`.  This file constructs a *Schreier transversal* for `Ñ`: a set `T ⊆ F` of coset
representatives which is closed under taking "prefixes", in the precise sense that every
`t ∈ T` other than `1` is of the form `t = s · y` with `s ∈ T` and `y` a generator or the
inverse of a generator.

The construction is the usual greedy one: a coset `q` is represented by a word of minimal
length, obtained from a minimal word of its "parent" coset by appending one letter.

The two facts proved here are the ones needed for the Magnus/Blanchfield theorem in
`RequestProject/MagnusKernel.lean`:

* `FiniteChains.rep_mul_letter` — the recursive shape of the representatives;
* `FiniteChains.closure_schreierGen` — the Schreier generators
  `s(t, x) = t · x · rep(t x)⁻¹`, for `t` a representative and `x` a generator, generate
  `Ñ` (the generation half of the Reidemeister–Schreier theorem).
-/

namespace FiniteChains

open FreeGroup

variable {α : Type*} (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The lengths of the words representing the coset `q`. -/
def cosetLengths (q : FreeGroup α ⧸ Nsub) : Set ℕ :=
  {n | ∃ L : List (α × Bool), L.length = n ∧
    (QuotientGroup.mk (FreeGroup.mk L)) = q}

/-- The length of a shortest word representing the coset `q`. -/
noncomputable def clen (q : FreeGroup α ⧸ Nsub) : ℕ := sInf (cosetLengths Nsub q)

omit [Nsub.Normal] in
theorem cosetLengths_nonempty (q : FreeGroup α ⧸ Nsub) : (cosetLengths Nsub q).Nonempty := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := Nsub) q
  obtain ⟨L, rfl⟩ := Quot.exists_rep w
  exact ⟨L.length, L, rfl, rfl⟩

omit [Nsub.Normal] in
theorem clen_mem (q : FreeGroup α ⧸ Nsub) : clen Nsub q ∈ cosetLengths Nsub q :=
  Nat.sInf_mem (cosetLengths_nonempty Nsub q)

omit [Nsub.Normal] in
theorem clen_le {q : FreeGroup α ⧸ Nsub} {L : List (α × Bool)}
    (h : (QuotientGroup.mk (FreeGroup.mk L) : FreeGroup α ⧸ Nsub) = q) :
    clen Nsub q ≤ L.length :=
  Nat.sInf_le ⟨L, rfl, h⟩

theorem clen_eq_zero_iff {q : FreeGroup α ⧸ Nsub} : clen Nsub q = 0 ↔ q = 1 := by
  constructor
  · intro h
    obtain ⟨L, hL, hLq⟩ := clen_mem Nsub q
    rw [h, List.length_eq_zero_iff] at hL
    subst hL
    tauto
  · rintro rfl
    have  :=
      clen_le Nsub (by
        show (QuotientGroup.mk 1 : FreeGroup α ⧸ Nsub) = 1
        rfl)
    aesop

/-- Every nontrivial coset is obtained from a coset of smaller minimal length by
appending one letter. -/
theorem exists_parent {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    ∃ py : (FreeGroup α ⧸ Nsub) × (α × Bool),
      clen Nsub py.1 + 1 = clen Nsub q ∧
        py.1 * (QuotientGroup.mk (FreeGroup.mk [py.2]) : FreeGroup α ⧸ Nsub) = q := by
  obtain ⟨L, hL, hLq⟩ := clen_mem Nsub q
  rcases List.eq_nil_or_concat L with rfl | ⟨L', y, rfl⟩
  · tauto
  · rw [List.concat_eq_append] at hL hLq
    refine ⟨⟨QuotientGroup.mk (FreeGroup.mk L'), y⟩, ?_, ?_⟩
    · have hmul : (QuotientGroup.mk (FreeGroup.mk L')) *
          (QuotientGroup.mk (FreeGroup.mk [y])) = q := by
        assumption
      have hup : clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) ≤ L'.length :=
        clen_le Nsub rfl
      have hdown : clen Nsub q ≤ clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) + 1 := by
        obtain ⟨M, hM, hMq⟩ := clen_mem Nsub (QuotientGroup.mk (FreeGroup.mk L'))
        have : (QuotientGroup.mk (FreeGroup.mk (M ++ [y]))) = q := by
          rw [show FreeGroup.mk (M ++ [y]) = FreeGroup.mk M * FreeGroup.mk [y] from rfl,
            QuotientGroup.mk_mul, hMq, hmul]
        have := clen_le Nsub this
        simp_all
      grind
    · assumption

/-- The parent coset and the last letter chosen for a nontrivial coset. -/
noncomputable def parentData {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    (FreeGroup α ⧸ Nsub) × (α × Bool) :=
  (exists_parent Nsub h).choose

theorem parentData_clen {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    clen Nsub (parentData Nsub h).1 + 1 = clen Nsub q :=
  (exists_parent Nsub h).choose_spec.1

theorem parentData_mul {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    (parentData Nsub h).1 *
      (QuotientGroup.mk (FreeGroup.mk [(parentData Nsub h).2]) : FreeGroup α ⧸ Nsub) = q :=
  (exists_parent Nsub h).choose_spec.2

theorem parentData_clen_lt {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    clen Nsub (parentData Nsub h).1 < clen Nsub q := by
  have := parentData_clen Nsub h
  omega

/-- The chosen representative of a coset: the Schreier transversal. -/
noncomputable def rep (q : FreeGroup α ⧸ Nsub) : FreeGroup α :=
  if h : clen Nsub q = 0 then 1
  else rep (parentData Nsub h).1 * FreeGroup.mk [(parentData Nsub h).2]
termination_by clen Nsub q
decreasing_by exact parentData_clen_lt Nsub h

theorem rep_of_clen_eq_zero {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q = 0) : rep Nsub q = 1 := by
  simp [rep, h]

@[simp] theorem rep_one : rep Nsub (1 : FreeGroup α ⧸ Nsub) = 1 :=
  rep_of_clen_eq_zero Nsub ((clen_eq_zero_iff Nsub).2 rfl)

/-- The recursive shape of the representatives: a nontrivial representative is a shorter
representative followed by one letter. -/
theorem rep_mul_letter {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :
    rep Nsub q = rep Nsub (parentData Nsub h).1 * FreeGroup.mk [(parentData Nsub h).2] := by
  rw [rep]
  aesop

/-- The chosen representative does represent the coset. -/
@[simp] theorem mk_rep (q : FreeGroup α ⧸ Nsub) :
    (QuotientGroup.mk (rep Nsub q) : FreeGroup α ⧸ Nsub) = q := by
  have key : ∀ n : ℕ, ∀ q : FreeGroup α ⧸ Nsub, clen Nsub q ≤ n →
      (QuotientGroup.mk (rep Nsub q)) = q := by
    intro n
    induction n with
    | zero =>
        intro q hq
        have h  := Nat.le_zero.1 hq
        simp [(clen_eq_zero_iff Nsub).1 h]
    | succ n ih =>
        intro q hq
        by_cases h : clen Nsub q = 0
        · grind
        · have hlt := parentData_clen Nsub h
          rw [rep_mul_letter Nsub h, QuotientGroup.mk_mul,
            ih (parentData Nsub h).1 (by omega), parentData_mul Nsub h]
  tauto

/-- The Schreier transversal. -/
def repSet : Set (FreeGroup α) := Set.range (rep Nsub)

theorem rep_mem_repSet (q : FreeGroup α ⧸ Nsub) : rep Nsub q ∈ repSet Nsub := ⟨q, rfl⟩

theorem rep_mk_of_mem {t : FreeGroup α} (ht : t ∈ repSet Nsub) :
    rep Nsub (QuotientGroup.mk t) = t := by
  obtain ⟨q, rfl⟩ := ht
  aesop

/-- Distinct elements of the transversal lie in distinct cosets. -/
theorem eq_of_mk_eq {t t' : FreeGroup α} (ht : t ∈ repSet Nsub) (ht' : t' ∈ repSet Nsub)
    (h : (QuotientGroup.mk t : FreeGroup α ⧸ Nsub) = QuotientGroup.mk t') : t = t' := by
  rw [← rep_mk_of_mem Nsub ht, ← rep_mk_of_mem Nsub ht', h]

/-! ### The Schreier generators -/

/-- The Schreier generator attached to a transversal element `t` and a generator `x`. -/
noncomputable def schreierGen (t : FreeGroup α) (x : α) : FreeGroup α :=
  t * FreeGroup.of x * (rep Nsub (QuotientGroup.mk (t * FreeGroup.of x)))⁻¹

theorem schreierGen_mem (t : FreeGroup α) (x : α) : schreierGen Nsub t x ∈ Nsub := by
  simp [← QuotientGroup.eq_one_iff, schreierGen, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep]

/-- The set of Schreier generators. -/
def schreierSet : Set (FreeGroup α) :=
  Set.range fun p : (FreeGroup α ⧸ Nsub) × α => schreierGen Nsub (rep Nsub p.1) p.2

theorem schreierSet_le : Subgroup.closure (schreierSet Nsub) ≤ Nsub := by
  rw [Subgroup.closure_le]
  rintro _ ⟨p, rfl⟩
  exact schreierGen_mem Nsub _ _

/-- The rewriting process: for every word `w`, the element `w · rep(w)⁻¹` is a product of
Schreier generators. -/
theorem mul_inv_rep_mem_closure (w : FreeGroup α) :
    w * (rep Nsub (QuotientGroup.mk w))⁻¹ ∈ Subgroup.closure (schreierSet Nsub) := by
  let H := Subgroup.closure (schreierSet Nsub)
  have gen (q : FreeGroup α ⧸ Nsub) (x : α) :
      rep Nsub q * FreeGroup.of x * (rep Nsub (q * QuotientGroup.mk (FreeGroup.of x)))⁻¹ ∈ H := by
    have h : schreierGen Nsub (rep Nsub q) x ∈ H := Subgroup.subset_closure ⟨(q,x), rfl⟩
    simpa only [schreierGen, QuotientGroup.mk_mul, mk_rep] using h
  have step (q : FreeGroup α ⧸ Nsub) (y : α × Bool) :
      rep Nsub q * FreeGroup.mk [y] * (rep Nsub (q * QuotientGroup.mk (FreeGroup.mk [y])))⁻¹ ∈ H := by
    obtain ⟨x, b⟩ := y
    cases b
    · rw [show FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ from inv_eq_iff_eq_inv.mp rfl,
        QuotientGroup.mk_inv]
      let q' := q * (QuotientGroup.mk (FreeGroup.of x))⁻¹
      have he : q' * QuotientGroup.mk (FreeGroup.of x) = q := by simp [q']
      have h := H.inv_mem (gen q' x)
      rw [he] at h
      change rep Nsub q * (FreeGroup.of x)⁻¹ * (rep Nsub q')⁻¹ ∈ H
      convert h using 1
      group
    · exact gen q x
  obtain ⟨l, rfl⟩ := Quot.exists_rep w
  induction l using List.reverseRecOn with
  | nil =>
      change (1 : FreeGroup α) * (rep Nsub 1)⁻¹ ∈ H
      simp [rep_one]
  | append_singleton l y ih =>
      change FreeGroup.mk l * (rep Nsub (QuotientGroup.mk (FreeGroup.mk l)))⁻¹ ∈ H at ih
      change FreeGroup.mk l * FreeGroup.mk [y] *
        (rep Nsub (QuotientGroup.mk (FreeGroup.mk l * FreeGroup.mk [y])))⁻¹ ∈ H
      rw [QuotientGroup.mk_mul]
      convert H.mul_mem ih (step (QuotientGroup.mk (FreeGroup.mk l)) y) using 1
      group

/-- **The Schreier generators generate `Ñ`.** -/
theorem closure_schreierGen : Subgroup.closure (schreierSet Nsub) = Nsub := by
  refine le_antisymm (schreierSet_le Nsub) ?_
  intro w hw
  have hmk  := (QuotientGroup.eq_one_iff w).2 hw
  have := mul_inv_rep_mem_closure Nsub w
  rwa [hmk, rep_one, inv_one, mul_one] at this

end FiniteChains
