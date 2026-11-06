import Mathlib
noncomputable section


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
def cosetLengths (q : FreeGroup α ⧸ Nsub) :=
  {n | ∃ L : List (α × Bool), L.length = n ∧
    (QuotientGroup.mk (FreeGroup.mk L) : FreeGroup α ⧸ Nsub) = q}

/-- The length of a shortest word representing the coset `q`. -/
def clen (q : FreeGroup α ⧸ Nsub) := sInf (cosetLengths Nsub q)

omit [Nsub.Normal] in
theorem cosetLengths_nonempty (q : FreeGroup α ⧸ Nsub) : (cosetLengths Nsub q).Nonempty := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective (s := Nsub) q
  obtain ⟨L, rfl⟩ := w.exists_rep
  exact ⟨L.length, L, rfl, rfl⟩

omit [Nsub.Normal] in
theorem clen_mem (q : FreeGroup α ⧸ Nsub) : clen Nsub q ∈ cosetLengths Nsub q :=
  Nat.sInf_mem (cosetLengths_nonempty Nsub q)

omit [Nsub.Normal] in
theorem clen_le {q : FreeGroup α ⧸ Nsub} {L : List (α × Bool)}
    (h : (QuotientGroup.mk (FreeGroup.mk L) : FreeGroup α ⧸ Nsub) = q) :
    clen Nsub q ≤ L.length :=
  Nat.sInf_le (by tauto)

theorem clen_eq_zero_iff : clen Nsub q = 0 ↔ q = 1 := by
  constructor
  · intro h
    obtain ⟨L, hL, hLq⟩ := clen_mem Nsub q
    rw [h, List.length_eq_zero_iff] at hL
    subst hL
    tauto
  · rintro rfl
    have : clen Nsub (1) ≤ ([]).length :=
      clen_le Nsub (by
        rfl)
    simpa using this

/-- Every nontrivial coset is obtained from a coset of smaller minimal length by
appending one letter. -/
theorem exists_parent (h : clen Nsub q ≠ 0) :
    ∃ py : (FreeGroup α ⧸ Nsub) × (α × Bool),
      clen Nsub py.1 + 1 = clen Nsub q ∧
        py.1 * (QuotientGroup.mk (FreeGroup.mk [py.2])) = q := by
  obtain ⟨L, hL, hLq⟩ := clen_mem Nsub q
  rcases L.eq_nil_or_concat with rfl | ⟨L', y, rfl⟩
  · simp_all
  · rw [List.concat_eq_append] at hL hLq
    refine ⟨⟨QuotientGroup.mk (FreeGroup.mk L'), y⟩, ?_, ?_⟩
    · have hmul : (QuotientGroup.mk (FreeGroup.mk L')) *
          (QuotientGroup.mk (FreeGroup.mk [y])) = q := by
        tauto
      have hup : clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) ≤ L'.length :=
        clen_le Nsub rfl
      have hdown : clen Nsub q ≤ clen Nsub (QuotientGroup.mk (FreeGroup.mk L')) + 1 := by
        obtain ⟨M, hM, hMq⟩ := clen_mem Nsub _
        have : (QuotientGroup.mk (FreeGroup.mk (M ++ [y]))) = q := by
          rw [show FreeGroup.mk (M ++ [y]) = FreeGroup.mk M * FreeGroup.mk [y] from rfl,
            QuotientGroup.mk_mul, hMq, hmul]
        have := clen_le Nsub this
        simp_all
      grind
    tauto

/-- The parent coset and the last letter chosen for a nontrivial coset. -/
def parentData {q : FreeGroup α ⧸ Nsub} (h : clen Nsub q ≠ 0) :=
  (exists_parent Nsub h).choose

theorem parentData_clen (h : clen Nsub q ≠ 0) :
    clen Nsub (parentData Nsub h).1 + 1 = clen Nsub q :=
  (exists_parent Nsub h).choose_spec.1

theorem parentData_mul (h : clen Nsub q ≠ 0) :
    (parentData Nsub h).1 *
      (QuotientGroup.mk (FreeGroup.mk [(parentData Nsub h).2])) = q :=
  (exists_parent Nsub h).choose_spec.2

theorem parentData_clen_lt (h : clen Nsub q ≠ 0) :
    clen Nsub (parentData Nsub h).1 < clen Nsub q := by
  have := parentData_clen Nsub h
  omega

/-- The chosen representative of a coset: the Schreier transversal. -/
def rep (q : FreeGroup α ⧸ Nsub) : FreeGroup α :=
  if h : clen Nsub q = 0 then 1
  else rep (parentData Nsub h).1 * FreeGroup.mk [(parentData Nsub h).2]
termination_by clen Nsub q
decreasing_by exact parentData_clen_lt Nsub h

theorem rep_of_clen_eq_zero (h : clen Nsub q = 0) : rep Nsub q = 1 := by
  rw [rep]
  simp_all

@[simp] theorem rep_one : rep Nsub 1 = 1 :=
  rep_of_clen_eq_zero Nsub ((clen_eq_zero_iff Nsub).2 rfl)

/-- The recursive shape of the representatives: a nontrivial representative is a shorter
representative followed by one letter. -/
theorem rep_mul_letter (h : clen Nsub q ≠ 0) :
    rep Nsub q = rep Nsub (parentData Nsub h).1 * FreeGroup.mk [(parentData Nsub h).2] := by
  rw [rep]
  simp_all

/-- The chosen representative does represent the coset. -/
@[simp] theorem mk_rep q :
    (QuotientGroup.mk (rep Nsub q)) = q := by
  have key : ∀ n, ∀ q, clen Nsub q ≤ n →
      (QuotientGroup.mk (rep Nsub q)) = q := by
    intro n
    induction n with
    | zero =>
        intro q hq
        have h := Nat.le_zero.1 hq
        rw [rep_of_clen_eq_zero Nsub h, (clen_eq_zero_iff Nsub).1 h]
        rfl
    | succ n ih =>
        intro q hq
        by_cases h : clen Nsub q = 0
        · rw [rep_of_clen_eq_zero Nsub h, (clen_eq_zero_iff Nsub).1 h]
          rfl
        · have hlt := parentData_clen Nsub h
          rw [rep_mul_letter Nsub h, QuotientGroup.mk_mul,
            ih _ (by omega), parentData_mul Nsub h]
  exact key _ q le_rfl

/-- The Schreier transversal. -/
def repSet := Set.range (rep Nsub)

theorem rep_mem_repSet q : rep Nsub q ∈ repSet Nsub := by tauto

theorem rep_mk_of_mem (ht : t ∈ repSet Nsub) :
    rep Nsub (QuotientGroup.mk t) = t := by
  obtain ⟨q, rfl⟩ := ht
  simp

/-- Distinct elements of the transversal lie in distinct cosets. -/
theorem eq_of_mk_eq (ht : t ∈ repSet Nsub) (ht' : t' ∈ repSet Nsub)
    (h : (QuotientGroup.mk t : FreeGroup α ⧸ Nsub) = QuotientGroup.mk t') : t = t' := by
  rw [← rep_mk_of_mem Nsub ht, ← rep_mk_of_mem Nsub ht', h]

/-! ### The Schreier generators -/

/-- The Schreier generator attached to a transversal element `t` and a generator `x`. -/
def schreierGen (t : FreeGroup α) (x : α) :=
  t * FreeGroup.of x * (rep Nsub (QuotientGroup.mk (t * FreeGroup.of x)))⁻¹

theorem schreierGen_mem t x : schreierGen Nsub t x ∈ Nsub := by
  simp [← QuotientGroup.eq_one_iff, schreierGen, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep]

/-- The set of Schreier generators. -/
def schreierSet :=
  Set.range fun p : (FreeGroup α ⧸ Nsub) × α => schreierGen Nsub (rep Nsub p.1) p.2

theorem schreierSet_le : Subgroup.closure (schreierSet Nsub) ≤ Nsub := by
  rw [Subgroup.closure_le]
  rintro _ ⟨p, rfl⟩
  exact schreierGen_mem Nsub _ _

/-- The rewriting process: for every word `w`, the element `w · rep(w)⁻¹` is a product of
Schreier generators. -/
theorem mul_inv_rep_mem_closure w :
    w * (rep Nsub (QuotientGroup.mk w))⁻¹ ∈ Subgroup.closure (schreierSet Nsub) := by
  obtain ⟨L, rfl⟩ := w.exists_rep
  induction L using List.reverseRecOn with
  | nil =>
      have h1 : (FreeGroup.mk ([] : List (α × Bool))) = 1 := rfl
      simp_all
  | append_singleton L' y ih =>
      have hsplit : FreeGroup.mk (L' ++ [y]) = FreeGroup.mk L' * FreeGroup.mk [y] := rfl
      set w' : FreeGroup α := FreeGroup.mk L' with hw'
      set t : FreeGroup α := rep Nsub (QuotientGroup.mk w') with ht
      have htmem : t ∈ repSet Nsub := rep_mem_repSet Nsub _
      have hmk : (QuotientGroup.mk (w' * FreeGroup.mk [y]) : FreeGroup α ⧸ Nsub)
          = QuotientGroup.mk (t * FreeGroup.mk [y]) := by
        aesop
      -- the one-letter step
      have hstep : t * FreeGroup.mk [y] *
          (rep Nsub (QuotientGroup.mk (t * FreeGroup.mk [y])))⁻¹
            ∈ Subgroup.closure (schreierSet Nsub) := by
        cases' y with x b
        cases b with
        | true =>
            cases' htmem with q hq
            refine Subgroup.subset_closure ⟨⟨q, x⟩, ?_⟩
            show schreierGen Nsub (rep Nsub q) x = _
            tauto
        | false =>
            have hof : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ :=
              inv_eq_iff_eq_inv.mp rfl
            rw [hof]
            set t' : FreeGroup α := rep Nsub (QuotientGroup.mk (t * (FreeGroup.of x)⁻¹)) with ht'
            have hrep : rep Nsub (QuotientGroup.mk (t' * FreeGroup.of x)) = t := by
              simp_all
            have hgen : schreierGen Nsub t' x = t' * FreeGroup.of x * t⁻¹ := by
              rw [schreierGen, hrep]
            have hmem : schreierGen Nsub t' x ∈ Subgroup.closure (schreierSet Nsub) := by
              refine Subgroup.subset_closure ⟨⟨QuotientGroup.mk (t * (FreeGroup.of x)⁻¹), x⟩, ?_⟩
              rfl
            have : t * (FreeGroup.of x)⁻¹ * t'⁻¹ = (schreierGen Nsub t' x)⁻¹ := by
              rw [hgen]; group
            rw [this]
            exact Subgroup.inv_mem _ hmem
      have hprod : FreeGroup.mk (L' ++ [y]) *
          (rep Nsub (QuotientGroup.mk (FreeGroup.mk (L' ++ [y]))))⁻¹
          = (w' * (rep Nsub (QuotientGroup.mk w'))⁻¹) *
            (t * FreeGroup.mk [y] *
              (rep Nsub (QuotientGroup.mk (t * FreeGroup.mk [y])))⁻¹) := by
        rw [hsplit, hmk, ← ht]
        group
      aesop

/-- **The Schreier generators generate `Ñ`.** -/
theorem closure_schreierGen : Subgroup.closure (schreierSet Nsub) = Nsub := by
  refine le_antisymm (schreierSet_le Nsub) ?_
  intro w hw
  have hmk : (QuotientGroup.mk w : FreeGroup α ⧸ Nsub) = 1 := by simp_all
  have := mul_inv_rep_mem_closure Nsub w
  rwa [hmk, rep_one, inv_one, mul_one] at this
