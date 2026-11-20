module

public import RequestProject.RACGGroup

@[expose] public section

/-!
# Length and descents in a right-angled Coxeter group

Building on the normal form theorem of `RequestProject/RACGGroup.lean`, this file introduces the
group `FiniteChains.RACG.CayGroup` of a right-angled Coxeter system, its word length
`FiniteChains.RACG.clen`, the distance `FiniteChains.RACG.cdist` of its Cayley graph and the
left descents `FiniteChains.RACG.IsDesc`.  The main result is the right-angled descent lemma
`FiniteChains.RACG.desc_two`: two distinct left descents of an element commute.
-/

noncomputable section

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The group of the right-angled Coxeter system, realised as permutations of the reduced
traces. -/
def CayGroup := Subgroup.closure (Set.range (actPerm A))

/-- A generator, as an element of the group. -/
def gen (s : V) : CayGroup A :=
  ⟨actPerm A s, Subgroup.subset_closure ⟨s, rfl⟩⟩

/-- The word length of an element of the group. -/
def clen (x : CayGroup A) := len A x

variable (l : List V)

/-- The element of the group determined by a word. -/
def cword : CayGroup A :=
  ⟨wordPerm A l, by
    induction l with
    | nil => simp
    | cons a t ih =>
        exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, rfl⟩) ih⟩

@[simp] theorem cword_val : ((cword A l : CayGroup A))
    = wordPerm A l := rfl

@[simp] theorem cword_cons (s : V) (l : List V) : cword A (s :: l) = gen A s * cword A l :=
  rfl

@[simp] theorem cword_nil : cword A [] = 1 := rfl

theorem cword_ceq {l m : List V} (h : CEq A.rel l m) : cword A l = cword A m :=
  Subtype.ext (by solve_by_elim [wordPerm_ceq])

theorem gen_mul_gen (s : V) : gen A s * gen A s = 1 :=
  Subtype.ext (by solve_by_elim [actPerm_mul_self])

theorem cword_apply_one {l : List V} (hl : IsRed A.rel l) :
    ((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A) = mkTr A l hl :=
  wordPerm_apply_one A hl

theorem exists_cword (x : CayGroup A) : ∃ l : List V, IsRed A.rel l ∧ cword A l = x := by
  obtain ⟨p, hp⟩ : ∃ l : List V, wordPerm A l = x := by
    refine Subgroup.closure_induction
      ?_ ?_ ?_ ?_ x.2
    · rintro g ⟨s, rfl⟩
      exact ⟨[s], by simp⟩
    · solve_by_elim
    · rintro g h - - ⟨l, rfl⟩ ⟨m, rfl⟩
      exact ⟨l ++ m, by simp [wordPerm_append]⟩
    · rintro g - ⟨l, rfl⟩
      exact ⟨l.reverse, by simp [wordPerm_reverse]⟩
  obtain ⟨m, hm, -, hmp⟩ := exists_isRed_word A p <;> aesop

theorem clen_cword {l : List V} (hl : IsRed A.rel l) : clen A (cword A l) = l.length := by
  show trLen A _ = l.length
  rw [cword_apply_one A hl, trLen_mkTr]

theorem clen_eq_zero_iff {x : CayGroup A} : clen A x = 0 ↔ x = 1 := by
  constructor
  · obtain ⟨l, hl, rfl⟩ := exists_cword A x
    simp_all [clen_cword]
  · solve_by_elim

@[simp] theorem clen_one : clen A 1 = 0 := rfl

theorem clen_le_of_cword {l : List V} {x : CayGroup A} (h : cword A l = x) :
    clen A x ≤ l.length := by
  rw [← h]
  exact len_le_length A l

variable (x : CayGroup A)

theorem clen_inv : clen A x⁻¹ = clen A x := by
  have key : ∀ y : CayGroup A, clen A y⁻¹ ≤ clen A y := by
    intro y
    obtain ⟨l, hl, rfl⟩ := exists_cword A y
    have h1 : cword A l.reverse = (cword A l)⁻¹ :=
      Subtype.ext (by solve_by_elim [wordPerm_reverse])
    have := clen_le_of_cword A h1
    simp_all [clen_cword]
  grind [inv_inv]

/-- `s` is a left descent of `x`: multiplying by `s` on the left shortens `x`. -/
def IsDesc (s : V) := clen A (gen A s * x) < clen A x

/-- Descents are visible on any reduced word: `s` shortens `x` exactly when it can be moved to
the front of a reduced word for `x`. -/
theorem isDesc_iff_canStart {x : CayGroup A} {l : List V} (hl : IsRed A.rel l)
    (hx : cword A l = x) (s : V) : IsDesc A x s ↔ canStart A.rel s l := by
  subst hx
  by_cases hc : canStart A.rel s l
  · have hpop : gen A s * cword A l = cword A (popStart s l) := by
      rw [(cword_ceq A (ceq_popStart A.rel_symm hc)), cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hlen := length_popStart A.rel_symm hc
    simp only [IsDesc, hpop, clen_cword A (isRed_popStart A.rel_irrefl A.rel_symm hl hc), clen_cword A hl, hc, iff_true]
    omega
  · have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    simp only [IsDesc, (cword_cons A s l).symm, clen_cword A hred, clen_cword A hl, hc, iff_false,
      List.length_cons, not_lt]
    omega

theorem clen_gen_mul (x : CayGroup A) (s : V) :
    clen A (gen A s * x) + 1 = clen A x ∨ clen A (gen A s * x) = clen A x + 1 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  by_cases hc : canStart A.rel s l
  · left
    have hpop : gen A s * cword A l = cword A (popStart s l) := by
      rw [(cword_ceq A (ceq_popStart A.rel_symm hc)), cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    rw [hpop, clen_cword A (isRed_popStart A.rel_irrefl A.rel_symm hl hc), clen_cword A hl]
    exact length_popStart A.rel_symm hc
  · right
    have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    rw [← cword_cons, clen_cword A hred, clen_cword A hl]
    simp

theorem clen_gen_mul_of_not_desc {x : CayGroup A} {s : V} (h : ¬ IsDesc A x s) :
    clen A (gen A s * x) = clen A x + 1 := by
  have hlt : ¬ clen A _ < clen A x := h
  rcases clen_gen_mul A x s with h' | h'
  · omega
  · exact h'

theorem gen_mul_gen_mul (x : CayGroup A) (s : V) : gen A s * (gen A s * x) = x := by
  rw [← mul_assoc, gen_mul_gen, one_mul]

variable {x : CayGroup A}

theorem exists_desc (hx : x ≠ 1) : ∃ s : V, IsDesc A x s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  match l, hl with
  | [], _ => simp_all
  | a :: t, hl =>
      exact ⟨a, (isDesc_iff_canStart A hl rfl a).2 (Or.inl rfl)⟩

variable {s r : V}

section

variable (hsr : s ≠ r) (hs : IsDesc A x s) (hr : IsDesc A x r)
include hsr hs hr

/-- **The right-angled descent lemma.**  Two distinct left descents of an element commute, and
the second one is still a descent after the first has been removed. -/
theorem desc_two : A.rel s r ∧ IsDesc A (gen A s * x) r := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs := (isDesc_iff_canStart A hl rfl s).1 hs
  obtain ⟨hrel, hpopr⟩ := canStart_two A.rel_symm hsr hcs ((isDesc_iff_canStart A hl rfl r).1 hr)
  refine ⟨hrel, ?_⟩
  have hpop : gen A s * cword A l = cword A (popStart s l) := by
    rw [(cword_ceq A (ceq_popStart A.rel_symm hcs)), cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
  rw [hpop]
  exact (isDesc_iff_canStart A (isRed_popStart A.rel_irrefl A.rel_symm hl hcs) rfl r).2 hpopr

/-- The left descents of an element pairwise commute. -/
theorem desc_rel : A.rel s r := (desc_two A hsr hs hr).1

end

/-- A descent of a commuting letter survives prefixing. -/
theorem desc_gen_mul_of_rel (hrel : A.rel s r) (hs : IsDesc A x s) :
    IsDesc A (gen A r * x) s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs := (isDesc_iff_canStart A hl rfl s).1 hs
  by_cases hcr : canStart A.rel r l
  · obtain ⟨-, hpops⟩ := canStart_two A.rel_symm (Ne.symm (by rintro rfl; exact A.rel_irrefl s hrel)) hcr hcs
    have hpop : gen A r * cword A l = cword A (popStart r l) := by
      rw [(cword_ceq A (ceq_popStart A.rel_symm hcr)), cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    rw [hpop]
    exact (isDesc_iff_canStart A (isRed_popStart A.rel_irrefl A.rel_symm hl hcr) rfl s).2 hpops
  · have hred : IsRed A.rel (r :: l) := ⟨hl, hcr⟩
    exact (isDesc_iff_canStart A hred rfl s).2 (Or.inr ⟨hrel, hcs⟩)

end RACG
end FiniteChains
