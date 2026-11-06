import Mathlib.Tactic

import RequestProject.RACGGroup

/-!
# Length and descents in a right-angled Coxeter group

Building on the normal form theorem of `RequestProject/RACGGroup.lean`, this file introduces the
group `FiniteChains.RACG.CayGroup` of a right-angled Coxeter system, its word length
`FiniteChains.RACG.clen`, the distance `FiniteChains.RACG.cdist` of its Cayley graph and the
left descents `FiniteChains.RACG.IsDesc`.  The main result is the right-angled descent lemma
`FiniteChains.RACG.desc_two`: two distinct left descents of an element commute.
-/

namespace FiniteChains.RACG



variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The group of the right-angled Coxeter system, realised as permutations of the reduced
traces. -/
def CayGroup  := Subgroup.closure (Set.range (actPerm A))

variable (s : V)
/-- A generator, as an element of the group. -/
noncomputable def gen  : CayGroup A :=
  ⟨actPerm A s, Subgroup.subset_closure ⟨s, rfl⟩⟩

/-- The word length of an element of the group. -/
noncomputable def clen (x : CayGroup A)  := len A (x : Equiv.Perm (Tr A))

variable (l : List V)
/-- The element of the group determined by a word. -/
noncomputable def cword  : CayGroup A :=
  ⟨wordPerm A l, by
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [wordPerm_cons]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, rfl⟩) ih⟩

@[simp] theorem cword_val  : ((cword A l : CayGroup A) : Equiv.Perm (Tr A))
    = wordPerm A l := rfl

@[simp] theorem cword_cons   : cword A (s :: l) = gen A s * cword A l :=
  Subtype.ext (by simp [gen])

@[simp] theorem cword_nil : cword A [] = 1 := Subtype.ext (by simp)

theorem cword_ceq {l m : List V} (h : CEq A.rel l m) : cword A l = cword A m :=
  Subtype.ext (by simpa using wordPerm_ceq A h)

theorem gen_mul_gen  : gen A s * gen A s = 1 :=
  Subtype.ext (by simpa [gen] using actPerm_mul_self A s)

variable {l : List V}
theorem cword_apply_one  (hl : IsRed A.rel l) :
    ((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A) = mkTr A l hl :=
  wordPerm_apply_one A hl

theorem exists_cword (x : CayGroup A) : ∃ l : List V, IsRed A.rel l ∧ cword A l = x := by
  obtain ⟨p, hp⟩ : ∃ l : List V, wordPerm A l = (x : Equiv.Perm (Tr A)) := by
    refine Subgroup.closure_induction (p := fun g _ => ∃ l : List V, wordPerm A l = g)
      ?_ ?_ ?_ ?_ x.2
    · rintro g ⟨s, rfl⟩
      exact ⟨[s], by simp⟩
    · exact ⟨[], by simp⟩
    · rintro g h - - ⟨l, rfl⟩ ⟨m, rfl⟩
      exact ⟨l ++ m, by rw [wordPerm_append]⟩
    · rintro g - ⟨l, rfl⟩
      exact ⟨l.reverse, by rw [wordPerm_reverse]⟩
  obtain ⟨m, hm, -, hmp⟩ := exists_isRed_word A p
  exact ⟨m, hm, Subtype.ext (by rw [cword_val, hmp, hp])⟩

theorem clen_cword  (hl : IsRed A.rel l) : clen A (cword A l) = l.length := by
  show trLen A (((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) = l.length
  rw [cword_apply_one A hl, trLen_mkTr]

variable {x : CayGroup A}
theorem clen_eq_zero_iff  : clen A x = 0 ↔ x = 1 := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := exists_cword A x
    rw [clen_cword A hl] at h
    have  := List.eq_nil_of_length_eq_zero h
    simp [this]
  · rintro rfl
    rfl

@[simp] abbrev clen_one  :=
  (FiniteChains.RACG.clen_eq_zero_iff A).mpr rfl

theorem clen_le_of_cword  {x : CayGroup A} (h : cword A l = x) :
    clen A x ≤ l.length := by
  rw [← h]
  exact len_le_length A l

theorem clen_inv (x : CayGroup A) : clen A x⁻¹ = clen A x := by
  have key : ∀ y : CayGroup A, clen A y⁻¹ ≤ clen A y := by
    intro y
    obtain ⟨l, hl, rfl⟩ := exists_cword A y
    have h1 : cword A l.reverse = (cword A l)⁻¹ :=
      Subtype.ext (by simpa using wordPerm_reverse A l)
    have := clen_le_of_cword A h1
    simpa [clen_cword A hl] using this
  have h1 := key x
  have h2 := key x⁻¹
  simp  at h2
  omega

/-- `s` is a left descent of `x`: multiplying by `s` on the left shortens `x`. -/
def IsDesc (x : CayGroup A) (s : V)  := clen A (gen A s * x) < clen A x

/-- Descents are visible on any reduced word: `s` shortens `x` exactly when it can be moved to
the front of a reduced word for `x`. -/
theorem isDesc_iff_canStart  {l : List V} (hl : IsRed A.rel l)
    (hx : cword A l = x) (s : V) : IsDesc A x s ↔ canStart A.rel s l := by
  subst hx
  by_cases hc : canStart A.rel s l
  · have hpop : gen A s * cword A l = cword A (popStart s l) := by
      have h1  :=
        cword_ceq A (ceq_popStart A.rel_symm hc)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hc
    have hlen  := length_popStart A.rel_symm hc
    simp [IsDesc, hpop, clen_cword A hred, clen_cword A hl, hc]
    omega
  · have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    have hcons  := (cword_cons A s l).symm
    simp only [IsDesc, hcons, clen_cword A hred, clen_cword A hl, hc, iff_false, List.length_cons]
    omega

theorem clen_gen_mul (x : CayGroup A) (s : V) :
    clen A (gen A s * x) + 1 = clen A x ∨ clen A (gen A s * x) = clen A x + 1 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  by_cases hc : canStart A.rel s l
  · left
    have hpop : gen A s * cword A l = cword A (popStart s l) := by
      have h1  :=
        cword_ceq A (ceq_popStart A.rel_symm hc)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hc
    rw [hpop, clen_cword A hred, clen_cword A hl]
    exact length_popStart A.rel_symm hc
  · right
    have hred : IsRed A.rel (s :: l) := ⟨hl, hc⟩
    rw [← cword_cons, clen_cword A hred, clen_cword A hl]
    simp

theorem clen_gen_mul_of_not_desc  {s : V} (h : ¬ IsDesc A x s) :
    clen A (gen A s * x) = clen A x + 1 := by
  have hlt : ¬ clen A (gen A s * x) < clen A x := h
  rcases clen_gen_mul A x s with h' | h'
  · omega
  · exact h'

theorem gen_mul_gen_mul (x : CayGroup A) (s : V) : gen A s * (gen A s * x) = x := by
  rw [← mul_assoc, gen_mul_gen, one_mul]

theorem exists_desc  (hx : x ≠ 1) : ∃ s : V, IsDesc A x s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  match l, hl with
  | [], _ => exact absurd (cword_nil A) hx
  | a :: t, hl =>
      exact ⟨a, (isDesc_iff_canStart A hl rfl a).2 (Or.inl rfl)⟩

variable {s r : V}
/-- **The right-angled descent lemma.**  Two distinct left descents of an element commute, and
the second one is still a descent after the first has been removed. -/
theorem desc_two   (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r ∧ IsDesc A (gen A s * x) r := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs  := (isDesc_iff_canStart A hl rfl s).1 hs
  have hcr  := (isDesc_iff_canStart A hl rfl r).1 hr
  obtain ⟨hrel, hpopr⟩ := canStart_two A.rel_symm hsr hcs hcr
  refine ⟨hrel, ?_⟩
  have hpop : gen A s * cword A l = cword A (popStart s l) := by
    have h1  :=
      cword_ceq A (ceq_popStart A.rel_symm hcs)
    rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
  have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hcs
  rw [hpop]
  exact (isDesc_iff_canStart A hred rfl r).2 hpopr

/-- The left descents of an element pairwise commute. -/
abbrev desc_rel   (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r)  :=
  (FiniteChains.RACG.desc_two A hsr hs hr).left

/-- A descent of a commuting letter survives prefixing. -/
theorem desc_gen_mul_of_rel   (hrel : A.rel s r) (hs : IsDesc A x s) :
    IsDesc A (gen A r * x) s := by
  have hrs : s ≠ r := by rintro rfl; exact A.rel_irrefl s hrel
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs  := (isDesc_iff_canStart A hl rfl s).1 hs
  by_cases hcr : canStart A.rel r l
  · obtain ⟨-, hpops⟩ := canStart_two A.rel_symm (Ne.symm hrs) hcr hcs
    have hpop : gen A r * cword A l = cword A (popStart r l) := by
      have h1  :=
        cword_ceq A (ceq_popStart A.rel_symm hcr)
      rw [h1, cword_cons, ← mul_assoc, gen_mul_gen, one_mul]
    have hred  := isRed_popStart A.rel_irrefl A.rel_symm hl hcr
    rw [hpop]
    exact (isDesc_iff_canStart A hred rfl s).2 hpops
  · have hred : IsRed A.rel (r :: l) := ⟨hl, hcr⟩
    rw [← cword_cons]
    exact (isDesc_iff_canStart A hred rfl s).2 (Or.inr ⟨hrel, hcs⟩)

end FiniteChains.RACG

