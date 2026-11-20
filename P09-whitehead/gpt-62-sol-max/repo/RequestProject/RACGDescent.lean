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

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The group of the right-angled Coxeter system, realised as permutations of the reduced
traces. -/
def CayGroup : Subgroup (Equiv.Perm (Tr A)) := Subgroup.closure (Set.range (actPerm A))

/-- A generator, as an element of the group. -/
noncomputable def gen (s : V) : CayGroup A :=
  ⟨actPerm A s, Subgroup.subset_closure ⟨s, rfl⟩⟩

/-- The word length of an element of the group. -/
noncomputable def clen (x : CayGroup A) : ℕ := len A x

/-- The element of the group determined by a word. -/
noncomputable def cword (l : List V) : CayGroup A :=
  ⟨wordPerm A l, by
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [wordPerm_cons]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, rfl⟩) ih⟩



@[simp] theorem cword_val (l : List V) : ((cword A l : CayGroup A) : Equiv.Perm (Tr A))
    = wordPerm A l := rfl

@[simp] theorem cword_cons (s : V) (l : List V) : cword A (s :: l) = gen A s * cword A l :=
  Subtype.ext rfl

@[simp] theorem cword_nil : cword A [] = 1 := Subtype.ext (by simp)

theorem cword_ceq {l m : List V} (h : CEq A.rel l m) : cword A l = cword A m :=
  Subtype.ext (by simpa using wordPerm_ceq A h)

theorem gen_mul_gen (s : V) : gen A s * gen A s = 1 :=
  Subtype.ext (by simpa [gen] using actPerm_mul_self A s)

/-- Commuting letters act by commuting generators. -/
theorem gen_comm {s r : V} (h : A.rel s r) : gen A s * gen A r = gen A r * gen A s :=
  Subtype.ext (actPerm_mul_comm A h)

theorem gen_mul_cword_popStart {s : V} {l : List V} (h : canStart A.rel s l) :
    gen A s * cword A l = cword A (popStart s l) := by
  rw [cword_ceq A (ceq_popStart A.rel_symm h), cword_cons, ← mul_assoc, gen_mul_gen, one_mul]

theorem cword_apply_one {l : List V} (hl : IsRed A.rel l) :
    ((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A) = mkTr A l hl :=
  wordPerm_apply_one A hl

theorem exists_cword (x : CayGroup A) : ∃ l : List V, IsRed A.rel l ∧ cword A l = x := by
  obtain ⟨p, hp⟩ : ∃ l : List V, wordPerm A l = x := by
    refine Subgroup.closure_induction (p := fun g _ => ∃ l : List V, wordPerm A l = g)
      ?_ ?_ ?_ ?_ x.2
    · rintro g ⟨s, rfl⟩
      exact ⟨[s], by simp⟩
    · tauto
    · rintro g h - - ⟨l, rfl⟩ ⟨m, rfl⟩
      exact ⟨l ++ m, by rw [wordPerm_append]⟩
    · rintro g - ⟨l, rfl⟩
      exact ⟨l.reverse, by rw [wordPerm_reverse]⟩
  obtain ⟨m, hm, -, hmp⟩ := exists_isRed_word A p
  exact ⟨m, hm, Subtype.ext (by simp_all)⟩

theorem clen_cword {l : List V} (hl : IsRed A.rel l) : clen A (cword A l) = l.length := by
  show trLen A (((cword A l : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) = l.length
  rw [cword_apply_one A hl, trLen_mkTr]

theorem clen_eq_zero_iff {x : CayGroup A} : clen A x = 0 ↔ x = 1 := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := exists_cword A x
    rw [clen_cword A hl] at h
    simp_all
  · aesop

@[simp] theorem clen_one : clen A (1 : CayGroup A) = 0 := (clen_eq_zero_iff A).2 rfl

theorem clen_le_of_cword {l : List V} {x : CayGroup A} (h : cword A l = x) :
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
  simp only [inv_inv] at h2
  omega

/-- `s` is a left descent of `x`: multiplying by `s` on the left shortens `x`. -/
def IsDesc (x : CayGroup A) (s : V) : Prop := clen A (gen A s * x) < clen A x

private theorem clen_gen_mul_of_reduced {l : List V} (hl : IsRed A.rel l) (s : V) :
    (canStart A.rel s l → clen A (gen A s * cword A l) + 1 = clen A (cword A l)) ∧
    (¬ canStart A.rel s l → clen A (gen A s * cword A l) = clen A (cword A l) + 1) := by
  constructor <;> intro h
  · rw [gen_mul_cword_popStart A h, clen_cword A (isRed_popStart A.rel_irrefl A.rel_symm hl h),
      clen_cword A hl]
    exact length_popStart A.rel_symm h
  · rw [← cword_cons, clen_cword A (show IsRed A.rel (s :: l) from ⟨hl, h⟩), clen_cword A hl]
    rfl

/-- Descents are visible on any reduced word: `s` shortens `x` exactly when it can be moved to
the front of a reduced word for `x`. -/
theorem isDesc_iff_canStart {x : CayGroup A} {l : List V} (hl : IsRed A.rel l)
    (hx : cword A l = x) (s : V) : IsDesc A x s ↔ canStart A.rel s l := by
  subst x
  have h := clen_gen_mul_of_reduced A hl s
  unfold IsDesc
  by_cases hc : canStart A.rel s l
  · have := h.1 hc
    simp [hc]; omega
  · simp [hc, h.2 hc]

theorem clen_gen_mul (x : CayGroup A) (s : V) :
    clen A (gen A s * x) + 1 = clen A x ∨ clen A (gen A s * x) = clen A x + 1 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have h := clen_gen_mul_of_reduced A hl s
  by_cases hc : canStart A.rel s l
  · exact Or.inl (h.1 hc)
  · exact Or.inr (h.2 hc)

theorem clen_gen_mul_of_not_desc {x : CayGroup A} {s : V} (h : ¬ IsDesc A x s) :
    clen A (gen A s * x) = clen A x + 1 := by
  have hlt : ¬ clen A (gen A s * x) < clen A x := h
  rcases clen_gen_mul A x s with h' | h'
  · omega
  · exact h'

theorem gen_mul_gen_mul (x : CayGroup A) (s : V) : gen A s * (gen A s * x) = x := by
  rw [← mul_assoc, gen_mul_gen, one_mul]

theorem exists_desc {x : CayGroup A} (hx : x ≠ 1) : ∃ s : V, IsDesc A x s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  match l, hl with
  | [], _ => tauto
  | a :: t, hl =>
      exact ⟨a, (isDesc_iff_canStart A hl rfl a).2 (Or.inl rfl)⟩

/-- **The right-angled descent lemma.**  Two distinct left descents of an element commute, and
the second one is still a descent after the first has been removed. -/
theorem desc_two {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r ∧ IsDesc A (gen A s * x) r := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs  := (isDesc_iff_canStart A hl rfl s).1 hs
  have hcr  := (isDesc_iff_canStart A hl rfl r).1 hr
  obtain ⟨hrel, hpopr⟩ := canStart_two A.rel_symm hsr hcs hcr
  refine ⟨hrel, ?_⟩
  have hred := isRed_popStart A.rel_irrefl A.rel_symm hl hcs
  rw [gen_mul_cword_popStart A hcs]
  exact (isDesc_iff_canStart A hred rfl r).2 hpopr

/-- The left descents of an element pairwise commute. -/
theorem desc_rel {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r := (desc_two A hsr hs hr).1

/-- A descent of a commuting letter survives prefixing. -/
theorem desc_gen_mul_of_rel {x : CayGroup A} {s r : V} (hrel : A.rel s r) (hs : IsDesc A x s) :
    IsDesc A (gen A r * x) s := by
  by_cases hr : IsDesc A x r
  · exact (desc_two A (by rintro rfl; exact A.rel_irrefl _ hrel) hr hs).2
  rw [IsDesc, ← mul_assoc, gen_comm A hrel, mul_assoc, clen_gen_mul_of_not_desc A hr]
  have hs' : clen A (gen A s * x) < clen A x := hs
  rcases clen_gen_mul A (gen A s * x) r with h | h <;> omega

end RACG
end FiniteChains
