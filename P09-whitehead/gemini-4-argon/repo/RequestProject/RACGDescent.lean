module

public import RequestProject.RACGGroup

@[expose] public section

noncomputable section
namespace FiniteChains.RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

def CayGroup : Subgroup (Equiv.Perm (Tr A)) := Subgroup.closure (Set.range (actPerm A))

def gen (s : V) : CayGroup A := ⟨actPerm A s, Subgroup.subset_closure ⟨s, rfl⟩⟩

def clen (x : CayGroup A) : ℕ := len A (x : Equiv.Perm (Tr A))

def cword (l : List V) : CayGroup A :=
  ⟨wordPerm A l, by
    induction l with
    | nil => simp
    | cons a _ ih => rw [wordPerm_cons]; exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, rfl⟩) ih⟩

@[simp] theorem cword_cons (s : V) (l : List V) : cword A (s :: l) = gen A s * cword A l :=
  Subtype.ext (by simp [gen, cword])

@[simp] theorem cword_nil : cword A [] = 1 := Subtype.ext (by simp [cword])

theorem cword_ceq {l m : List V} (h : CEq A.rel l m) : cword A l = cword A m :=
  Subtype.ext (wordPerm_ceq A h)

theorem gen_mul_gen (s : V) : gen A s * gen A s = 1 :=
  Subtype.ext (by simpa [gen] using actPerm_mul_self A s)

theorem exists_cword (x : CayGroup A) : ∃ l : List V, IsRed A.rel l ∧ cword A l = x := by
  obtain ⟨p, hp⟩ : ∃ l : List V, wordPerm A l = (x : Equiv.Perm (Tr A)) := by
    refine Subgroup.closure_induction (p := fun g _ => ∃ l : List V, wordPerm A l = g)
      ?_ ⟨[], by simp⟩ ?_ ?_ x.2
    · rintro _ ⟨s, rfl⟩; exact ⟨[s], by simp⟩
    · rintro _ _ _ _ ⟨l, rfl⟩ ⟨m, rfl⟩; exact ⟨l ++ m, wordPerm_append A l m⟩
    · rintro _ _ ⟨l, rfl⟩; exact ⟨l.reverse, wordPerm_reverse A l⟩
  obtain ⟨m, hm, -, hmp⟩ := exists_isRed_word A p
  exact ⟨m, hm, Subtype.ext (hmp.trans hp)⟩

theorem clen_cword {l : List V} (hl : IsRed A.rel l) : clen A (cword A l) = l.length := by
  show trLen A (wordPerm A l (oneTr A)) = l.length
  rw [wordPerm_apply_one A hl, trLen_mkTr]

theorem clen_eq_zero_iff {x : CayGroup A} : clen A x = 0 ↔ x = 1 := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  rw [clen_cword A hl] at h
  simp [List.eq_nil_of_length_eq_zero h]

@[simp] theorem clen_one : clen A (1 : CayGroup A) = 0 := (clen_eq_zero_iff A).2 rfl

theorem clen_inv (x : CayGroup A) : clen A x⁻¹ = clen A x := by
  have key (y : CayGroup A) : clen A y⁻¹ ≤ clen A y := by
    obtain ⟨l, hl, rfl⟩ := exists_cword A y
    have h1 : cword A l.reverse = (cword A l)⁻¹ := Subtype.ext (wordPerm_reverse A l)
    have h2 : clen A (cword A l.reverse) ≤ l.reverse.length := len_le_length A l.reverse
    simpa [← h1, clen_cword A hl] using h2
  have h1 := key x; have h2 := key x⁻¹; simp only [inv_inv] at h2; omega

def IsDesc (x : CayGroup A) (s : V) : Prop := clen A (gen A s * x) < clen A x

theorem gen_mul_cword_of_canStart {s : V} {l : List V} (hc : canStart A.rel s l) :
    gen A s * cword A l = cword A (popStart s l) := by
  rw [cword_ceq A (ceq_popStart A.rel_symm hc), cword_cons, ← mul_assoc, gen_mul_gen, one_mul]

theorem isDesc_iff_canStart {x : CayGroup A} {l : List V} (hl : IsRed A.rel l)
    (hx : cword A l = x) (s : V) : IsDesc A x s ↔ canStart A.rel s l := by
  subst hx
  by_cases hc : canStart A.rel s l
  · have hlen := length_popStart A.rel_symm hc
    simp only [IsDesc, gen_mul_cword_of_canStart A hc,
      clen_cword A (isRed_popStart A.rel_irrefl A.rel_symm hl hc), clen_cword A hl, hc, iff_true]
    omega
  · simp only [IsDesc, ← cword_cons A s l, clen_cword A (l := s :: l) ⟨hl, hc⟩, clen_cword A hl,
      hc, iff_false, List.length_cons, not_lt]
    omega

theorem clen_gen_mul_of_not_desc {x : CayGroup A} {s : V} (h : ¬ IsDesc A x s) :
    clen A (gen A s * x) = clen A x + 1 := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hc : ¬ canStart A.rel s l := mt (isDesc_iff_canStart A hl rfl s).2 h
  rw [← cword_cons, clen_cword A (l := s :: l) ⟨hl, hc⟩, clen_cword A hl]; rfl

theorem gen_mul_gen_mul (x : CayGroup A) (s : V) : gen A s * (gen A s * x) = x := by
  rw [← mul_assoc, gen_mul_gen, one_mul]

theorem exists_desc {x : CayGroup A} (hx : x ≠ 1) : ∃ s : V, IsDesc A x s := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  match l, hl with
  | [], _ => exact absurd (cword_nil A) hx
  | a :: _, hl => exact ⟨a, (isDesc_iff_canStart A hl rfl a).2 (.inl rfl)⟩

theorem desc_rel {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsDesc A x s)
    (hr : IsDesc A x r) : A.rel s r := by
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  exact (canStart_two A.rel_symm hsr ((isDesc_iff_canStart A hl rfl s).1 hs)
    ((isDesc_iff_canStart A hl rfl r).1 hr)).1

theorem desc_gen_mul_of_rel {x : CayGroup A} {s r : V} (hrel : A.rel s r) (hs : IsDesc A x s) :
    IsDesc A (gen A r * x) s := by
  have hrs : s ≠ r := fun he => A.rel_irrefl s (he ▸ hrel)
  obtain ⟨l, hl, rfl⟩ := exists_cword A x
  have hcs := (isDesc_iff_canStart A hl rfl s).1 hs
  by_cases hcr : canStart A.rel r l
  · rw [gen_mul_cword_of_canStart A hcr]
    exact (isDesc_iff_canStart A (isRed_popStart A.rel_irrefl A.rel_symm hl hcr) rfl s).2
      (canStart_two A.rel_symm (Ne.symm hrs) hcr hcs).2
  · rw [← cword_cons]
    exact (isDesc_iff_canStart A (l := r :: l) ⟨hl, hcr⟩ rfl s).2 (.inr ⟨hrel, hcs⟩)
