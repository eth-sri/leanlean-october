module

public import ADR11.Defs

@[expose] public section

namespace ADR11

open Finset Real Filter Topology

section BasicDefs

variable {X : Type*} [Fintype X] [DecidableEq X]

def restrictClusters (S : Finset X) (H : Finset (Finset X)) : Finset (Finset S) :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

namespace SpeciesTree

noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with A ≠ univ ∧ A.subtype (· ∈ S) = C, σ.length A

noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := mem_image.2 ⟨univ, mem_filter.2 ⟨σ.univ_mem, by simpa using hS⟩, by simp⟩
  singleton_mem x := mem_image.2 ⟨{x.1}, mem_filter.2 ⟨σ.singleton_mem x.1, ⟨x.1, by simp [x.2]⟩⟩,
    by ext ⟨y, _⟩; simp [Subtype.ext_iff]⟩
  nonempty_of_mem C hC := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨y, hy⟩ := (mem_filter.1 hA).2
    exact ⟨⟨y, (mem_inter.1 hy).2⟩, by simp [(mem_inter.1 hy).1]⟩
  laminar C hC D hD := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC; obtain ⟨B, hB, rfl⟩ := mem_image.1 hD
    rcases σ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1 with h | h | h
    · exact Or.inl (subtype_mono h)
    · exact Or.inr (Or.inl (subtype_mono h))
    · exact Or.inr (Or.inr (disjoint_left.2 fun a ha hb =>
        disjoint_left.1 h (mem_subtype.1 ha) (mem_subtype.1 hb)))
  length := σ.restrictLength S
  length_pos C hC hCu := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    exact sum_pos (fun B hB => σ.length_pos B (mem_filter.1 hB).1 (mem_filter.1 hB).2.1)
      ⟨A, mem_filter.2 ⟨(mem_filter.1 hA).1, fun e => hCu (e ▸ subtype_univ _), rfl⟩⟩

end SpeciesTree

def hierarchyOf (C : Finset (Finset X)) : Finset (Finset X) :=
  insert univ (C ∪ univ.image ({·}))

def treeOfClusters (C : Finset (Finset X)) : Finset (Finset X) :=
  unroot (hierarchyOf C)

def caterpillar4 : Finset (Finset (Fin 4)) := hierarchyOf {{0, 1}, {0, 1, 2}}

def balanced5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}
def caterpillar5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}
def pseudocaterpillar5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}

def T5 (i : ℕ) : Finset (Finset (Fin 5)) :=
  let f (a b c : Fin 5) := treeOfClusters {{a, b}, {a, b, c}}
  match i with
  | 1 => f 0 1 2 | 2 => f 0 1 3 | 3 => f 0 1 4 | 4 => f 0 2 1 | 5 => f 0 2 3
  | 6 => f 0 2 4 | 7 => f 0 3 1 | 8 => f 0 3 2 | 9 => f 0 3 4 | 10 => f 0 4 1
  | 11 => f 0 4 2 | 12 => f 0 4 3 | 13 => f 1 2 0 | 14 => f 1 3 0 | 15 => f 1 4 0
  | _ => ∅

noncomputable def u (σ : SpeciesTree (Fin 5)) (i : ℕ) : ℝ :=
  σ.unrootedDist id (T5 i)

end BasicDefs

section Forest

variable {L : Type*} [Fintype L] [DecidableEq L]

def IsForest (F : Finset (Finset L)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def merges (F : Finset (Finset L)) : Finset (Finset (Finset L)) :=
  (roots F).offDiag.image fun p => insert (p.1 ∪ p.2) F

def lineages (F : Finset (Finset L)) : Finset L := F.sup id

theorem mem_roots {F : Finset (Finset L)} {A : Finset L} :
    A ∈ roots F ↔ A ∈ F ∧ ∀ B ∈ F, A ⊆ B → B = A := mem_filter

theorem roots_subset (F : Finset (Finset L)) : roots F ⊆ F := filter_subset _ _

theorem mem_merges {F G : Finset (Finset L)} :
    G ∈ merges F ↔ ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F := by
  simp only [merges, mem_image, mem_offDiag, Prod.exists]
  exact ⟨fun ⟨A, B, ⟨hA, hB, hAB⟩, e⟩ => ⟨A, hA, B, hB, hAB, e.symm⟩,
    fun ⟨A, hA, B, hB, hAB, e⟩ => ⟨A, B, ⟨hA, hB, hAB⟩, e.symm⟩⟩

omit [Fintype L] in
theorem subset_lineages {F : Finset (Finset L)} {A : Finset L} (hA : A ∈ F) : A ⊆ lineages F :=
  le_sup (f := id) hA

theorem exists_mem_roots_subset {F : Finset (Finset L)} {A : Finset L} (hA : A ∈ F) :
    ∃ R ∈ roots F, A ⊆ R :=
  let ⟨R, hAR, hR⟩ := F.exists_le_maximal hA
  ⟨R, mem_roots.2 ⟨hR.1, fun _ hB hRB => le_antisymm (hR.2 hB hRB) hRB⟩, hAR⟩

theorem IsForest.disjoint_of_mem_roots {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : Disjoint A B := by
  rw [mem_roots] at hA hB
  rcases hF.2 A hA.1 B hB.1 with h | h | h
  · exact absurd (hA.2 B hB.1 h).symm hAB
  · exact absurd (hB.2 A hA.1 h) hAB
  · exact h

theorem IsForest.eq_of_mem_roots_of_mem {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L} (hlA : l ∈ A) (hlB : l ∈ B) :
    A = B := by
  by_contra hAB; exact disjoint_left.1 (hF.disjoint_of_mem_roots hA hB hAB) hlA hlB

theorem union_not_mem_of_mem_roots {F : Finset (Finset L)} {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : A ∪ B ∉ F := fun h =>
  hAB ((mem_roots.1 hB).2 A (mem_roots.1 hA).1
    (((mem_roots.1 hA).2 _ h subset_union_left) ▸ subset_union_right))

lemma root_subset_union {F : Finset (Finset L)} (hF : IsForest F)
    {A B C : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hC : C ∈ roots F)
    (h : C ⊆ A ∪ B) : C = A ∨ C = B := by
  obtain ⟨x, hx⟩ := hF.1 C (roots_subset F hC)
  exact (mem_union.1 (h hx)).imp (hF.eq_of_mem_roots_of_mem hC hA hx)
    (hF.eq_of_mem_roots_of_mem hC hB hx)

theorem IsForest.isForest_merge {F : Finset (Finset L)} (hF : IsForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) : IsForest (insert (A ∪ B) F) := by
  have sub_or_disj : ∀ C ∈ F, C ⊆ A ∪ B ∨ Disjoint C (A ∪ B) := fun C hC => by
    obtain ⟨R, hR, hCR⟩ := exists_mem_roots_subset hC
    by_cases hRA : R = A; · exact Or.inl (hCR.trans (hRA ▸ subset_union_left))
    by_cases hRB : R = B; · exact Or.inl (hCR.trans (hRB ▸ subset_union_right))
    exact Or.inr (disjoint_union_right.2 ⟨(hF.disjoint_of_mem_roots hR hA hRA).mono_left hCR,
      (hF.disjoint_of_mem_roots hR hB hRB).mono_left hCR⟩)
  refine ⟨fun C hC => ?_, fun C hC D hD => ?_⟩
  · rcases mem_insert.1 hC with rfl | hC
    · exact (hF.1 A (roots_subset F hA)).mono subset_union_left
    · exact hF.1 C hC
  · rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
    · exact Or.inl subset_rfl
    · exact (sub_or_disj D hD).elim (Or.inr ∘ Or.inl) fun h => Or.inr (Or.inr h.symm)
    · exact (sub_or_disj C hC).elim Or.inl (Or.inr ∘ Or.inr)
    · exact hF.2 C hC D hD

theorem IsForest.of_mem_merges {F G : Finset (Finset L)} (hF : IsForest F) (hG : G ∈ merges F) :
    IsForest G ∧ #(roots G) + 1 = #(roots F) ∧ F ⊆ G ∧ G ≠ F ∧ lineages G = lineages F := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  have hA' := mem_roots.1 hA; have hB' := mem_roots.1 hB
  have hrm : roots (insert (A ∪ B) F) = insert (A ∪ B) (((roots F).erase A).erase B) := by
    ext C; simp only [mem_roots, mem_insert, mem_erase, forall_eq_or_imp]
    by_cases hCU : C = A ∪ B
    · subst hCU; simp only [true_or, iff_true, true_and, imp_true_iff]
      exact fun D hD hUD => absurd (hA'.2 D hD (subset_union_left.trans hUD) ▸
        hB'.2 D hD (subset_union_right.trans hUD)) hAB
    · simp only [hCU, Ne.symm hCU, false_or, imp_false]
      exact ⟨fun ⟨hC, hm, hmax⟩ => ⟨fun e => hm (e ▸ subset_union_right),
          fun e => hm (e ▸ subset_union_left), hC, hmax⟩,
        fun ⟨hCB, hCA, hC, hmax⟩ => ⟨hC, fun hsub =>
          (root_subset_union hF hA hB (mem_roots.2 ⟨hC, hmax⟩) hsub).elim hCA hCB, hmax⟩⟩
  have hU : A ∪ B ∉ ((roots F).erase A).erase B := fun h =>
    union_not_mem_of_mem_roots hA hB hAB (roots_subset F (mem_of_mem_erase (mem_of_mem_erase h)))
  refine ⟨hF.isForest_merge hA hB, ?_, subset_insert _ _,
    fun h => union_not_mem_of_mem_roots hA hB hAB (h ▸ mem_insert_self _ _), ?_⟩
  · rw [hrm, card_insert_of_notMem hU, card_erase_add_one (mem_erase.2 ⟨hAB.symm, hB⟩),
      card_erase_add_one hA]
  · simp only [lineages, sup_insert, id]
    exact union_eq_right.2 (union_subset (subset_lineages hA'.1) (subset_lineages hB'.1))

theorem IsForest.two_mul_sum_merges {F : Finset (Finset L)} (hF : IsForest F)
    (v : Finset (Finset L) → ℝ) :
    2 * ∑ G ∈ merges F, v G = ∑ p ∈ (roots F).offDiag, v (insert (p.1 ∪ p.2) F) := by
  rw [mul_sum, ← sum_fiberwise_of_maps_to (g := fun p : Finset L × Finset L => insert (p.1 ∪ p.2) F)
    (t := merges F) (fun _ h => mem_image_of_mem _ h)]
  refine sum_congr rfl fun G hG => ?_
  obtain ⟨⟨A, B⟩, hp, rfl⟩ := mem_image.1 hG
  obtain ⟨hA, hB, hAB⟩ : A ∈ roots F ∧ B ∈ roots F ∧ A ≠ B := mem_offDiag.1 hp
  rw [show (roots F).offDiag.filter (fun p => insert (p.1 ∪ p.2) F = insert (A ∪ B) F) =
      {(A, B), (B, A)} by
    ext p; rw [mem_filter, mem_offDiag, mem_insert, mem_singleton]
    rcases p with ⟨C, D⟩; simp only [Prod.mk.injEq]
    refine ⟨fun ⟨⟨hC, hD, hCD⟩, hzw⟩ => ?_, fun h => ?_⟩
    · have hU : C ∪ D = A ∪ B := (mem_insert.1 (hzw ▸ mem_insert_self (C ∪ D) F)).resolve_right
        (union_not_mem_of_mem_roots hC hD hCD)
      rcases root_subset_union hF hA hB hC (hU ▸ subset_union_left) with rfl | rfl <;>
        rcases root_subset_union hF hA hB hD (hU ▸ subset_union_right) with rfl | rfl
      exacts [absurd rfl hCD, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, absurd rfl hCD]
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨hA, hB, hAB⟩, rfl⟩
      · exact ⟨⟨hB, hA, hAB.symm⟩, by simp [union_comm]⟩,
    sum_pair (fun h => hAB (Prod.mk.inj h).1)]
  dsimp only; rw [union_comm B A, two_mul]

theorem IsForest.card_merges {F : Finset (Finset L)} (hF : IsForest F) :
    #(merges F) = (#(roots F)).choose 2 := by
  have h1 := hF.two_mul_sum_merges fun _ => (1 : ℝ)
  simp only [sum_const, nsmul_eq_mul, mul_one] at h1
  have hN : 2 * #(merges F) = #(roots F).offDiag := by exact_mod_cast h1
  rw [offDiag_card] at hN
  have h2 : 2 * (#(roots F)).choose 2 = #(roots F) * #(roots F) - #(roots F) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _)),
      Nat.mul_sub_left_distrib, mul_one]
  omega

omit [Fintype L] in
lemma one_apply_ite (F G : Finset (Finset L)) :
    (1 : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) F G = if G = F then 1 else 0 := by
  rw [Matrix.one_apply]; simp [eq_comm]

end Forest

section Kingman

variable {L : Type*} [Fintype L] [DecidableEq L]

theorem mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot; simp only [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨_, ⟨h1, h2⟩, rfl⟩)
    exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩]

theorem compl_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

theorem IsForest.sum_kingmanGenerator_mul {F : Finset (Finset L)} (hF : IsForest F)
    (v : Finset (Finset L) → ℝ) :
    ∑ G, kingmanGenerator F G * v G =
      -((#(roots F)).choose 2 : ℝ) * v F + ∑ G ∈ merges F, v G := by
  have heq : ∀ G, kingmanGenerator F G =
      (if G = F then -((#(roots F)).choose 2 : ℝ) else 0) + (if G ∈ merges F then 1 else 0) := by
    intro G; simp only [kingmanGenerator, ← mem_merges]
    by_cases h1 : G = F
    · subst h1; simp [show G ∉ merges G from fun h => (hF.of_mem_merges h).2.2.2.1 rfl]
    · simp [h1]
  simp only [heq, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_univ,
    ite_true, sum_ite_mem, univ_inter]

theorem isForest_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (A : Finset X) :
    IsForest (sampledForest s A) := by
  refine ⟨fun C hC => ?_, fun C hC D hD => ?_⟩
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hC; exact singleton_nonempty l
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hC; obtain ⟨m, -, rfl⟩ := mem_image.1 hD
    exact if h : l = m then Or.inl (h ▸ subset_rfl) else Or.inr (Or.inr (disjoint_singleton.2 h))

noncomputable def jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0

def deathPow : ℕ → ℕ → ℕ → ℝ
  | 0, k, j => if k = j then 1 else 0
  | m + 1, k, j => ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j)

noncomputable def deathProb (k j : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, t ^ m / (m.factorial : ℝ) * deathPow m k j

theorem jumpMatrix_pow_succ_apply {F : Finset (Finset L)} (hk : 2 ≤ #(roots F))
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ (n + 1)) F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, (jumpMatrix ^ n) F' G := by
  rw [pow_succ', Matrix.mul_apply]
  simp_rw [show ∀ F', jumpMatrix F F' = if F' ∈ merges F then _ else 0 from fun _ => ite_eq_right (by omega),
    ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, mul_sum]

theorem jumpMatrix_pow_of_card_roots_le_one {F : Finset (Finset L)} (hk : #(roots F) ≤ 1)
    (n : ℕ) (G : Finset (Finset L)) :
    (jumpMatrix ^ n) F G = if G = F then 1 else 0 := by
  induction n with
  | zero => rw [pow_zero, one_apply_ite]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [show ∀ H, jumpMatrix F H = if H = F then 1 else 0 from fun _ => ite_eq_left hk,
      ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq', ite_eq_left (mem_univ F), ih]

theorem jumpMatrix_pow_support {F G : Finset (Finset L)} (hF : IsForest F) {n : ℕ}
    (h : (jumpMatrix ^ n) F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧
      #(roots G) = if n < #(roots F) then #(roots F) - n else min (#(roots F)) 1 := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero, one_apply_ite] at h; split_ifs at h with hGF
    · subst hGF; exact ⟨hF, subset_rfl, rfl, by split_ifs <;> omega⟩
    · exact absurd rfl h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := exists_ne_zero_of_sum_ne_zero h
    have hJ := left_ne_zero_of_mul hF'; have hJn := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · obtain rfl : F' = F := by by_contra hne; exact hJ (by simp [jumpMatrix, hk, hne])
      obtain ⟨h1, h2, h3, h4⟩ := ih hF hJn
      exact ⟨h1, h2, h3, by rw [h4]; split_ifs <;> omega⟩
    · have hmem : F' ∈ merges F := by by_contra hne; exact hJ (by simp [jumpMatrix, hk, hne])
      obtain ⟨hF'f, hcard, hsub, -, hlin⟩ := hF.of_mem_merges hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih hF'f hJn
      exact ⟨h1, hsub.trans h2, h3.trans hlin, by rw [h4]; split_ifs <;> omega⟩

theorem deathPow_succ (m k j : ℕ) :
    deathPow (m + 1) k j = ((k.choose 2 : ℕ) : ℝ) * (deathPow m (k - 1) j - deathPow m k j) := rfl

theorem deathPow_eq_zero_of_lt {k j : ℕ} (h : k < j) (m : ℕ) : deathPow m k j = 0 := by
  induction m generalizing k with
  | zero => simp [deathPow, h.ne]
  | succ m ih => rw [deathPow_succ, ih (lt_of_le_of_lt (Nat.sub_le k 1) h), ih h, sub_self, mul_zero]

lemma deathPow_self (m k : ℕ) : deathPow m k k = (-((k.choose 2 : ℕ) : ℝ)) ^ m := by
  induction m with
  | zero => simp [deathPow]
  | succ m ih =>
    rw [deathPow_succ, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [deathPow_eq_zero_of_lt (Nat.sub_lt hk one_pos)]; ring

theorem hasSum_deathProb (k j : ℕ) (t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * deathPow m k j) (deathProb k j t) := by
  have habs : ∀ m k, |deathPow m k j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m := fun m => by
    induction m with
    | zero => intro k; simp only [deathPow, pow_zero]; split_ifs <;> simp
    | succ m ih =>
      intro k; rw [deathPow_succ, abs_mul, pow_succ, abs_of_nonneg (by positivity)]
      have h1 : |deathPow m (k - 1) j| ≤ (2 * ((k.choose 2 : ℕ) : ℝ)) ^ m :=
        (ih (k - 1)).trans (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (Nat.choose_le_choose 2 (k.sub_le 1))) zero_le_two) m)
      nlinarith [ih k, abs_sub (deathPow m (k - 1) j) (deathPow m k j),
        show (0 : ℝ) ≤ (k.choose 2 : ℕ) by positivity]
  refine (Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (|t| * (2 * ((k.choose 2 : ℕ) : ℝ)))) fun m => ?_).hasSum
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, mul_pow, mul_div_right_comm]
  gcongr; exact habs m k

theorem hasSum_exp_mul (x t : ℝ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℝ) * x ^ m) (exp (x * t)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.congr_fun fun m => by rw [mul_pow]; ring

set_option backward.isDefEq.respectTransparency false in
theorem hasSum_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  simpa using Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j

theorem kingmanTransition_apply {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
  have hpow : ∀ (m : ℕ) {F : Finset (Finset L)}, IsForest F →
      (kingmanGenerator ^ m) F G =
        deathPow m (#(roots F)) (#(roots G)) * (jumpMatrix ^ (#(roots F) - #(roots G))) F G := by
    intro m; induction m with
    | zero =>
      intro F _; rw [pow_zero, one_apply_ite]; simp only [deathPow]
      by_cases h : G = F
      · subst h; simp
      · rw [ite_eq_right h]
        split_ifs with hk <;>
          [rw [hk, Nat.sub_self, pow_zero, one_apply_ite, ite_eq_right h, mul_zero]; rw [zero_mul]]
    | succ m ih =>
      intro F hF
      rw [pow_succ', Matrix.mul_apply, hF.sum_kingmanGenerator_mul, ih hF,
        sum_congr rfl fun F' hF' => by
          obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
          rw [ih hF'f, show #(roots F') = #(roots F) - 1 by omega],
        ← mul_sum, deathPow_succ]
      by_cases hk : #(roots F) ≤ 1
      · have hem : merges F = ∅ := eq_empty_of_forall_notMem fun _ hG =>
          let ⟨A, hA, B, hB, hAB, _⟩ := mem_merges.1 hG; hAB (card_le_one.1 hk A hA B hB)
        simp [Nat.choose_eq_zero_of_lt (by omega : #(roots F) < 2), hem]
      · replace hk : 2 ≤ #(roots F) := by omega
        by_cases hjk : #(roots G) < #(roots F)
        · have hstep := jumpMatrix_pow_succ_apply hk (#(roots F) - 1 - #(roots G)) G
          rw [show #(roots F) - 1 - #(roots G) + 1 = #(roots F) - #(roots G) by omega] at hstep
          have hC : (((#(roots F)).choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
          rw [hstep]; field_simp; ring
        · rw [deathPow_eq_zero_of_lt (show #(roots F) - 1 < #(roots G) by omega)]; ring
  exact (hasSum_exp_apply (t • kingmanGenerator (L := L)) F G).unique
    (((hasSum_deathProb (#(roots F)) (#(roots G)) t).mul_right _).congr_fun fun n => by
      rw [smul_pow, Matrix.smul_apply, hpow n hF, smul_eq_mul]; ring)

theorem kingmanTransition_zero : kingmanTransition (L := L) 0 = 1 := by simp [kingmanTransition]

theorem kingmanTransition_add (s t : ℝ) :
    kingmanTransition (L := L) (s + t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition; rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

lemma kingmanTransition_of_card_roots_le_one {F : Finset (Finset L)} (hF : IsForest F)
    (hk : #(roots F) ≤ 1) (t : ℝ) (G : Finset (Finset L)) :
    kingmanTransition t F G = if G = F then 1 else 0 := by
  rw [kingmanTransition_apply hF]
  by_cases hG : G = F
  · subst hG
    have hd : deathProb (#(roots G)) (#(roots G)) t = 1 := by
      simpa [deathProb, deathPow_self, Nat.choose_eq_zero_of_lt (by omega : #(roots G) < 2)] using
        (hasSum_exp_mul 0 t).tsum_eq
    simp [hd]
  · rw [jumpMatrix_pow_of_card_roots_le_one hk, ite_eq_right hG, mul_zero]

theorem deathProb_eq_zero_of_lt {k j : ℕ} (h : k < j) (t : ℝ) : deathProb k j t = 0 := by
  simp [deathProb, deathPow_eq_zero_of_lt h]

lemma absorb_tendsto {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop
      (𝓝 ((jumpMatrix ^ (#(roots F) - 1)) F G)) := by
  rcases Nat.eq_zero_or_pos (#(roots F)) with h0 | hpos
  · rw [h0, Nat.zero_sub, pow_zero, one_apply_ite, show (fun t => kingmanTransition t F G) = _ from
      funext fun t => kingmanTransition_of_card_roots_le_one hF (by omega) t G]
    exact tendsto_const_nhds
  · rw [show (fun t => kingmanTransition t F G) = _ from
      funext fun t => kingmanTransition_apply hF t G]
    set k := #(roots F); set j := #(roots G)
    have htd : Tendsto (deathProb k j) atTop (𝓝 (if j = 1 then 1 else 0)) := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj
      · have hz : ∀ m n, 1 ≤ n → deathPow m n 0 = 0 := fun m => by
          induction m with
          | zero => intro n hn; exact ite_eq_right (by omega)
          | succ m ih =>
            intro n hn; rcases eq_or_lt_of_le hn with rfl | h
            · simp [deathPow]
            · simp [deathPow, ih (n - 1) (by omega), ih n hn]
        simp [hj0, show deathProb k 0 = fun _ => 0 from funext fun _ => by simp [deathProb, hz _ _ hpos]]
      rcases lt_or_ge k j with hkj | hjk
      · rw [show deathProb k j = fun _ => 0 from funext fun t => deathProb_eq_zero_of_lt hkj t,
          ite_eq_right (by omega)]
        exact tendsto_const_nhds
      have hspec : ∀ {k j : ℕ}, 1 ≤ j → j ≤ k → ∃ a : ℕ → ℝ, (j = 1 → a 1 = 1) ∧
          ∀ m, deathPow m k j = ∑ r ∈ Icc j k, a r * (-((r.choose 2 : ℕ) : ℝ)) ^ m := by
        intro k j hj hjk; induction k with
        | zero => omega
        | succ k ih =>
          rcases eq_or_lt_of_le hjk with rfl | hlt
          · exact ⟨fun _ => 1, fun _ => rfl, fun m => by simp [deathPow_self]⟩
          · obtain ⟨b, hb1, hb⟩ := ih (by omega)
            let c : ℕ → ℝ := fun r => ((r.choose 2 : ℕ) : ℝ)
            have hck : ∀ r ∈ Icc j k, c r < c (k + 1) := fun r hr => Nat.cast_lt.2 <|
              calc r.choose 2 < r + r.choose 2 := Nat.lt_add_of_pos_left (hj.trans (mem_Icc.1 hr).1)
                _ = (r + 1).choose 2 := by simp [Nat.choose_succ_succ]
                _ ≤ (k + 1).choose 2 := Nat.choose_le_choose 2 (Nat.succ_le_succ (mem_Icc.1 hr).2)
            let f : ℕ → ℝ := fun r => c (k + 1) / (c (k + 1) - c r) * b r
            let a : ℕ → ℝ := fun r => if r = k + 1 then -∑ s ∈ Icc j k, f s else f r
            refine ⟨a, fun hj1 => ?_, fun m => ?_⟩
            · subst hj1
              simp [a, show k ≠ 0 by omega, f, c,
                div_self ((Nat.cast_ne_zero (R := ℝ)).2 (Nat.choose_pos (by omega : 2 ≤ k + 1)).ne'), hb1 rfl]
            · induction m with
              | zero =>
                simp only [deathPow, hlt.ne', ↓reduceIte, pow_zero, mul_one, sum_Icc_succ_top hjk]
                rw [sum_congr rfl fun r hr => show a r = f r from ite_eq_right (by rw [mem_Icc] at hr; omega)]
                simp [a]
              | succ m ihm =>
                rw [deathPow_succ, Nat.add_sub_cancel, hb m, ihm, sum_Icc_succ_top hjk, sum_Icc_succ_top hjk]
                have h1 : c (k + 1) * ((∑ r ∈ Icc j k, b r * (-c r) ^ m) - ∑ r ∈ Icc j k, a r * (-c r) ^ m) =
                    ∑ r ∈ Icc j k, a r * (-c r) ^ (m + 1) := by
                  rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
                  refine sum_congr rfl fun r hr => ?_
                  have hne : c (k + 1) - c r ≠ 0 := sub_ne_zero.2 (hck r hr).ne'
                  rw [show a r = f r from ite_eq_right (by rw [mem_Icc] at hr; omega), pow_succ]
                  dsimp only [f]; field_simp; ring
                linarith [show a (k + 1) * (-c (k + 1)) ^ (m + 1) = -c (k + 1) * (a (k + 1) * (-c (k + 1)) ^ m) by
                  rw [pow_succ]; ring]
      obtain ⟨a, ha1, ha⟩ := hspec hj hjk
      have hprob : deathProb k j = fun t =>
          ∑ m ∈ Icc j k, exp (-(((m.choose 2 : ℕ) : ℝ) * t)) * a m := funext fun t =>
        (hasSum_deathProb k j t).unique <| by
          convert hasSum_sum (s := Icc j k) (fun m _ => by
            simpa only [neg_mul] using (hasSum_exp_mul (-((m.choose 2 : ℕ) : ℝ)) t).mul_right (a m)) using 1
          ext n; rw [ha n, mul_sum]; exact sum_congr rfl fun m _ => by ring
      rw [hprob, show (if j = 1 then (1 : ℝ) else 0) =
          ∑ m ∈ Icc j k, (if m = 1 then (1 : ℝ) else 0) * a m by
        simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_Icc]
        split_ifs <;> first | exact (ha1 (by omega)).symm | omega | rfl]
      refine tendsto_finsetSum _ fun m hm => Tendsto.mul_const (a m) ?_
      have hm1 := Nat.le_trans hj (mem_Icc.1 hm).1
      split_ifs with h
      · subst h; simp
      · have hp : (0 : ℝ) < ((m.choose 2 : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
        exact tendsto_exp_comp_nhds_zero.mpr
          (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hp tendsto_id))
    have hl := htd.mul_const ((jumpMatrix ^ (k - j)) F G)
    by_cases hG : j = 1
    · simpa [hG] using hl
    · suffices (jumpMatrix ^ (k - 1)) F G = 0 by simpa [hG, this] using hl
      by_contra h
      have hs := (jumpMatrix_pow_support hF h).2.2.2
      rw [ite_eq_left (by omega)] at hs; omega

theorem tendsto_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) := by
  have h := absorb_tendsto hF G
  rwa [show kingmanAbsorption F G = _ from h.limUnder_eq]

theorem kingmanAbsorption_apply {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanAbsorption F G = (jumpMatrix ^ (#(roots F) - 1)) F G :=
  (absorb_tendsto hF G).limUnder_eq

end Kingman

section Contract

variable {ι : Type*} [DecidableEq ι] {L : Type*} [Fintype L] [DecidableEq L]

noncomputable def csum (T : Finset ι) (φ : ι → Finset (Finset L) → ℝ)
    (w : Finset (Finset L) → ℝ) : ℝ :=
  ∑ f : T → Finset (Finset L), (∏ B : T, φ B (f B)) * w (univ.sup f)

lemma csum_congr {T : Finset ι} {φ φ' : ι → Finset (Finset L) → ℝ}
    {w w' : Finset (Finset L) → ℝ} (hφ : ∀ B ∈ T, φ B = φ' B) (hw : ∀ F, w F = w' F) :
    csum T φ w = csum T φ' w' :=
  sum_congr rfl fun f _ => by rw [hw]; exact congrArg (· * _) (prod_congr rfl fun B _ => by rw [hφ B B.2])

lemma csum_singleton (D : ι) (φ : ι → Finset (Finset L) → ℝ) (w : Finset (Finset L) → ℝ) :
    csum {D} φ w = ∑ x, φ D x * w x := by
  unfold csum
  have : Nonempty ↥({D} : Finset ι) := ⟨⟨D, mem_singleton_self D⟩⟩
  rw [← (Equiv.funUnique ({D} : Finset ι) (Finset (Finset L))).symm.sum_comp]
  exact sum_congr rfl fun x _ => congrArg₂ (· * ·)
    ((prod_coe_sort {D} (fun B => φ B x)).trans (prod_singleton _ _))
    (congrArg w (sup_const univ_nonempty x))

lemma csum_union {T₁ T₂ : Finset ι} (h : Disjoint T₁ T₂)
    (φ : ι → Finset (Finset L) → ℝ) (w : Finset (Finset L) → ℝ) :
    csum (T₁ ∪ T₂) φ w = csum T₁ φ (fun F₁ => csum T₂ φ (fun F₂ => w (F₁ ∪ F₂))) := by
  unfold csum
  rw [← (Equiv.piFinsetUnion (fun _ : ι => Finset (Finset L)) h).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun f₁ _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun f₂ _ => ?_
  set g := Equiv.piFinsetUnion (fun _ : ι => Finset (Finset L)) h (f₁, f₂)
  have hl : ∀ (B : ι) (hB : B ∈ T₁), g ⟨B, mem_union_left _ hB⟩ = f₁ ⟨B, hB⟩ :=
    fun B hB => Equiv.piFinsetUnion_left _ h hB _
  have hr : ∀ (B : ι) (hB : B ∈ T₂), g ⟨B, mem_union_right _ hB⟩ = f₂ ⟨B, hB⟩ :=
    fun B hB => Equiv.piFinsetUnion_right _ h hB _
  have hprod : ∏ B : ↥(T₁ ∪ T₂), φ B (g B) = (∏ B : T₁, φ B (f₁ B)) * ∏ B : T₂, φ B (f₂ B) := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union T₁ T₂ h)
      (fun x => φ (Equiv.Finset.union T₁ T₂ h x) (g (Equiv.Finset.union T₁ T₂ h x))) _ (fun _ => rfl),
      Fintype.prod_sum_type]
    exact congrArg₂ (· * ·)
      (prod_congr rfl fun B _ => by rw [Equiv.Finset.union_inl, hl B B.2])
      (prod_congr rfl fun B _ => by rw [Equiv.Finset.union_inr, hr B B.2])
  have hsup : univ.sup g = univ.sup f₁ ∪ univ.sup f₂ := by
    ext C; simp only [mem_union, Finset.mem_sup, mem_univ, true_and]
    exact ⟨fun ⟨⟨B, hB⟩, hC⟩ => (mem_union.1 hB).imp
        (fun h1 => ⟨⟨B, h1⟩, hl B h1 ▸ hC⟩) (fun h2 => ⟨⟨B, h2⟩, hr B h2 ▸ hC⟩),
      fun hc => hc.elim (fun ⟨⟨B, h1⟩, hC⟩ => ⟨⟨B, mem_union_left _ h1⟩, (hl B h1).symm ▸ hC⟩)
        (fun ⟨⟨B, h2⟩, hC⟩ => ⟨⟨B, mem_union_right _ h2⟩, (hr B h2).symm ▸ hC⟩)⟩
  rw [hprod, hsup, mul_assoc]

lemma csum_filter {T : Finset ι} (P : ι → Prop) [DecidablePred P]
    {φ : ι → Finset (Finset L) → ℝ} (h0 : ∀ B ∈ T, ¬ P B → ∀ G, φ B G = if G = ∅ then 1 else 0)
    (w : Finset (Finset L) → ℝ) :
    csum T φ w = csum (T.filter P) φ w := by
  have hz : ∀ {S : Finset ι}, (∀ B ∈ S, ∀ G, φ B G = if G = ∅ then 1 else 0) →
      ∀ u, csum S φ u = u ∅ := by
    intro S; induction S using Finset.induction_on with
    | empty => intro _ u; unfold csum; rw [Fintype.sum_unique]; simp
    | insert D S hDS ih =>
      intro h u; rw [insert_eq, csum_union (disjoint_singleton_left.2 hDS), csum_singleton]
      simp_rw [ih (fun B hB => h B (mem_insert_of_mem hB)), h D (mem_insert_self D S),
        union_empty, ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq']; simp
  conv_lhs => rw [← filter_union_filter_not_eq P T]
  rw [csum_union (disjoint_filter_filter_not T T P)]
  exact csum_congr (fun _ _ => rfl) fun F => by
    rw [hz (fun B hB => h0 B (mem_filter.1 hB).1 (mem_filter.1 hB).2), union_empty]

lemma csum_equiv {ι' : Type*} [DecidableEq ι'] {T : Finset ι} {T' : Finset ι'} (e : T ≃ T')
    {φ : ι → Finset (Finset L) → ℝ} {ψ : ι' → Finset (Finset L) → ℝ}
    (hφ : ∀ B : T, φ B = ψ (e B)) (w : Finset (Finset L) → ℝ) :
    csum T φ w = csum T' ψ w := by
  unfold csum
  let Φ := e.arrowCongr (Equiv.refl (Finset (Finset L)))
  rw [← Φ.sum_comp]
  refine sum_congr rfl fun f _ => ?_
  have hΦ : ∀ B, Φ f (e B) = f B := fun _ => by simp [Φ, Equiv.arrowCongr_apply]
  refine congrArg₂ (· * ·) ?_ (congrArg w ?_)
  · rw [← e.prod_comp]; exact prod_congr rfl fun B _ => by rw [hΦ, hφ]
  · exact le_antisymm
      (Finset.sup_le fun B _ => by rw [← hΦ B]; exact le_sup (mem_univ (e B)))
      (Finset.sup_le fun C _ => le_sup (f := f) (mem_univ (e.symm C)))

end Contract

section MSC

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

theorem nonempty_of_mem_unroot {G : Finset (Finset X)} (hG : IsHierarchy G)
    {A : Finset X} (hA : A ∈ unroot G) : A.Nonempty ∧ A ≠ univ := by
  rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hG.2.2.1 A h1, h2⟩
  · exact ⟨(compl_ne_univ_iff_nonempty A).1 h2, fun e =>
      not_nonempty_empty (by rw [e, compl_univ] at h1; exact hG.2.2.1 _ h1)⟩

@[simp] theorem populationKernel_univ (len : Finset X → ℝ) :
    populationKernel (L := L) len univ = kingmanAbsorption := ite_eq_left rfl

theorem populationKernel_ne_univ (len : Finset X → ℝ) {A : Finset X} (hA : A ≠ univ) :
    populationKernel (L := L) len A = kingmanTransition (len A) := ite_eq_right hA

noncomputable def enteringDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : Finset (Finset L)) : ℝ :=
  csum (childClusters H A) (forestDist H len s) fun S => if S ∪ sampledForest s A = F then 1 else 0

theorem forestDist_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ F, enteringDist H len s A F * populationKernel len A F G := by
  rw [forestDist]; unfold enteringDist csum
  simp_rw [sum_mul]; rw [sum_comm]
  exact sum_congr rfl fun f _ => by simp_rw [mul_assoc, ite_mul, one_mul, zero_mul, ← mul_sum]; rw [sum_ite_eq]; simp

theorem forestDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (G : Finset (Finset L)) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist]
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]; simp

theorem forestDist_of_childClusters_eq_pair {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C : Finset X} (h : childClusters H A = {B, C}) (hBC : B ≠ C)
    (G : Finset (Finset L)) :
    forestDist H len s A G =
      ∑ F₁, ∑ F₂, forestDist H len s B F₁ * forestDist H len s C F₂ *
        populationKernel len A (F₁ ∪ F₂ ∪ sampledForest s A) G := by
  rw [forestDist]; change csum (childClusters H A) (forestDist H len s)
    (fun F => populationKernel len A (F ∪ sampledForest s A) G) = _
  rw [h, insert_eq B {C}, csum_union (disjoint_singleton.2 hBC)]
  simp_rw [csum_singleton, mul_sum, ← mul_assoc]

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A := mem_filter

theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ :=
  filter_eq_empty_iff.2 fun B hB ⟨hBx, _⟩ =>
    not_nonempty_empty (ssubset_singleton_iff.1 hBx ▸ hH.2.2.1 B hB)

theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h
  · exact absurd hC.2.1 (hB.2.2 C hC.1 (lt_of_le_of_ne h hBC))
  · exact absurd hB.2.1 (hC.2.2 B hB.1 (lt_of_le_of_ne h hBC.symm))
  · exact h

omit [Fintype X] in
theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by simp [sampledForest]

omit [Fintype X] in
theorem singleton_mem_sampledForest {s : L → X} {A : Finset X} {l : L} :
    {l} ∈ sampledForest s A ↔ s l ∈ A := by
  simp [mem_sampledForest, singleton_inj, eq_comm]

lemma IsHierarchy.isForest_entering {H : Finset (Finset X)} (hH : IsHierarchy H) {s : L → X}
    {A : Finset X} (f : childClusters H A → Finset (Finset L))
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X))) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) := by
  have hsub : ∀ (B : childClusters H A) (C : Finset L), C ∈ f B → ∀ l ∈ C,
      s l ∈ (B : Finset X) := fun B C hC l hl => by
    have : l ∈ lineages (f B) := by simp only [lineages, Finset.mem_sup, id]; exact ⟨C, hC, hl⟩
    rw [(hf B).2, mem_filter] at this; exact this.2
  have slam : ∀ (l : L) (D : Finset L), {l} ⊆ D ∨ D ⊆ {l} ∨ Disjoint {l} D := fun l D =>
    if h : l ∈ D then Or.inl (singleton_subset_iff.2 h) else Or.inr (Or.inr (disjoint_singleton_left.2 h))
  refine ⟨⟨fun C hC => ?_, fun C hC D hD => ?_⟩, subset_union_right, ?_⟩
  · rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC; exact (hf B).1.1 C hCB
    · exact (isForest_sampledForest s A).1 C hC
  · rcases mem_union.1 hD with hD' | hD'
    · rcases mem_union.1 hC with hC' | hC'
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC'; obtain ⟨B', -, hDB'⟩ := Finset.mem_sup.1 hD'
        by_cases hBB' : B = B'
        · subst hBB'; exact (hf B).1.2 C hCB D hDB'
        · exact Or.inr (Or.inr (disjoint_left.2 fun l hlC hlD =>
            disjoint_left.1 (hH.disjoint_of_mem_childClusters B.2 B'.2 (Subtype.ext_iff.not.1 hBB'))
              (hsub B C hCB l hlC) (hsub B' D hDB' l hlD)))
      · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC'; exact slam l D
    · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hD'
      rcases slam l C with h | h | h; exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h.symm)]
  · ext l; simp only [lineages, Finset.mem_sup, id, mem_filter]
    refine ⟨fun ⟨C, hC, hlC⟩ => ⟨mem_univ _, ?_⟩,
      fun ⟨_, h⟩ => ⟨{l}, mem_union_right _ (singleton_mem_sampledForest.2 h), mem_singleton_self l⟩⟩
    rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
      exact (mem_childClusters.1 B.2).2.1.1 (hsub B C hCB l hlC)
    · obtain ⟨l', hl', rfl⟩ := mem_sampledForest.1 hC; exact mem_singleton.1 hlC ▸ hl'

theorem forestDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = univ.filter (fun l => s l ∈ A) := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hG
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f fun B => by
    have hBm := mem_childClusters.1 B.2
    obtain ⟨h1, -, h3⟩ := ih B hBm.2.1 hBm.1 (prod_ne_zero_iff.1 (left_ne_zero_of_mul hf) B (mem_univ _))
    exact ⟨h1, h3⟩
  have hpk := right_ne_zero_of_mul hf
  unfold populationKernel at hpk; split_ifs at hpk
  · obtain ⟨hG1, hG2, hG3, -⟩ := jumpMatrix_pow_support hF (kingmanAbsorption_apply hF G ▸ hpk)
    exact ⟨hG1, hSF.trans hG2, hG3.trans hLF⟩
  · obtain ⟨hG1, hG2, hG3, -⟩ := jumpMatrix_pow_support hF
      (right_ne_zero_of_mul (kingmanTransition_apply hF _ G ▸ hpk))
    exact ⟨hG1, hSF.trans hG2, hG3.trans hLF⟩

lemma isForest_entering_of_prod {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) {A : Finset X} {f : childClusters H A → Finset (Finset L)}
    (hprod : ∏ B : childClusters H A, forestDist H len s B (f B) ≠ 0) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) :=
  hH.isForest_entering f fun B => by
    obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
      (prod_ne_zero_iff.1 hprod B (mem_univ _))
    exact ⟨h1, h3⟩

theorem forestDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) : ∑ G, forestDist H len s A G = 1 := by
  have ksum : ∀ {F : Finset (Finset L)}, IsForest F → ∀ t, ∑ G, kingmanTransition t F G = 1 := by
    have hrow : ∀ (n : ℕ) {F : Finset (Finset L)}, IsForest F →
        ∑ G, (kingmanGenerator ^ n) F G = if n = 0 then 1 else 0 := fun n => by
      induction n with
      | zero => intro _ _; simp [one_apply_ite]
      | succ n ih =>
        intro F hF
        simp_rw [pow_succ', Matrix.mul_apply]; rw [sum_comm]; simp_rw [← mul_sum]
        rw [hF.sum_kingmanGenerator_mul, ih hF,
          sum_congr rfl fun F' hF' => ih (hF.of_mem_merges hF').1,
          sum_const, hF.card_merges, nsmul_eq_mul, ite_eq_right (Nat.succ_ne_zero n)]; ring
    intro F hF t
    refine (hasSum_sum (s := univ) fun G _ => hasSum_exp_apply (t • kingmanGenerator (L := L)) F G).unique
      ((hasSum_ite_eq 0 (1 : ℝ)).congr_fun fun n => ?_)
    simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_sum, hrow n hF]
    split_ifs with hn <;> [subst hn; skip] <;> simp
  induction A using Finset.strongInduction with
  | H A ih =>
  simp_rw [show ∀ G, forestDist H len s A G = _ from fun G => by rw [forestDist]]
  rw [sum_comm]; simp_rw [← mul_sum]
  have hterm : ∀ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G =
      ∏ B : childClusters H A, forestDist H len s B (f B) := fun f => by
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hprod, zero_mul]
    · have hF := (isForest_entering_of_prod hH len s hprod).1
      rw [show ∑ G, populationKernel len A _ G = 1 by
        unfold populationKernel; split_ifs
        · exact tendsto_nhds_unique (tendsto_finsetSum univ fun G _ => tendsto_kingmanTransition hF G)
            (by simp_rw [ksum hF]; exact tendsto_const_nhds)
        · exact ksum hF _, mul_one]
  simp_rw [hterm, ← Fintype.prod_sum]
  exact prod_eq_one fun B _ => ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1

theorem enteringDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : Finset (Finset L)} (hF : enteringDist H len s A F ≠ 0) :
    IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = univ.filter (fun l => s l ∈ A) := by
  obtain ⟨f, -, hf⟩ := exists_ne_zero_of_sum_ne_zero hF
  dsimp only at hf; split_ifs at hf with hfF
  exacts [hfF ▸ isForest_entering_of_prod hH len s (left_ne_zero_of_mul hf), absurd (mul_zero _) hf]

omit [DecidableEq X] in
theorem IsHierarchy.subset_or_subset_of_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H) {x : X} (hxA : x ∈ A) (hxB : x ∈ B) :
    A ⊆ B ∨ B ⊆ A :=
  (hH.2.2.2 A hA B hB).elim Or.inl fun h => h.elim Or.inr fun hd => absurd hxB (disjoint_left.1 hd hxA)

theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x,
      (singleton_subset_iff.2 hx).ssubset_of_ne fun e => by subst e; simp at hA⟩⟩
  obtain ⟨hBH, hxB, hBA⟩ := mem_filter.1 hB
  exact ⟨B, mem_childClusters.2 ⟨hBH, hBA, fun C hC hBC hCA =>
    not_lt.2 (hmax C (mem_filter.2 ⟨hC, hBC.subset hxB, hCA⟩)) (card_lt_card hBC)⟩, hxB⟩

theorem IsHierarchy.exists_mem_childClusters_superset {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B : Finset X} (hB : B ∈ H) (hBA : B ⊂ A) : ∃ C ∈ childClusters H A, B ⊆ C := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB; obtain ⟨a, haA, haB⟩ := exists_of_ssubset hBA
  obtain ⟨C, hC, hbC⟩ := hH.exists_mem_childClusters
    (one_lt_card.2 ⟨b, hBA.subset hb, a, haA, fun e => haB (e ▸ hb)⟩) (hBA.subset hb)
  refine ⟨C, hC, (hH.subset_or_subset_of_mem (mem_childClusters.1 hC).1 hB hbC hb).elim (fun h => ?_) id⟩
  by_contra hBC; exact (mem_childClusters.1 hC).2.2 B hB (ssubset_of_subset_not_subset h hBC) hBA

theorem IsHierarchy.childClusters_eq_pair {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) (hA : B ∪ C = A) :
    childClusters H A = {B, C} := by
  have hcov : ∀ E ∈ H, E ⊂ A → E ⊆ B ∨ E ⊆ C := fun E hE hEA => by
    rcases hH.2.2.2 E hE B hB with hEB | hBE | hdB
    · exact Or.inl hEB
    · rcases hH.2.2.2 E hE C hC with hEC | hCE | hdC
      · exact Or.inr hEC
      · exact absurd (hA ▸ union_subset hBE hCE) hEA.not_subset
      · exact Or.inl fun x hx => (mem_union.1 (hA ▸ hEA.subset hx)).resolve_right (disjoint_left.1 hdC hx)
    · exact Or.inr fun x hx => (mem_union.1 (hA ▸ hEA.subset hx)).resolve_left (disjoint_left.1 hdB hx)
  have hm : ∀ {U V}, U ∈ H → V ∈ H → Disjoint U V → U ∪ V = A →
      (∀ E ∈ H, E ⊂ A → E ⊆ U ∨ E ⊆ V) → U ∈ childClusters H A := fun {U V} hU hV hUV hUVA hc => by
    obtain ⟨u, hu⟩ := hH.2.2.1 U hU; obtain ⟨v, hv⟩ := hH.2.2.1 V hV
    exact mem_childClusters.2 ⟨hU, (hUVA ▸ subset_union_left).ssubset_of_ne fun e =>
      disjoint_right.1 hUV hv (e ▸ hUVA ▸ mem_union_right U hv),
      fun E hE hUE hEA => (hc E hE hEA).elim hUE.not_subset fun hEV =>
        disjoint_left.1 hUV hu (hEV (hUE.subset hu))⟩
  have hBm := hm hB hC hBC hA hcov
  have hCm := hm hC hB hBC.symm (union_comm B C ▸ hA) fun E hE hEA => (hcov E hE hEA).symm
  ext D; simp only [mem_insert, mem_singleton]
  refine ⟨fun hD => ?_, fun h => h.elim (· ▸ hBm) (· ▸ hCm)⟩
  obtain ⟨hDH, hDA, hmax⟩ := mem_childClusters.1 hD
  exact (hcov D hDH hDA).imp
    (fun h => h.eq_or_ssubset.resolve_right fun hs => hmax B hB hs (mem_childClusters.1 hBm).2.1)
    (fun h => h.eq_or_ssubset.resolve_right fun hs => hmax C hC hs (mem_childClusters.1 hCm).2.1)

theorem forestDist_singleton_of_card_le_one {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {x : X} (hx : #(univ.filter fun l => s l = x) ≤ 1)
    (G : Finset (Finset L)) :
    forestDist H len s {x} G = if G = sampledForest s {x} then 1 else 0 := by
  rw [forestDist_of_childClusters_eq_empty (hH.childClusters_singleton x)]
  have hF := isForest_sampledForest s ({x} : Finset X)
  have hk : #(roots (sampledForest s {x})) ≤ 1 :=
    (card_le_card (roots_subset _)).trans (card_image_le.trans (by simpa using hx))
  by_cases hxu : ({x} : Finset X) = univ
  · rw [populationKernel, ite_eq_left hxu, kingmanAbsorption_apply hF,
      Nat.sub_eq_zero_of_le hk, pow_zero, one_apply_ite]
  · rw [populationKernel_ne_univ _ hxu, kingmanTransition_of_card_roots_le_one hF hk]

theorem forestDist_id_singleton {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (x : X) (G : Finset (Finset X)) :
    forestDist H len id {x} G = if G = {{x}} then 1 else 0 := by
  rw [forestDist_singleton_of_card_le_one hH len (by simp [filter_eq']) G]
  congr 2; ext C; simp [sampledForest, eq_comm]

theorem unrootedDist_nonneg (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ σ.unrootedDist s T := by
  have hkt : ∀ {t : ℝ}, 0 ≤ t → ∀ F G : Finset (Finset L), 0 ≤ kingmanTransition t F G := by
    intro t ht F G
    let c : ℝ := ((Fintype.card (Finset L)).choose 2 : ℕ)
    let P := kingmanGenerator (L := L) + c • 1
    have hP : ∀ H K, 0 ≤ P H K := fun H K => by
      simp only [P, Matrix.add_apply, Matrix.smul_apply, one_apply_ite, smul_eq_mul, kingmanGenerator]
      split_ifs <;> [linarith [show (((#(roots H)).choose 2 : ℕ) : ℝ) ≤ c from
        Nat.cast_le.2 (Nat.choose_le_choose 2 (card_le_univ _))]; norm_num; norm_num]
    have hPn : ∀ n H K, 0 ≤ (P ^ n) H K := fun n => by
      induction n with
      | zero => intro H K; rw [pow_zero, one_apply_ite]; split_ifs <;> norm_num
      | succ n ih => intro H K; rw [pow_succ', Matrix.mul_apply]; exact sum_nonneg fun _ _ => mul_nonneg (hP _ _) (ih _ _)
    show 0 ≤ NormedSpace.exp (t • kingmanGenerator) F G
    rw [show t • kingmanGenerator = t • P + Matrix.diagonal fun _ => -(t * c) by
        ext H K; simp [P, Matrix.diagonal, Matrix.one_apply]; split_ifs <;> ring,
      Matrix.exp_add_of_commute _ _ (by ext H K; simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]),
      Matrix.exp_diagonal, Matrix.mul_diagonal, Pi.exp_def, ← Real.exp_eq_exp_ℝ]
    exact mul_nonneg ((hasSum_exp_apply (t • P) F G).nonneg fun n => by
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (hPn n F G))) (exp_nonneg _)
  have hnn : ∀ {A : Finset X}, A ∈ σ.clusters → ∀ G, 0 ≤ forestDist σ.clusters σ.length s A G := by
    intro A; induction A using Finset.strongInduction with
    | H A ih =>
    intro hA G; rw [forestDist]
    refine sum_nonneg fun f _ => ?_
    by_cases hprod : ∏ B : childClusters σ.clusters A, forestDist σ.clusters σ.length s B (f B) = 0
    · rw [hprod, zero_mul]
    · refine mul_nonneg (prod_nonneg fun B _ => ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _) ?_
      unfold populationKernel; split_ifs with hAu
      · exact ge_of_tendsto (tendsto_kingmanTransition
          (isForest_entering_of_prod σ.isHierarchy σ.length s hprod).1 G)
          (eventually_atTop.2 ⟨0, fun _ ht => hkt ht _ G⟩)
      · exact hkt (σ.length_pos A hA hAu).le _ G
  exact sum_nonneg fun G _ => by split_ifs; exacts [hnn σ.univ_mem G, le_rfl]

theorem unrootedDist_sum (σ : SpeciesTree X) (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  unfold SpeciesTree.unrootedDist; rw [sum_comm]
  simp_rw [sum_ite_eq, mem_univ, ite_true]
  exact forestDist_sum σ.isHierarchy σ.length s σ.univ_mem

end MSC

end ADR11
