module

public import Mathlib

/-!
# Cubical simplices and boundary incidence

The grid simplices of a labelled cube are classified by their boundary coordinates.
Coordinate-change counts order their vertices and determine the number of parent simplices,
providing the incidence identities used in the cubical Sperner argument.
-/

@[expose] public section

open Classical

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := Pi.instFintype

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

section
variable (m:ℕ )
def simplex (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}
end

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

section
variable (I : Fin (n1 +1) → SC.G)
def case_A  := ∃ j, ∀ k, I k j = 0

def case_B  := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C  :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D  := ∀ j, ∀ q, ∃ k,I k j ≠ q

theorem one_of_ABCD  :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  · apply Or.inl
    use j
    rwa [← q0]
  by_cases qp : q = Fin.last SC.p
  · apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  suffices h3 : case_C SC I by
    simp_all
  use j, q
end

section simplex_properties

section
variable {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
include hs
theorem monotone_1_of_simplex (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by
  intro j
  let f := fun i ↦ I i j
  suffices h3 : Monotone f by tauto
  rw [(@Fin.monotone_iff_le_succ m _ _ f)]
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp at h3
  convert! h3 <;> ext <;> simp [Nat.mod_eq_of_lt]

theorem monotone_2_of_simplex  :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j :=
  ⟨monotone_1_of_simplex SC I hs i1 i2, fun h1 => le_of_not_gt fun h2 => h2.ne' (hs.1 (funext fun j =>
    le_antisymm (h1 j) (monotone_1_of_simplex SC I hs i2 i1 h2.le j)))⟩
end

theorem last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by
  cases m
  simp
  exact (hs.2 0 (by omega) j).2

theorem le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by
  apply le_trans _ (le_trans (last_of_simplex SC I hs j) _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  simp_all [monotone_1_of_simplex]

end simplex_properties

theorem p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by
  intro h1
  have h2 := (SC.rl_proper fun _ ↦ 0).2 ⟨0, by omega⟩
  simp_all

section simplex_child

def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
⟨if a.val < j.val then a.val else a.val+1, by grind⟩

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

theorem insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by
  grind [insert_index]

theorem almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k :=
  ⟨⟨if a.1 < j.1 then a.1 else a.1 - 1, by grind⟩, by grind [insert_index]⟩

theorem insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by
  intro a b h1
  grind [insert_index]

theorem insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by
  apply StrictMono.injective
  apply insert_index_strict_mono

theorem delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by
  by_contra h2
  obtain ⟨k, h3⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  exact @insert_index_ne SC n1 hn1 i1 k (hs.1 (h3 ▸ congrFun h1 k))

theorem delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) :=
  ⟨fun k1 k2 h2 => insert_index_inj SC i (hs.1 h2), fun i2 hi2 j =>
    ⟨monotone_1_of_simplex SC J hs _ _ ((insert_index_strict_mono SC i).monotone
      (Fin.natCast_mono hi2 (by omega))) j, le_add_one_of_simplex SC J hs _ _ j⟩⟩

theorem delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J :=
  ⟨@delete_vertex_simplex SC n1 hn1 J hs i, hs, fun _ ⟨_, hi2⟩ => ⟨_, hi2⟩⟩

theorem is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by
  have h31 : Function.Injective f := by exact hsm.injective
  have hns : ∃ j, ∀ i, f i ≠ j := by
    by_contra! h1
    have h4 := Nat.card_eq_of_bijective f (by tauto)
    simp_all
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by
    simp_all [almost_surjective_of_insert_index]
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := fun k1 k2 h => by
    rwa [← (@insert_index_strict_mono SC n1 hn1 j).lt_iff_lt, ← hg, ← hg, hsm.lt_iff_lt]
  ext k
  rw [hg, h2.apply_eq]

theorem child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by
  refine ⟨fun h1 => ?_, by simp_all [delete_vertex_is_face]⟩
  choose f hf using fun k => h1.2.2 ⟨k, rfl⟩
  have h3 : StrictMono f := Monotone.strictMono_of_injective (fun k1 k2 h2 => by
    rwa [monotone_2_of_simplex SC J hs, hf, hf, ← monotone_2_of_simplex SC I h1.1])
    fun k1 k2 h2 => h1.1.1 (by rw [← hf, ← hf, h2])
  obtain ⟨j, rfl⟩ := @is_insert_index_of_strict_mono SC n1 hn1 f h3
  exact ⟨j, funext fun k => (hf k).symm⟩

end simplex_child

section cases_ABCD

theorem insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by
  refine ⟨fun j2 => if h : j2 = j then v else
    I (@almost_surjective_of_insert_index SC n1 hn1 j j2 h).choose, funext fun i => ?_, by simp⟩
  have h := @insert_index_ne SC n1 hn1 j i
  simp only [delete_vertex, h, dite_false]
  exact congrArg I (insert_index_inj SC j (almost_surjective_of_insert_index SC j _ h).choose_spec)


theorem surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by
  have h3 : (i+1).1 = i.1 + 1 := Fin.val_add_one_of_lt (by grind)
  grind [insert_index]

theorem parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by
  subst h1
  intro j1 j2 h4
  have h7 j3 (h : J j3 = J j) : j3 = j := by
    by_contra h51
    obtain ⟨i3, rfl⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j3 h51
    exact h2 ⟨i3, h⟩
  by_cases h8 : j1 = j
  · subst h8; exact (h7 j2 h4.symm).symm
  by_cases h9 : j2 = j
  · subst h9; exact h7 j1 h4
  obtain ⟨i1, rfl⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j1 h8
  obtain ⟨i2, rfl⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h9
  exact congrArg _ (hs.1 h4)


theorem parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by
  suffices h4 : simplex SC SC.n J by
    rw [child_simplex_char]
    use 0
    omega
  have h4 : J 0 ∉ Set.range I := fun ⟨i1, hi1⟩ => h2 (funext fun k =>
    le_antisymm (h3 k).1 (hi1 ▸ monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1) k))
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  intro j1 hj1 k1
  apply And.intro
  · rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    · simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  · have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      simp_all
    rw [e1, show (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 by simp] at h6
    exact congrFun h6 k1 ▸ (h3 k1).2

theorem parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by
  suffices h4 : simplex SC SC.n J by
    rw [child_simplex_char]
    use j
    omega
  have h4 : J j ∉ Set.range I := fun ⟨i1, hi1⟩ => h2 (funext fun k =>
    le_antisymm (hi1 ▸ monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1) k) (h3 k).1)
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by
      grind
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    omega
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  · rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    · rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    obtain rfl : j1 = n1 := by omega
    have h14 : Fin.ofNat _ (j1+1) = j := by
      simp_all
    rw [h14]
    simpa using (h3 k1).1
  · rw [show J 0 = I 0 by simpa using h5 0 (by omega), ← hj]
    exact (h3 k1).2



theorem parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by
  suffices h4 : simplex SC SC.n J by
    rw [child_simplex_char]
    use j
    omega
  have h6 j3 (h7 : j3 ≠ j) : ∃ i3, I i3 = J j3 := by
    obtain ⟨i3, rfl⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j3 h7
    exact ⟨i3, by rw [h1]; rfl⟩
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  · have hsi := @surround_index SC n1 hn1 j i hij
    have ha : (Fin.ofNat (SC.n+1) i2 : ℕ) = i2 := Nat.mod_eq_of_lt (by omega)
    have hb : (Fin.ofNat (SC.n+1) (i2+1) : ℕ) = i2 + 1 := Nat.mod_eq_of_lt (by omega)
    subst h1
    by_cases h8 : Fin.ofNat (SC.n+1) i2 = j
    · rw [h8, show Fin.ofNat (SC.n+1) (i2+1) = insert_index SC j (i+1) by
        ext; rw [hb, ← (hsi (by grind)).2]; grind]
      exact h5.2
    by_cases h9 : Fin.ofNat (SC.n+1) (i2+1) = j
    · rw [h9, show Fin.ofNat (SC.n+1) i2 = insert_index SC j i by ext; grind [insert_index]]
      exact h5.1
    obtain ⟨i3, hi3⟩ := @almost_surjective_of_insert_index SC n1 hn1 j _ h8
    obtain ⟨i4, hi4⟩ := @almost_surjective_of_insert_index SC n1 hn1 j _ h9
    rw [hi3, hi4]
    exact monotone_1_of_simplex SC _ hs _ _ ((@insert_index_strict_mono SC n1 hn1 j).le_iff_le.1
      (by rw [← hi3, ← hi4, Fin.le_def, ha, hb]; omega)) k2
  · have hm i : I 0 k2 ≤ I i k2 ∧ I i k2 ≤ I (Fin.last n1) k2 :=
      ⟨monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _) k2,
        monotone_1_of_simplex SC I hs _ _ (Fin.le_last _) k2⟩
    have hJ j3 : I 0 k2 ≤ J j3 k2 ∧ J j3 k2 ≤ I (Fin.last n1) k2 := by
      by_cases h12 : j3 = j
      · subst h12; exact ⟨(hm i).1.trans h5.1, h5.2.trans (hm _).2⟩
      obtain ⟨i3, hi3⟩ := h6 _ h12
      exact hi3 ▸ hm i3
    exact Nat.le_trans (hJ _).2 ((last_of_simplex SC I hs k2).trans (Nat.add_le_add_right (hJ 0).1 1))


noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

theorem ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by
  unfold coord_change_count
  have h k := And.intro (monotone_1_of_simplex SC I hs i1 i2 h1.1 k)
    (And.intro (monotone_1_of_simplex SC I hs i2 i3 h1.2 k) (le_add_one_of_simplex SC I hs i3 i1 k))
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun k _ => by grind)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
  grind

theorem ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  apply funext
  simp_all

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨coord_change_count SC (I 0) (I i), Nat.lt_succ_of_le (card_finset_fin_le _)⟩

theorem ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by
  intro i1 i2 h1
  unfold ccc_fun
  simp
  rw [ccc_add SC I hs 0 i1 i2 (by grind)]
  simp
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1

theorem ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by
  simp_all [is_insert_index_of_strict_mono, ccc_fun_strict_mono]

theorem ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by
    rw [Fin.ext_iff]
    change Finset.card {k : Fin SC.n | I 0 k ≠ I (Fin.last m) k} = SC.n ↔ _
    have hcard := Finset.card_eq_iff_eq_univ
      {k : Fin SC.n | I 0 k ≠ I (Fin.last m) k}
    simp_all
  refine Iff.trans ⟨fun h2 k1 => ?_, fun h2 k1 q => ?_⟩ h1.symm
  · obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    exact fun h3 => hi2 (le_antisymm (h3 ▸ monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2) k1)
      (monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1))
  · by_contra! hq
    exact h2 k1 (by rw [hq, hq])


theorem last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by
  have h3 j3 : ccc_fun SC J j3 = j3 := (ccc_fun_strict_mono SC J hs).apply_eq
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  apply lt_of_lt_of_le _ (monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k)
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm

theorem delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by
  let I := @delete_vertex SC n1 hn1 j1 J
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  · simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      omega
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by
      rw [h1, ← hi1]
      rfl
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by
      apply ccc_pos _ _ hs
      aesop
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by
      simp only [← h8]
      apply ccc_add SC J hs
      suffices h9 : j3 ≠ j1 by
        simp_all
        exact Fin.one_le_of_ne_zero h9
      apply insert_index_ne
    have h10 : c2 + SC.n ≤ SC.n := by
      omega
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by
    unfold I delete_vertex
    congr!
    simp_all [insert_index]
  have h3 j3 : ccc_fun SC J j3 = j3 := (ccc_fun_strict_mono SC J hs).apply_eq
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by
    unfold ccc_fun
    aesop
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne

theorem case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    simp [ccc_fun, coord_change_count]
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  refine ⟨fun h3 h4 => @insert_index_ne SC n1 hn1 j _ (h3.trans h4.symm), fun h3 => ?_⟩
  obtain ⟨i2, hi2⟩ := @almost_surjective_of_insert_index SC n1 hn1 j _ (Ne.symm h3)
  exact le_antisymm (Fin.le_last _) (hi2 ▸ (@insert_index_strict_mono SC n1 hn1 j).monotone (Fin.le_last i2))

theorem case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := (@delete_vertex_is_face SC n1 hn1 J hs j).1

  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  · rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  simp_all

theorem same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by
  refine ⟨fun a ↦ congrFun a j, fun h2 => funext fun j2 => ?_⟩
  by_cases h3 : j2 = j
  · rwa [h3]
  obtain ⟨i1, rfl⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  exact congrFun h1 i1

theorem case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    omega
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    grind
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := Fin.le_of_lt (Fin.lt_add_one_iff.mpr (by grind))
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by
    omega
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by
      omega
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by
      apply ccc_add SC I hs
      simp_all
    simp_all
  obtain ⟨k1, k2, h4⟩ : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by
    obtain ⟨k1, k2, h, e⟩ := Finset.card_eq_two.1 h3
    exact ⟨k1, k2, h, by rw [← Finset.coe_eq_pair.2 e]; simp⟩
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := h4.2.symm.subset (Set.mem_insert _ _)
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := h4.2.symm.subset (by simp)
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by
    intro h21
    let ins := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 k : I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by
      have := monotone_1_of_simplex SC I hs _ _ h32 k
      unfold ins
      split <;> simp_all
    have h22 : J3 j1 k3 ≠ I i1 k3 := by
      grind
    have h7 : ins ∉ Set.range I := fun ⟨i2, hi2⟩ => by
      rw [forall_and, ← hi2, ← monotone_2_of_simplex _ _ hs, ← monotone_2_of_simplex _ _ hs] at h6
      rcases (WCovBy.le_and_le_iff ⟨h32, fun i3 h33 => not_lt.2 (Fin.add_one_le_of_lt h33)⟩).mp h6
        with rfl | rfl <;> grind
    exact ⟨J3, hJ3.1, @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1 (by rwa [hJ3.2])
      (by simp_all), h22⟩

  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 (h14 : I = @delete_vertex SC n1 hn1 j1 J3) (h13 : is_face SC I J3) k :
      I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by
    subst h14
    exact ⟨monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1 k, monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2 k⟩
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      omega
    apply And.intro
    · apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp
    omega
  refine Finset.card_eq_two.mpr ⟨J1, J2, fun h9 => hJ2.2.2 (by rw [← h9, (h7 J1 k1 hJ1).2 k2 h4.1]),
    subset_antisymm ?_ ?_⟩
  · intro J3 hJ3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hJ3 ⊢
    obtain ⟨j2, hj2⟩ := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := by grind
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    obtain ⟨k5, hk5⟩ : ∃ k5, J3 j1 k5 ≠ I i1 k5 := Function.ne_iff.mp fun h19 =>
      @insert_index_ne SC n1 hn1 j1 i1 (hJ3.2.1.1 (by rw [h19, hj2]; rfl))
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    have h19 : k5 = k1 ∨ k5 = k2 := h4.2.subset (show I i1 k5 ≠ I (i1+1) k5 by omega)
    have h20 (J4 : _ → SC.G) (h21 : J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4) :
        J3 j1 = J4 j1 := funext fun k6 => by
      by_cases h22 : k5 = k6
      · rw [← h22, h21.1, h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    rcases
 h19 with rfl | rfl
    · exact .inl (h20 _ h71)
    · exact .inr (h20 _ h72)
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  · simp [Finset.insert_subset_iff, hJ1.2.1, hJ2.2.1]

theorem unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    grind
  have h6 : 2 ≤ sᶜ.card := by
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ, true_and]
    use k1
    grind
  have h7 := add_le_add h4 h6
  simp at h7
  omega

theorem case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := fun h11 => @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2
    (by grind) (le_antisymm (monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _) k2) (h11 ▸ Fin.le_last _))
  let ins2 := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.2 (h1 k))
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    simp at h11
    omega
  have h4 : is_face SC I J1 := by
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    · rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    simp_all
  use J1
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  rw [(last_eq_first_add_one SC J2 hJ2.2.2.1 k1), h2 k1, hJ2.1]
  unfold delete_vertex insert_index
  grind

theorem case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by
    rw [h2.1]
    unfold delete_vertex insert_index
    grind
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [(last_eq_first_add_one SC J h2.2.2.1) k1,←h4,hk1 0] at h5
  linarith

theorem case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := fun h11 => @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2
    (by grind) (le_antisymm (monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _) k2) (h11 ▸ Fin.zero_le _))
  let ins2 := fun k ↦ (I (Fin.last n1) k) - 1
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by
    rw [(Fin.val_sub_one_of_ne_zero (h1 k))]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    omega
  have h4 : is_face SC I J1 := parent_simplex_case_BC SC I hs J1 hJ1.1 h3 fun k2 => by
    rw [hJ1.2, Fin.le_def, ← add_le_add_iff_right 1, h21 k2]
    exact ⟨le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2, le_rfl⟩
  refine ⟨J1, ⟨hJ1.1, h4⟩, fun J2 hJ2 => ?_⟩

  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by
    rw [hJ2.1]
    unfold delete_vertex insert_index
    congr!
  rw [←h6, ←h21 k1] at h5
  omega

theorem zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by
  grind

theorem case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by
    rw [h2.1]
    unfold delete_vertex insert_index
    aesop
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←(last_eq_first_add_one SC J h2.2.2.1) k1,← h4,hk1]
  rfl

theorem case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by
  have hnd : ¬ case_D SC I := by
    contrapose! hABC
    tauto
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp
  apply Iff.intro
  · intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · omega
    · exact h1.2.1
  · intro h1
    rw [←or_and_right] at h1
    exact h1.2
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  simp_all

theorem case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  omega

theorem case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by
  obtain ⟨k1, h1⟩  := id h2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 (@p_ne_zero_of_cube SC n1 hn1)
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1

theorem case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by
  obtain ⟨k1, h1⟩  := id h2
  have h4 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1

end cases_ABCD

theorem boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by
  have hs : simplex SC n1 I := by
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  grind [one_of_ABCD, case_C_parent_count, case_D_parent_count]

theorem case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)

theorem parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by
  grind [one_of_ABCD, case_A_parent_count, case_B_parent_count, case_C_parent_count, case_D_parent_count]
