module

public import Mathlib
public import FixedPointTheorems.cubical_sperner

public section

@[expose] section

/-!
# Fixed points in the unit cube

Reduced labels encode coordinatewise displacement of a continuous cube map.
Cubical Sperner simplices on finer grids yield approximate fixed points, and
compactness of the cube supplies a genuine fixed point.
-/

open Classical

variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by simp only [rl_point, s, he, Finset.min_empty]
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, h3]
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
  have h1 : @rl_point n f x = m.1 := by simp only [rl_point, s, hm]
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    have h3 : k1 ∈ s := by
      apply Finset.mem_of_min
      rw [hm]
      simp only [WithTop.coe_eq_coe]
      ext
      exact h2
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at h3
    exact h3
  }
  {
    intro h2
    exact Finset.min_le_of_eq (s := s) (by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, h2]) hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  refine ⟨h1.1, fun k => ⟨?_, fun h2 => (h1.2 k).2 (Or.inr h2)⟩⟩
  intro h2 h3
  have h4 := (h1.2 k).1 h3
  rw [h2] at h4
  simp only [zero_ne_one, or_false] at h4
  exact absurd h4 (not_lt.mpr ((f x).2.1 k))
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · rcases h1.1 h2 with h3 | h3
    · exact le_of_lt h3
    · rw [h3]; exact (f x).2.2 k
  · exact le_of_not_gt fun h3 => (not_le.mpr h2) (h1.2 (Or.inl h3))
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq, Pi.le_def, Pi.zero_apply, Pi.one_apply, ← forall_and]
    intro i
    refine ⟨div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p), ?_⟩
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    refine ⟨h1.1, fun k => ⟨?_, ?_⟩⟩
    · intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    · intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      exact (div_eq_one_iff_eq (by simp only [ne_eq, Nat.cast_eq_zero]; omega)).mpr rfl
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  refine (dist_pi_le_iff (by positivity)).mpr fun k => ?_
  show |((v1 k).1 : ℝ) / p - ((v2 k).1 : ℝ) / p| ≤ 1 / p
  rw [abs_sub_le_iff]
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr ppos
  constructor
  · rw [sub_le_iff_le_add', ← add_div, div_le_div_iff_of_pos_right hp, ← Nat.cast_add_one,
      Nat.cast_le]
    exact (h1 k).1
  · rw [sub_le_iff_le_add', ← add_div, div_le_div_iff_of_pos_right hp, ← Nat.cast_add_one,
      Nat.cast_le]
    exact (h1 k).2
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := fun h => h3.2.symm.subset h
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  refine ⟨x0, fun k => ⟨?_, ?_⟩⟩
  · apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  refine ⟨discrete_map p (I ik), ?_, (reduced_label_props_3 f (discrete_map p (I ik)) k).1 hik⟩
  exact dist_discrete_map p ppos _ _
    (fun j => ⟨le_add_one_of_simplex _ I h3.1 i0 ik j,
      le_add_one_of_simplex _ I h3.1 ik i0 j⟩)
}

theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact fun i ↦ (x0s i).2
    exact ⟨⟨a, ha⟩, φ, h3.1, tendsto_subtype_rng.mpr h3.2⟩
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  have hc2 (k : Fin n) : Continuous (fun x : @unit_cube n => x.1 k) :=
    (continuous_apply k).comp continuous_subtype_val
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by
    apply le_of_tendsto_of_tendsto' ((hc2 k).seqContinuous h2.2)
      ((hc2 k).seqContinuous (f.2.seqContinuous h2.2))
    exact fun i ↦ (hx0 (φ i) k).1
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by
    obtain ⟨yk, h6⟩ := axiomOfChoice fun n => (hx0 (φ n) k).2
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by
      apply tendsto_of_tendsto_of_dist h2.2
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (@tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _)
      · exact fun _ ↦ dist_nonneg
      · intro i
        refine (h6 i).1.trans ?_
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        exact inv_anti₀ (Nat.cast_add_one_pos i)
          (by simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply])
    apply le_of_tendsto_of_tendsto' ((hc2 k).seqContinuous (f.2.seqContinuous h4))
      ((hc2 k).seqContinuous h4)
    exact fun i ↦ (h6 i).2
  exact ⟨xxx, Subtype.ext (funext fun k => le_antisymm (h4 k) (h3 k))⟩
}
