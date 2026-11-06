module

public import Mathlib
public import FixedPointTheorems.cubical_sperner

/-!
# Fixed points in the unit cube

Reduced labels encode coordinatewise displacement of a continuous cube map.
Cubical Sperner simplices on finer grids yield approximate fixed points, and
compactness of the cube supplies a genuine fixed point.
-/

@[expose] public section

open Classical

variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

section
variable (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
theorem reduced_label_props_1 
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  · have h1 : @rl_point n f x = n := by
      show rlp = n
      unfold rlp minval
      simp_all
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by
      grind
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
  have h1 : @rl_point n f x = m.1 := by
    show rlp = m.1
    unfold rlp minval
    simp_all
  rw [h1]
  simp
  intro k1
  apply And.intro
  · intro h2
    suffices h3 : k1 ∈ s by
      grind
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  · intro h2
    have h3 : k1 ∈ s := by
      grind
    exact Finset.min_le_of_eq h3 hm

theorem reduced_label_props_2 
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  · intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  simp_all

theorem reduced_label_props_3 (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  · intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  grind
end

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    omega
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    · intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    · intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega

theorem dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by rfl
  have hx2 : x2 k = (v2 k).1 / p := by rfl
  rw [hx1, hx2, Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    rwa [div_le_div_iff_of_pos_right (Nat.cast_pos'.mpr ppos), ←Nat.cast_add_one, Nat.cast_le]
  }

theorem nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by
    intro h4
    exact h3.2.symm.subset h4
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  · apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by tauto
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  simp_all

theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := by grind
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) :=
    (continuous_apply k).comp continuous_subtype_val
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by
    apply le_of_tendsto_of_tendsto' ((hc2 k).seqContinuous h2.2) ((hc2 k).seqContinuous $ f.2.seqContinuous h2.2)
    exact fun i ↦ (hx0 (φ i) k).1
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by
      apply tendsto_of_tendsto_of_dist h2.2
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (@tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _) _
      · intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      exact fun _ ↦ dist_nonneg
    apply le_of_tendsto_of_tendsto' ((hc2 k).seqContinuous $ f.2.seqContinuous h4) ((hc2 k).seqContinuous h4)
    exact fun i ↦ (h6 i).2
  use xxx
  ext k
  grind
