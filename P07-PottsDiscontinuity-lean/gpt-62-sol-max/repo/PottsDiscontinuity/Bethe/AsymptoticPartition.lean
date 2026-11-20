module

public import PottsDiscontinuity.Bethe.AsymptoticNorm

/-! # Cyclic root cells and their gap estimates -/

@[expose] public section

open Set
open scoped BigOperators
open Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

section

variable {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n)

theorem rootPartitionPoint_zero :
    rootPartitionPoint n p hn ⟨0, by omega⟩ = p ⟨n - 1, by omega⟩ - 2 * Real.pi := rfl

theorem rootPartitionPoint_end :
    rootPartitionPoint n p hn ⟨n + 1, by omega⟩ = p ⟨0, hn⟩ + 2 * Real.pi := by
  simp [rootPartitionPoint]

theorem rootPartitionPoint_root (j : Fin n) :
    rootPartitionPoint n p hn ⟨j.val + 1, by omega⟩ = p j := by
  grind [rootPartitionPoint]

end

/-- The linear progression of Bethe indices gives the same increment rule for the
base roots and for the interacting counting function. -/
theorem rootPartitionPoint_increment {N k : ℕ} (hs : 2 * (k + 1) ≤ N)
    {p : Fin (k + 1) → ℝ} (f : ℝ → ℝ) (d : ℝ)
    (hroot : ∀ i, f (p i) = discreteBetheIndex (k + 1) i * d)
    (hperiod : ∀ x, f (x + 2 * Real.pi) = f x + ((N : ℝ) - (k + 1 : ℕ)) * d)
    (j : Fin (k + 2)) :
    f (rootPartitionPoint (k + 1) p (by omega) j.succ) -
      f (rootPartitionPoint (k + 1) p (by omega) j.castSucc) =
      rootGapMultiplicity N (k + 1) j * d := by
  have hcast := Nat.cast_sub (R := ℝ) (by omega : 2 * (k + 1) ≤ N + 1)
  by_cases h₀ : j.val = 0
  · have he : j = 0 := Fin.ext h₀
    subst j
    change f (p 0) - f (p (Fin.last k) - 2 * Real.pi) = _
    have h := hperiod (p (Fin.last k) - 2 * Real.pi)
    rw [sub_add_cancel] at h
    rw [show f (p (Fin.last k) - 2 * Real.pi) = _ from eq_sub_of_add_eq h.symm, hroot, hroot]
    simp [rootGapMultiplicity, discreteBetheIndex, hcast]
    ring
  · by_cases hj : j.val = k + 1
    · have he : j = Fin.last (k + 1) := Fin.ext hj
      subst j
      have h₁ : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
          p 0 + 2 * Real.pi := rootPartitionPoint_end p (by omega)
      have h₂ : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc =
          p (Fin.last k) := rootPartitionPoint_root p (by omega) (Fin.last k)
      rw [h₁, h₂, hperiod, hroot, hroot]
      simp [rootGapMultiplicity, discreteBetheIndex, hcast]
      ring
    · have hlo : rootPartitionPoint (k + 1) p (by omega) j.castSucc = p ⟨j.val - 1, by omega⟩ := by
        simp [rootPartitionPoint, h₀, show j.val ≠ k + 1 + 1 by omega]
      have hhi : rootPartitionPoint (k + 1) p (by omega) j.succ = p ⟨j.val, by omega⟩ := by
        simp [rootPartitionPoint, hj]
      rw [hlo, hhi, hroot, hroot]
      simp [rootGapMultiplicity, h₀, hj, discreteBetheIndex, Nat.cast_sub (by omega : 1 ≤ j.val)]
      ring

theorem rootPartitionPoint_strictMono {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) : StrictMono (rootPartitionPoint n p hn) := by
  intro i j hij
  by_cases hi0 : i.val = 0
  · have hi : rootPartitionPoint n p hn i = p ⟨n - 1, by omega⟩ - 2 * Real.pi := by
      simp only [rootPartitionPoint, dite_eq_left hi0]
    rw [hi]
    have hlast := (hp.1 ⟨n - 1, by omega⟩).2
    by_cases hjend : j.val = n + 1
    · have hj : rootPartitionPoint n p hn j = p ⟨0, hn⟩ + 2 * Real.pi := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_left hjend]
      rw [hj]
      have hfirst := (hp.1 ⟨0, hn⟩).1
      linarith [Real.pi_pos]
    · have hj : rootPartitionPoint n p hn j = p ⟨j.val - 1, by omega⟩ := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_right hjend]
      rw [hj]
      have hbound := (hp.1 ⟨j.val - 1, by omega⟩).1
      linarith
  · have hiend : i.val ≠ n + 1 := by omega
    have hi : rootPartitionPoint n p hn i = p ⟨i.val - 1, by omega⟩ := by
      simp only [rootPartitionPoint, dite_eq_right hi0, dite_eq_right hiend]
    rw [hi]
    by_cases hjend : j.val = n + 1
    · have hj : rootPartitionPoint n p hn j = p ⟨0, hn⟩ + 2 * Real.pi := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_left hjend]
      rw [hj]
      have hfirst := (hp.1 ⟨0, hn⟩).1
      have hbound := (hp.1 ⟨i.val - 1, by omega⟩).2
      linarith
    · have hj : rootPartitionPoint n p hn j = p ⟨j.val - 1, by omega⟩ := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_right hjend]
      rw [hj]
      exact hp.2.1 (show (⟨i.val - 1, by omega⟩ : Fin n) < ⟨j.val - 1, by omega⟩ from
        by change i.val - 1 < j.val - 1; omega)

theorem rootPartition_gap_pos {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (j : Fin (n + 1)) :
    0 < rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc := by
  apply sub_pos.mpr
  exact rootPartitionPoint_strictMono hp hn (show j.castSucc < j.succ from by
    simp)

theorem rootStepDensity_on_cell {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
    {x : ℝ} (hx : rootPartitionPoint n p hn j.castSucc ≤ x ∧
      x < rootPartitionPoint n p hn j.succ) :
    rootStepDensity N n p hn x = rootGapMultiplicity N n j /
      ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)) := by
  have hm := (rootPartitionPoint_strictMono hp hn).monotone
  unfold rootStepDensity
  rw [Finset.sum_eq_single j]
  · simp_all
  · intro k _ hkj
    have hk : ¬ (rootPartitionPoint n p hn k.castSucc ≤ x ∧
        x < rootPartitionPoint n p hn k.succ) := by
      intro hk
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · have hle : k.succ ≤ j.castSucc := by assumption
        have := hm hle
        linarith
      · have hle : j.succ ≤ k.castSucc := by assumption
        have := hm hle
        linarith
    exact ite_eq_right hk
  simp

/-- Every cyclic root cell meets the physical interval. -/
theorem rootPartition_cell_meets_Icc {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (j : Fin (n + 1)) :
    ∃ x ∈ Icc (-Real.pi) Real.pi,
      rootPartitionPoint n p hn j.castSucc ≤ x ∧
        x < rootPartitionPoint n p hn j.succ := by
  have hm := rootPartitionPoint_strictMono hp hn
  have hlo : -Real.pi < rootPartitionPoint n p hn j.succ := by
    have hfirst : rootPartitionPoint n p hn ⟨1, by omega⟩ = p ⟨0, hn⟩ := by
      simpa using rootPartitionPoint_root p hn ⟨0, hn⟩
    have := hm.monotone (show (⟨1, by omega⟩ : Fin (n + 2)) ≤ j.succ from by
      change 1 ≤ j.val + 1; omega)
    rw [hfirst] at this
    exact (hp.1 ⟨0, hn⟩).1.trans_le this
  have hhi : rootPartitionPoint n p hn j.castSucc < Real.pi := by
    have hlast : rootPartitionPoint n p hn ⟨n, by omega⟩ = p ⟨n - 1, by omega⟩ := by
      convert rootPartitionPoint_root p hn ⟨n - 1, by omega⟩ using 1
      grind
    have := hm.monotone (show j.castSucc ≤ (⟨n, by omega⟩ : Fin (n + 2)) from by
      change j.val ≤ n; omega)
    rw [hlast] at this
    exact this.trans_lt (hp.1 ⟨n - 1, by omega⟩).2
  refine ⟨max (-Real.pi) (rootPartitionPoint n p hn j.castSucc),
    ⟨le_max_left _ _, max_le (by linarith [Real.pi_pos]) hhi.le⟩, le_max_right _ _, ?_⟩
  aesop

/-- A positive lower bound for the density gives the required gap bound. -/
theorem rootPartition_gap_le_of_density_lower {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) {m : ℝ} (hm : 0 < m)
    (hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m / 2 ≤ rootStepDensity N n p hn x)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      2 * rootGapMultiplicity N n j / (m * (N : ℝ)) := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hgap := rootPartition_gap_pos hp hn j
  obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp hn j
  have hb := hlower x hx
  rw [rootStepDensity_on_cell hp hn hs j hcell] at hb
  have hb' := (le_div_iff₀ (mul_pos hN hgap)).mp hb
  apply (le_div_iff₀ (mul_pos hm hN)).mpr
  nlinarith only [hb']

theorem rootGapMultiplicity_le_offset {N n r : ℕ} (hs : 2 * n ≤ N)
    (hcount : N = 2 * (n + r)) (j : Fin (n + 1)) :
    rootGapMultiplicity N n j ≤ (2 * r + 1 : ℝ) := by
  have hnat : N + 1 - 2 * n = 2 * r + 1 := by omega
  unfold rootGapMultiplicity
  split_ifs
  · rw [hnat]
    push_cast
    rfl
  simp

/-- The missing gap estimate for Theorem 2.6: only convergence of the
weighted density norm is assumed; no Bethe equation or convergence rate is
needed. The count identity is exactly `n = N/2-r` for even `N`. -/
theorem eventually_rootPartition_gap_le {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N n : ι → ℕ) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (hn : ∀ i, 0 < n i)
    (hs : ∀ i, 2 * n i ≤ N i) (hcount : ∀ i, N i = 2 * (n i + r))
    (hb : ∀ i, BddAbove (densityValues Δ (rootStepError Δ (N i) (p i) (hn i))))
    (hlim : Tendsto (fun i => densityNorm Δ
      (rootStepError Δ (N i) (p i) (hn i))) l (𝓝 0)) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ i in l, ∀ j : Fin (n i + 1),
      rootPartitionPoint (n i) (p i) (hn i) j.succ -
        rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤
          2 * (2 * r + 1 : ℝ) / (m * (N i : ℝ)) := by
  obtain ⟨m, hm, hlower⟩ := eventually_density_ge_half hΔ
    (fun i => rootStepDensity (N i) (n i) (p i) (hn i)) hb hlim
  refine ⟨m, hm, ?_⟩
  filter_upwards [hlower] with i hi j
  apply (rootPartition_gap_le_of_density_lower (hp i) (hn i) (hs i) hm hi j).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset (hs i) (hcount i) j)
    (by norm_num)

theorem root_interior_gap_of_mesh {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) {d : ℝ}
    (hmesh : ∀ j : Fin (n + 1),
      rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤ d)
    (j : ℕ) (hj : j + 1 < n) : p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ d := by
  have hi := hmesh ⟨j + 1, by omega⟩
  change rootPartitionPoint n p hn ⟨j + 1 + 1, by omega⟩ -
    rootPartitionPoint n p hn ⟨j + 1, by omega⟩ ≤ d at hi
  grind [rootPartitionPoint_root]

private def interiorCell {k : ℕ} (j : Fin k) : Fin (k + 2) := j.castSucc.succ

private theorem interiorCell_left {k : ℕ} (p : Fin (k + 1) → ℝ) (j : Fin k) :
    rootPartitionPoint _ p (by omega) (interiorCell j).castSucc = p j.castSucc :=
  rootPartitionPoint_root p (by omega) j.castSucc

private theorem interiorCell_right {k : ℕ} (p : Fin (k + 1) → ℝ) (j : Fin k) :
    rootPartitionPoint _ p (by omega) (interiorCell j).succ = p j.succ :=
  rootPartitionPoint_root p (by omega) j.succ

/-- A local quadrature estimate. `w` is any modulus bound for the test
function on this cell; `E` is the actual uniform error of its density. -/
theorem root_mesh_consequences {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) {d : ℝ}
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d) :
    p 0 + Real.pi ≤ d ∧ Real.pi - p (Fin.last k) ≤ d ∧
      ∀ j : Fin k, p j.succ - p j.castSucc ≤ d := by
  have hfirst := hmesh 0
  have hlast := hmesh (Fin.last (k + 1))
  have h0 : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := rfl
  have hend : rootPartitionPoint (k + 1) p (by omega)
      (Fin.last (k + 1)).castSucc = p (Fin.last k) := by
    convert rootPartitionPoint_root p (by omega) (Fin.last k) using 1
    congr 1
  have hzero : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := rfl
  have hfinal : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
      p 0 + 2 * Real.pi := by
    convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
  rw [h0, hzero] at hfirst
  rw [hend, hfinal] at hlast
  refine ⟨by linarith [(hp.1 (Fin.last k)).2], by linarith [(hp.1 0).1], ?_⟩
  intro j
  simpa [interiorCell_left, interiorCell_right] using hmesh (interiorCell j)

theorem exists_interior_root_cell {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    {x : ℝ} (hleft : q ⟨0, hn⟩ ≤ x) (hright : x < q ⟨n - 1, by omega⟩) :
    ∃ j : Fin n, ∃ hj : j.val + 1 < n,
      q j ≤ x ∧ x < q ⟨j.val + 1, hj⟩ := by
  classical
  let s := Finset.univ.filter (fun j => q j ≤ x)
  have hs : s.Nonempty := ⟨⟨0, hn⟩, by grind⟩
  let j := s.max' hs
  have hjmem : j ∈ s := s.max'_mem hs
  have hjx : q j ≤ x := (Finset.mem_filter.mp hjmem).2
  have hjnext : j.val + 1 < n := by
    grind
  refine ⟨j, hjnext, hjx, ?_⟩
  by_contra h
  have hm : (⟨j.val + 1, hjnext⟩ : Fin n) ∈ s := by
    grind
  have hb := s.le_max' ⟨j.val + 1, hjnext⟩ hm
  change j.val + 1 ≤ j.val at hb
  omega

theorem one_le_rootGapMultiplicity {N n : ℕ} (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    1 ≤ rootGapMultiplicity N n j := by
  unfold rootGapMultiplicity
  split_ifs
  · exact_mod_cast (show 1 ≤ N + 1 - 2 * n by omega)
  · exact le_rfl

end PottsDiscontinuity.Bethe
