module

public import Chazelle.Core.RestoreFArcs
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-E, the search: the geometry of a kind-1 piece

A kind-1 piece runs over the walk vertices `s, s + 1, …, s + m` (modulo `n`), and its weight is
`m`: so every one of its `m` walk edges is counted (`counted_of_wt`).  In a chain model the
counted edges are tour edges, so the piece's chain lies on the model's chain (`piece_set_sub`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)

/-- **The walk edges met by the open key interval of a piece** `(s, s + m)`. -/
theorem piece_edges {s m n : ℕ} (hs : s < n) (hm : 0 < m) (hmn : m < n) {p : ℕ} (hp : p < n) :
    (∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc (s : ℝ) (((s + m) % n : ℕ) : ℝ) (p + t)) ↔
      ∃ d, d < m ∧ (s + d) % n = p := by
  rw [Model.mem_arcEdges_iff]
  by_cases hw : s + m < n
  · rw [Nat.mod_eq_of_lt hw]
    have h1 : (s : ℝ) < ((s + m : ℕ) : ℝ) := by exact_mod_cast (by omega : s < s + m)
    rw [ite_eq_left h1]
    constructor
    · rintro ⟨a, b⟩
      have a' : p < s + m := by exact_mod_cast a
      have b' : s < p + 1 := by exact_mod_cast b
      exact ⟨p - s, by omega, by rwo [Nat.mod_eq_of_lt (by omega)]⟩
    · rintro ⟨d, hd, e⟩
      rw [Nat.mod_eq_of_lt (by omega)] at e
      exact ⟨by exact_mod_cast (by omega : p < s + m), by exact_mod_cast (by omega : s < p + 1)⟩
  · have e1 : (s + m) % n = s + m - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e1]
    have h1 : ¬ (s : ℝ) < ((s + m - n : ℕ) : ℝ) := by
      have : ¬ s < s + m - n := by omega
      exact_mod_cast this
    rw [ite_eq_right h1]
    constructor
    · rintro (a | b)
      · have a' : p < s + m - n := by exact_mod_cast a
        exact ⟨p + n - s, by omega, by
          rw [show s + (p + n - s) = p + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]⟩
      · have b' : s < p + 1 := by exact_mod_cast b
        exact ⟨p - s, by omega, by rwo [Nat.mod_eq_of_lt (by omega)]⟩
    · rintro ⟨d, hd, e⟩
      by_cases h : s + d < n
      · rw [Nat.mod_eq_of_lt h] at e
        right; exact_mod_cast (by omega : s < p + 1)
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at e
        left; exact_mod_cast (by omega : p < s + m - n)

/-- **A piece of weight `m` over `m` walk edges has all its edges counted.** -/
theorem counted_of_wt {M : Model} {s m : ℕ} (hs : s < M.W.n) (hm : 0 < m) (hmn : m < M.W.n)
    (hwt : M.arcWt (s : ℝ) (((s + m) % M.W.n : ℕ) : ℝ) = m) :
    ∀ d, d < m → M.counted ((s + d) % M.W.n) := by
  classical
  set n := M.W.n
  set S : Set ℕ := {p | p < n ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    sideInArc (s : ℝ) (((s + m) % n : ℕ) : ℝ) (p + t)} with hS
  set T : Set ℕ := {p | p < n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    sideInArc (s : ℝ) (((s + m) % n : ℕ) : ℝ) (p + t)} with hT
  have hSe : S = (fun d => (s + d) % n) '' Set.Iio m := by
    ext p
    simp [hS, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨hp, h⟩
      obtain ⟨d, hd, e⟩ := (piece_edges hs hm hmn hp).1 h
      exact ⟨d, hd, e⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨Nat.mod_lt _ (by omega), (piece_edges hs hm hmn (Nat.mod_lt _ (by omega))).2 ⟨d, hd, rfl⟩⟩
  have hinj : Set.InjOn (fun d => (s + d) % n) (Set.Iio m) := by
    intro x hx y hy hxy
    simp [Set.mem_Iio] at hx hy
    simp at hxy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.ModEq.add_left_cancel' s hxy
      have h2 := (Nat.modEq_iff_dvd' h.le).1 this
      obtain ⟨k, hk⟩ := h2
      rcases k with _ | k
      · omega
      · have : n * (k + 1) ≥ n := Nat.le_mul_of_pos_right _ (by omega)
        omega
    · have := Nat.ModEq.add_left_cancel' s hxy
      have h2 := (Nat.modEq_iff_dvd' h.le).1 this.symm
      obtain ⟨k, hk⟩ := h2
      rcases k with _ | k
      · omega
      · have : n * (k + 1) ≥ n := Nat.le_mul_of_pos_right _ (by omega)
        omega
  have hcS : S.ncard = m := by
    rw [hSe, hinj.ncard_image, Set.ncard_eq_toFinset_card' , Set.toFinset_Iio]
    simp
  have hTS : T ⊆ S := fun p hp => ⟨hp.1, hp.2.2⟩
  have hSf : S.Finite := by rw [hSe]; exact (Set.finite_Iio m).image _
  have hcT : T.ncard = m := hwt
  have hTeq : T = S := Set.eq_of_subset_of_ncard_le hTS (by rw [hcS, hcT]) hSf
  intro d hd
  have hmem : (s + d) % n ∈ S := by rw [hSe]; exact ⟨d, hd, rfl⟩
  rw [← hTeq] at hmem
  exact hmem.2.1

/-- A point of a counted walk edge of a chain model lies on the chain. -/
theorem counted_pt_mem (C : Chain) {p : ℕ} (hp : (chainModel C).counted p) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) :
    Geometry.lerp ((chainModel C).W.vtx p)
      ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n)) t ∈ C.set := by
  obtain ⟨h6, hp'⟩ := hp
  have hn  := chainModel_n C
  rw [hn, Nat.mod_eq_of_lt (by omega)]
  rcases h1.lt_or_eq with h1 | rfl
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := p - 6) (t := t) (by omega)
      (fun h => absurd h (by omega)) h0 h1
    rw [show p - 6 + 6 = p by omega] at this
    unfold Chazelle.Chain.sidePt at this
    rwa [C.sideWalk_n, Nat.mod_eq_of_lt (by omega)] at this
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := p + 1 - 6) (t := 0) (by omega)
      (fun _ => rfl) le_rfl one_pos
    rw [show p + 1 - 6 + 6 = p + 1 by omega, Chazelle.Chain.sidePt_zero] at this
    have e : Geometry.lerp ((chainModel C).W.vtx p) ((chainModel C).W.vtx (p + 1)) 1 =
        (chainModel C).W.vtx (p + 1) := by
      simp [Geometry.lerp, one_mul, add_sub_cancel]
    rwx [e]

/-- **The chain of a piece over counted edges of a chain model lies on the model's chain.** -/
theorem piece_set_sub {C Cα : Chain} {s : ℕ}
    (hdir : (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ((s + d) % (chainModel C).W.n) = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m →
        (chainModel C).W.vtx ((s + d) % (chainModel C).W.n) = Cα.vertex (Cα.m - d)))
    (hc : ∀ d, d < Cα.m → (chainModel C).counted ((s + d) % (chainModel C).W.n)) :
    Cα.set ⊆ C.set := by
  set n := (chainModel C).W.n
  have hsucc : ∀ d, ((s + d) % n + 1) % n = (s + (d + 1)) % n := fun d => by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
  intro x hx
  obtain ⟨k, hk, hx⟩ := hx
  rw [Cα.chainEdge_eq] at hx
  obtain ⟨t, t0, t1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  rcases hdir with hu | hd
  · have := counted_pt_mem C (hc k hk) t0 t1
    rwa [hsucc, hu k hk.le, hu (k + 1) hk] at this
  · have := counted_pt_mem C (hc (Cα.m - k - 1) (by omega)) (t := 1 - t) (by linarith)
      (by linarith)
    rw [hsucc, hd _ (by omega), hd _ (by omega), show Cα.m - (Cα.m - k - 1) = k + 1 by omega,
      show Cα.m - (Cα.m - k - 1 + 1) = k by omega] at this
    have e : Geometry.lerp (Cα.vertex (k + 1)) (Cα.vertex k) (1 - t) =
        Geometry.lerp (Cα.vertex k) (Cα.vertex (k + 1)) t := by
      simp [Geometry.lerp, Prod.mk.injEq]; constructor <;> ring
    rwa [e] at this

end

end Restore

end Chazelle.Core
