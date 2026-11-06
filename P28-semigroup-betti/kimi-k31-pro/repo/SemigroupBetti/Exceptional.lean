/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Antichain

/-!
# The exceptional case `(A, B) = (1, W - 1)`

Write-up `PROOF_B_lean_writeup.md`: Lemma 14, Lemma 15, Lemma 16.
-/

@[expose] public section

namespace SemigroupBetti

open Finset

namespace GenData

variable (G : GenData)

/-! ### Saturation -/

/-- **Saturation.** If the selected `k`-coordinates of a family of size `c` take values in
`[1, c]`, every value in `[1, c]` is attained. -/
lemma exists_coord_eq {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) (hcard : F.card = c) {v : ℕ}
    (hv1 : 1 ≤ v) (hvc : v ≤ c) : ∃ d ∈ F, G.sel d K k = v := by
  obtain ⟨d, hd, h⟩ := surj_on_of_inj_on_of_card_le (s := F) (t := Icc 1 c)
    (fun d _ => G.sel d K k) (fun d hd => mem_Icc.2 (hc d hd))
    (fun d d' hd hd' h => G.sel_coord_injOn hik hKe F hF hd hd' h)
    (by simp [hcard]) v (mem_Icc.2 ⟨hv1, hvc⟩)
  exact ⟨d, hd, h.symm⟩

/-! ### Facts in the exceptional case -/

section Exceptional

variable {G}
variable (hA : G.A = 1) (hB : G.B = G.W - 1)
include hA hB
set_option linter.unusedSectionVars false

lemma exc_R : G.R = G.W - 1 := by
  have := G.three_le_W; unfold R; omega

lemma exc_t : G.t = 1 := by have := G.three_le_W; unfold t; omega

lemma exc_p : G.p = 1 := by
  unfold p dg; rw [exc_t hA hB, show G.s = 1 from hA]; rfl

lemma exc_q : G.q = 1 := by
  unfold q dg; rw [exc_t hA hB, show G.s = 1 from hA]; rfl

lemma exc_U2 : G.U2 = Pi.single 2 (G.W - 1) := by
  funext j; fin_cases j <;> simp [U2, hA]

lemma exc_V2 : G.V2 = ![0, 1, 0, G.W - 2] := by
  have := G.three_le_W
  have h1 : G.W - G.B = 1 := by omega
  have h2 : G.B - G.A = G.W - 2 := by omega
  simp only [V2, h1, h2]

/-- `ν(0,0,W-1,0) = ν(0,1,0,W-2)`, both equal to `(W-1) n₂`. -/
lemma exc_nu_V2 : G.nu ![0, 1, 0, G.W - 2] = (G.W - 1) * G.n 2 := by
  rw [← exc_V2 hA hB, ← G.identity2, exc_U2 hA hB, G.nu_single]

/-- `gcd(n₂, n₃) = 1` in the exceptional family. -/
lemma exc_coprime : Nat.Coprime (G.n 3) (G.n 2) := by
  have hW := G.three_le_W
  have hn2 : G.n 2 = G.m + G.g * (G.W - 1) := by rw [n_two, G.b_eq, hB]
  have hn3 : G.n 3 = G.n 2 + G.g := by
    rw [hn2, n_three, G.w_eq]
    have : G.W = (G.W - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  rw [hn3, Nat.coprime_self_add_left, hn2, Nat.coprime_add_mul_left_right]
  exact Nat.Coprime.symm (show Nat.Coprime G.m G.g from G.gcd_eq_one)

end Exceptional

/-! ### Lemma 14 -/

/-- **Lemma 14.** If `A = 1`, `B = W - 1` and `P = W - 2`, then `c₂ = W - 1`. -/
theorem lemma14 (hA : G.A = 1) (hB : G.B = G.W - 1) (hP : G.P = G.W - 2) :
    G.crit 2 = G.W - 1 := by
  have hW := G.three_le_W
  -- `c₂ ≤ W - 1`
  have hle : G.crit 2 ≤ G.W - 1 := by
    apply Nat.find_min'
    rw [isCritCand_iff]
    refine ⟨by omega, ![0, 1, 0, G.W - 2], exc_nu_V2 hA hB, fun h => ?_⟩
    have := congrFun h 1
    simp at this
  by_contra hne
  have hc : G.crit 2 ≤ G.W - 2 := by omega
  have hc1 := G.one_le_crit 2
  -- saturation: some `𝓟` degree has selected `23`-vector `(0,0,W-2,y)`
  have hK : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
  obtain ⟨D, hD, hzD⟩ := G.exists_coord_eq (K := {2, 3}) (i := 3) (k := 2) (by decide) (by decide)
    G.famP (fun d hd => G.sideP_split hd)
    (fun d hd => by
      have := G.sel_two_bounds (G.sideP_split hd) hK (by decide)
      rw [hA] at this; exact this)
    hP (v := G.W - 2) (by omega) le_rfl
  have hS23 := G.sideP_split hD
  have hS01 := G.isSplit_of_mem_fam hD
  set z := G.sel D {2, 3}
  have hz0 : z 0 = 0 := G.sel_eq_zero hS23 hK (by decide)
  have hz1 : z 1 = 0 := G.sel_eq_zero hS23 hK (by decide)
  have hz3 : 0 < z 3 := G.sel_pos hS23 hK (by decide)
  have hnuz : G.nu z = D := (G.sel_of_split hS23 hK).1
  -- the alternative `r` at the critical degree avoids `2` and uses `0` or `1`
  obtain ⟨r, hr, hrne⟩ := G.exists_alt 2
  have hr2 := G.alt_coord_eq_zero hr hrne
  have hr01 : 0 < r 0 ∨ 0 < r 1 := by
    by_contra! h0
    have hr0 : r 0 = 0 := by omega
    have hr1 : r 1 = 0 := by omega
    have hreq : r = Pi.single 3 (r 3) := by
      funext j; fin_cases j <;> simp [hr0, hr1, hr2]
    rw [hreq, G.nu_single] at hr
    have hdvd : G.n 3 ∣ G.crit 2 * G.n 2 := ⟨r 3, by rw [← hr, mul_comm]⟩
    have h3 := (exc_coprime hA hB).dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) h3
    have := G.W_le_w
    have := G.m_pos
    have hn3 : G.n 3 = G.m + G.w := rfl
    omega
  -- the bridge `b = r + (W-2-c₂) e₂ + y e₃`
  let b := r + Pi.single 2 (G.W - 2 - G.crit 2) + Pi.single 3 (z 3)
  have hb : G.nu b = D := by
    simp only [b]
    rw [G.nu_add, G.nu_add, G.nu_single, G.nu_single, hr, ← hnuz, G.nu_eq_sum z, hz0, hz1, hzD,
      ← Nat.add_mul, Nat.add_sub_cancel' hc, n_two, n_three]
    ring
  have hK01 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have hy := G.sel_of_split hS01 hK01
  obtain ⟨i, hi, hri⟩ : ∃ i ∈ ({0, 1} : Finset (Fin 4)), 0 < r i := by
    rcases hr01 with h | h
    · exact ⟨0, by simp, h⟩
    · exact ⟨1, by simp, h⟩
  have hyi := G.sel_pos hS01 hK01 hi
  refine G.no_bridge hS01 hy.1 hnuz hb hi hyi (j := 3) (by decide) hz3
    ⟨i, ?_, hyi⟩ ⟨3, ?_, hz3⟩
  · simp only [b, Pi.add_apply]; omega
  · simp [b]; omega

/-! ### Lemma 15 -/

/-- **Lemma 15.** If `A = 1`, `B = W - 1` and `Q = W - 2`, then some `𝓠` degree has selected
`13`-vector with `u = 1`, and every such vector is exactly `(0,1,0,W-2)`. -/
theorem lemma15 (hA : G.A = 1) (hB : G.B = G.W - 1) (hQ : G.Q = G.W - 2) :
    (∃ D ∈ G.famQ, G.sel D {1, 3} 1 = 1) ∧
      ∀ D ∈ G.famQ, G.sel D {1, 3} 1 = 1 → G.sel D {1, 3} = ![0, 1, 0, G.W - 2] := by
  have hW := G.three_le_W
  have hK : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
  have hF : ∀ d ∈ G.famQ, G.IsSplit d {1, 3} := fun d hd => G.sideQ_split hd
  refine ⟨?_, ?_⟩
  · exact G.exists_coord_eq (K := {1, 3}) (i := 3) (k := 1) (by decide) (by decide) G.famQ hF
      (fun d hd => by
        have := G.sel_one_bounds (hF d hd) hK (by decide)
        rw [hB] at this; exact this)
      hQ (v := 1) le_rfl (by omega)
  · intro D hD hu
    set z := G.sel D {1, 3}
    have hS := hF D hD
    have hz0 : z 0 = 0 := G.sel_eq_zero hS hK (by decide)
    have hz2 : z 2 = 0 := G.sel_eq_zero hS hK (by decide)
    -- lower bound `v ≥ W - 2` from Lemma 11
    have hT := G.pairsOf_antichain (F := G.famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hpos := G.pairsOf_pos (F := G.famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hmem : (z 1, z 3) ∈ G.pairsOf G.famQ {1, 3} 1 3 := mem_image.2 ⟨D, hD, rfl⟩
    have hco := hT.corank_le hpos hmem
    have hfilt : (G.pairsOf G.famQ {1, 3} 1 3).filter (fun y => z 1 ≤ y.1) =
        G.pairsOf G.famQ {1, 3} 1 3 := by
      apply filter_true_of_mem
      intro y hy; rw [hu]; exact (hpos y hy).1
    rw [hfilt, G.card_pairsOf (by decide) (by decide) hF] at hco
    rw [show G.famQ.card = G.W - 2 from hQ] at hco
    -- upper bound `v ≤ W - 2` by the exceptional replacement
    have hv : z 3 ≤ G.W - 2 := by
      by_contra hv
      have hU : G.V2 ≤ z := by
        rw [exc_V2 hA hB]; intro j; fin_cases j <;> simp [hz0, hz2, hu]; omega
      exact G.no_replace hS hK hU G.identity2.symm (k := 3)
        (by change G.V2 3 < z 3; rw [exc_V2 hA hB]; simp; omega) (j := 2) (by decide)
        (by rw [exc_U2 hA hB]; simp; omega)
    funext j; fin_cases j <;> simp [hz0, hz2, hu]; omega

/-! ### Lemma 16 -/

/-- **Lemma 16.** If `(A, B) = (1, W - 1)` then `P + Q ≤ 2W - 5`. -/
theorem lemma16_PQ (hA : G.A = 1) (hB : G.B = G.W - 1) : G.P + G.Q ≤ 2 * G.W - 5 := by
  have hW := G.three_le_W
  have hP := G.P_le
  have hQ := G.Q_le
  rw [exc_R hA hB] at hP hQ
  by_contra hc
  have hP' : G.P = G.W - 2 := by omega
  have hQ' : G.Q = G.W - 2 := by omega
  have hc2 := G.lemma14 hA hB hP'
  obtain ⟨⟨D, hD, hu⟩, hall⟩ := G.lemma15 hA hB hQ'
  have hsel := hall D hD hu
  have hK : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
  have hDeq : D = G.crit 2 * G.n 2 := by
    rw [← (G.sel_of_split (G.sideQ_split hD) hK).1, hsel, exc_nu_V2 hA hB, hc2]
  obtain ⟨-, -, hS, -⟩ := G.mem_fam.1 hD
  subst hDeq
  exact hS ⟨_, by rw [G.compSupp_critVertex 2]; rfl⟩

/-- **Main combinatorial theorem.** `β₁ ≤ 2W`. -/
theorem beta1_le_two_W : G.beta1 ≤ 2 * G.W := by
  rw [G.beta1_eq]
  by_cases h : (G.s, G.t) = (1, 1)
  · obtain ⟨hA, hB⟩ := G.st_eq_one_one_iff.1 h
    have hW := G.three_le_W
    have hPQ := G.lemma16_PQ hA hB
    have hE := G.E_le
    rw [exc_p hA hB, exc_q hA hB] at hE
    have hσ := G.sigma_le_four
    omega
  · have hσ := G.sigma_le_four
    have hP := G.P_le
    have hQ := G.Q_le
    have hE := G.E_le
    have hs := G.s_pos
    have ht := G.t_pos
    have hR := G.two_le_R
    rw [G.R_eq] at hP hQ hR
    have hpq := G.p_add_q_le
    have hp0 := G.p_pos
    rcases lt_trichotomy G.s G.t with hlt | heq | hgt
    · omega
    · have hdg : G.dg = G.s := by unfold dg; rw [← heq, Nat.gcd_self]
      have hp : G.p = 1 := by
        have := G.dg_mul_p; rw [hdg, ← heq] at this
        exact (Nat.mul_eq_left (by omega)).1 this
      have hq : G.q = 1 := by
        have := G.dg_mul_q; rw [hdg] at this
        exact (Nat.mul_eq_left (by omega)).1 this
      have hs2 : 2 ≤ G.s := by
        by_contra hc
        exact h (Prod.ext (by omega) (by omega))
      omega
    · omega

end GenData

end SemigroupBetti
