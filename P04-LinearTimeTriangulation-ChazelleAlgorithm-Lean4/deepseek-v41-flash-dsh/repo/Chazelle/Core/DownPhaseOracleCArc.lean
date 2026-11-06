module

public import Chazelle.Core.DownPhaseOraclePlan

/-!
# WP-M (E7-B, part 6): the chain arcs of a subarc

For a subarc of `L ≤ n - 1` walk edges of the interior walk (`SubOK`), the one or two arcs of
the chain model of its chain (`chain_arcSet_one`, `chain_arcSet_two`) satisfy everything the
chain oracles require (`CArc`: proper ends on the walk, inner points, weight at most `L`) and
have the point sets of the corresponding parts of the subarc (`chainArcs_one`,
`chainArcs_two`).
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)

variable {Q : Polygon}

/-- **A chain arc query**: the ends are proper positions on the walk of the chain model, non-vertex
ends are inner points, the weight is at most `γ`, and the point set is `S`. -/
def CArc (Q : Polygon) (C : Chain) (s e : WPos) (γ : ℕ) (S : Set Point) : Prop :=
  ProperPos (chainModel C) Q Q.n s ∧ ProperPos (chainModel C) Q Q.n e ∧
    s.edge < (chainModel C).W.n ∧ e.edge < (chainModel C).W.n ∧
    (s.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos Q s)) ∧
    (e.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos Q e)) ∧
    (chainModel C).arcWt ((chainModel C).key Q s) ((chainModel C).key Q e) ≤ γ ∧
    (chainModel C).arcSet ((chainModel C).key Q s) ((chainModel C).key Q e) = S

/-- **A subarc of the interior walk** from `⟨u, sh⟩` to `⟨(u + ee) mod n, eh⟩` meeting `L ≤ n - 1`
walk edges (the end normalized). -/
structure SubOK (Q : Polygon) (u L sh ee eh : ℕ) : Prop where
  hu : u < Q.n
  h1 : 1 ≤ L
  h2 : L + 1 ≤ Q.n
  hs : ProperPos (interiorModel Q) Q Q.n ⟨u, sh⟩
  he : ProperPos (interiorModel Q) Q Q.n ⟨(u + ee) % Q.n, eh⟩
  hee : (eh = 0 ∧ ee = L) ∨
    (eh ≠ 0 ∧ ee + 1 = L ∧ 0 < (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩)
  hxy : (interiorModel Q).param Q ⟨u, sh⟩ < ee + (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩

theorem chain_counted (C : Chain) :
    ∀ p, p < (chainModel C).W.n → ((chainModel C).counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6) :=
  fun p hp => chainModel_counted_iff C p hp

theorem keyCeil_le_succ {e : ℕ} {f : ℝ} : keyCeil e f ≤ e + 1 := by
  unfold keyCeil; split_ifs <;> omega

/-- An inner point of the chain model from a proper interior position with the same point. -/
theorem innerPt_of_mi {C : Chain} (hC : C.P = Q) {p h : ℕ} (hp : p < Q.n)
    (hpp : ProperPos (interiorModel Q) Q Q.n ⟨p, h⟩) {z : Point}
    (hz : z = (interiorModel Q).pos Q ⟨p, h⟩) : (chainModel C).InnerPt z := by
  obtain ⟨b1, b2⟩ := mi_pos_bound hp hpp
  rw [← hz, ← hC] at *
  exact innerPt_chain C b1 b2

section

variable {u L sh ee eh : ℕ} (h : SubOK Q u L sh ee eh)

include h in
theorem sub_ee_le : ee ≤ L := by
  rcases h.hee with ⟨-, h1⟩ | ⟨-, h1, -⟩ <;> omega

include h in
theorem sub_he' : ee < L ∨ (ee = L ∧ eh = 0) := by
  rcases h.hee with ⟨h0, h1⟩ | ⟨-, h1, -⟩
  · exact Or.inr ⟨h1, h0⟩
  · exact Or.inl (by omega)

include h in
theorem sub_keyCeil : keyCeil ee ((interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩) = L := by
  unfold keyCeil
  rcases h.hee with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · rw [ite_eq_left (by rw [h0]; rfl)]; exact h1
  · rw [ite_eq_right h2.ne']; exact h1

include h in
/-- **The chain arc of a subarc, no split.** -/
theorem chainArcs_one (hs : tau Q u L h.h1 h.h2 ≤ L) {γ : ℕ} (hγ : L ≤ γ) :
    CArc Q (ch Q u L h.h1 h.h2) ⟨6 + tau Q u L h.h1 h.h2, sh⟩
      ⟨6 + tau Q u L h.h1 h.h2 + ee, eh⟩ γ
      (oset (interiorWalk Q) u ((interiorModel Q).param Q ⟨u, sh⟩)
        (ee + (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩)) := by
  have hu := h.hu
  have h1 := h.h1
  have h2 := h.h2
  set τ := tau Q u L h.h1 h.h2 with hτ
  have ht : τ < 2 * L := tau_lt
  have hn : (MC Q u L h.h1 h.h2).W.n = 2 * L + 7 := cm_n'
  have hee := sub_ee_le h
  have hps := param_start hu h.h1 h.h2 sh
  have hpe := param_end_one hu h.h1 h.h2 (e := ee) (h₂ := eh) hs (sub_he' h)
  have hA := agree_pre hu h.h1 h.h2
  refine ⟨⟨by rw [hps]; exact h.hs.1, by rw [hps]; exact h.hs.2.1, h.hs.2.2⟩,
    ⟨by rw [hpe]; exact h.he.1, by rw [hpe]; exact h.he.2.1, h.he.2.2⟩,
    by show 6 + τ < _; rw [hn]; omega, by show 6 + τ + ee < _; rw [hn]; omega, ?_, ?_, ?_,
    chain_arcSet_one hu h.h1 h.h2 hs ⟨h.hs.1, h.hs.2.1⟩ ⟨h.he.1, h.he.2.1⟩ (sub_he' h) h.hxy⟩
  · right
    have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA Q (d := 0)
      (by omega) sh
    rw [Nat.add_zero, Nat.add_zero, mi_n, Nat.mod_eq_of_lt hu, hn,
      Nat.mod_eq_of_lt (show 6 + τ < 2 * L + 7 by omega)] at this
    exact innerPt_of_mi ch_P hu h.hs this.symm
  · by_cases h0 : eh = 0
    · left; exact h0
    right
    have hel : ee < L := by rcases sub_he' h with h' | ⟨-, h'⟩; exact h'; exact absurd h' h0
    have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA Q (d := ee)
      (by omega) eh
    rw [mi_n, hn, Nat.mod_eq_of_lt (show 6 + τ + ee < 2 * L + 7 by omega)] at this
    exact innerPt_of_mi ch_P (Nat.mod_lt _ (by omega)) h.he this.symm
  · have hc := chain_counted (ch Q u L h.h1 h.h2)
    have hk := sub_keyCeil h
    have hw := arcWt_off (chainModel (ch Q u L h.h1 h.h2)) (lo := 6) (hi := 2 * L + 6) hc
      (by rw [hn]; omega) (u := 6 + τ) (e := ee) (by rw [hn]; omega) (by omega)
      h.hs.1 h.hs.2.1 h.he.1 h.he.2.1 h.hxy (Or.inr ⟨by rw [hk]; omega, by rw [hn]; omega⟩)
    rw [hn, Nat.mod_eq_of_lt (show 6 + τ + ee < 2 * L + 7 by omega), hk] at hw
    rw [key_eq, key_eq, hps, hpe]
    exact hw.le.trans hγ

include h in
/-- **The chain arcs of a subarc, split at the top.** -/
theorem chainArcs_two (hs : L < tau Q u L h.h1 h.h2) {γ : ℕ} (hγ : L ≤ γ) :
    CArc Q (ch Q u L h.h1 h.h2) ⟨6 + tau Q u L h.h1 h.h2, sh⟩ ⟨2 * L + 6, 0⟩ γ
      (oset (interiorWalk Q) u ((interiorModel Q).param Q ⟨u, sh⟩)
        ((2 * L - tau Q u L h.h1 h.h2 : ℕ) : ℝ)) ∧
    CArc Q (ch Q u L h.h1 h.h2) ⟨6, 0⟩ ⟨6 + (ee - (2 * L - tau Q u L h.h1 h.h2)), eh⟩ γ
      (oset (interiorWalk Q) u ((2 * L - tau Q u L h.h1 h.h2 : ℕ) : ℝ)
        (ee + (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩)) := by
  have hu := h.hu
  have h1 := h.h1
  have h2 := h.h2
  set τ := tau Q u L h.h1 h.h2 with hτ
  set L₁ := 2 * L - τ with hL₁
  have ht : τ < 2 * L := tau_lt
  have hn : (MC Q u L h.h1 h.h2).W.n = 2 * L + 7 := cm_n'
  have hee := sub_ee_le h
  have hle : L₁ ≤ ee := by rcases h.hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
  have hps := param_start hu h.h1 h.h2 sh
  have hpe := param_end_two hu h.h1 h.h2 (e := ee) (h₂ := eh) hs hle (sub_he' h)
  have hA := agree_pre hu h.h1 h.h2
  have hA2 := agree_post hu h.h1 h.h2 hs
  have hxy2 : (L₁ : ℝ) < ee + (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩ := by
    rcases h.hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
    · have : (L₁ : ℝ) < ee := by exact_mod_cast (show L₁ < ee by omega)
      have : (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩ = 0 := by rw [h0]; rfl
      linarith
    · have : (L₁ : ℝ) ≤ ee := by exact_mod_cast hle
      linarith
  obtain ⟨hS1, hS2⟩ := chain_arcSet_two hu h.h1 h.h2 hs hle ⟨h.hs.1, h.hs.2.1⟩
    ⟨h.he.1, h.he.2.1⟩ (sub_he' h) hxy2
  have hc := chain_counted (ch Q u L h.h1 h.h2)
  have hk := sub_keyCeil h
  constructor
  · refine ⟨⟨by rw [hps]; exact h.hs.1, by rw [hps]; exact h.hs.2.1, h.hs.2.2⟩,
      ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩,
      by show 6 + τ < _; rw [hn]; omega, by show 2 * L + 6 < _; rw [hn]; omega, ?_,
      Or.inl rfl, ?_, hS1⟩
    · right
      have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA Q (d := 0)
        (by omega) sh
      rw [Nat.add_zero, Nat.add_zero, mi_n, Nat.mod_eq_of_lt hu, hn,
        Nat.mod_eq_of_lt (show 6 + τ < 2 * L + 7 by omega)] at this
      exact innerPt_of_mi ch_P hu h.hs this.symm
    · have hw := arcWt_off (chainModel (ch Q u L h.h1 h.h2)) (lo := 6) (hi := 2 * L + 6) hc
        (by rw [hn]; omega) (u := 6 + τ) (e := L₁) (t₂ := 0) (by rw [hn]; omega) (by omega)
        h.hs.1 h.hs.2.1 le_rfl zero_lt_one
        (by have : (1 : ℝ) ≤ L₁ := by exact_mod_cast (show 1 ≤ L₁ by omega)
            linarith [h.hs.2.1])
        (Or.inr ⟨by unfold keyCeil; rw [ite_eq_left rfl]; omega, by rw [hn]; omega⟩)
      rw [hn, Nat.mod_eq_of_lt (show 6 + τ + L₁ < 2 * L + 7 by omega)] at hw
      have hk0 : keyCeil L₁ (0 : ℝ) = L₁ := by unfold keyCeil; rw [ite_eq_left rfl]
      rw [key_eq, key_eq, hps, param_zero, add_zero,
        show ((2 * L + 6 : ℕ) : ℝ) = ((6 + τ + L₁ : ℕ) : ℝ) + 0 by
          rw [add_zero]; congr 1; omega]
      rw [hw, hk0]; omega
  · refine ⟨⟨le_rfl, zero_lt_one, Nat.zero_le _⟩,
      ⟨by rw [hpe]; exact h.he.1, by rw [hpe]; exact h.he.2.1, h.he.2.2⟩,
      by show 6 < _; rw [hn]; omega, by show 6 + (ee - L₁) < _; rw [hn]; omega, Or.inl rfl,
      ?_, ?_, hS2⟩
    · by_cases h0 : eh = 0
      · left; exact h0
      right
      have hel : ee < L := by rcases sub_he' h with h' | ⟨-, h'⟩; exact h'; exact absurd h' h0
      have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA2 Q (d := ee - L₁)
        (by omega) eh
      rw [mi_n, hn, Nat.mod_eq_of_lt (show 6 + (ee - L₁) < 2 * L + 7 by omega),
        show u + L₁ + (ee - L₁) = u + ee by omega] at this
      exact innerPt_of_mi ch_P (Nat.mod_lt _ (by omega)) h.he this.symm
    · have hpos : (0 : ℝ) < ((ee - L₁ : ℕ) : ℝ) + (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩ := by
        have e1 : ((ee - L₁ : ℕ) : ℝ) = ee - L₁ := Nat.cast_sub hle
        rw [e1]; linarith
      have hw := arcWt_off (chainModel (ch Q u L h.h1 h.h2)) (lo := 6) (hi := 2 * L + 6) hc
        (by rw [hn]; omega) (u := 6) (e := ee - L₁) (t₁ := 0) (by rw [hn]; omega) le_rfl
        le_rfl zero_lt_one h.he.1 h.he.2.1 hpos
        (Or.inr ⟨by have := keyCeil_le_succ (e := ee - L₁)
                        (f := (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩)
                    have := keyCeil_le (e := ee - L₁)
                        (f := (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩)
                    omega, by rw [hn]; omega⟩)
      rw [hn, Nat.mod_eq_of_lt (show 6 + (ee - L₁) < 2 * L + 7 by omega)] at hw
      rw [key_eq, key_eq, hpe, param_zero, show ((6 : ℕ) : ℝ) + 0 = ((6 : ℕ) : ℝ) + 0 from rfl]
      rw [hw]
      have := keyCeil_le_succ (e := ee - L₁) (f := (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩)
      have hk2 : keyCeil (ee - L₁) ((interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩) ≤ L := by
        unfold keyCeil at hk ⊢
        split_ifs at hk ⊢ <;> omega
      omega

end

end

end IOrc

end Chazelle.Core
