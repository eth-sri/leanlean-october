module

public import Chazelle.Core.DownPhaseDrvRCostSpec
public import Chazelle.Core.Lemma41Bridge

/-!
# Down-phase driver: the cost arithmetic of one level (D11), `DrvR.LvCostSpec`

**`lvCostSpec : DrvR.LvCostSpec`**.  Everything is measured in `E = 2^(μ/75)` (the tools of
`Lemma41Bridge`): `lemma41Nat μ ≥ μ² E^74` (`lemma41Nat_ge`), `lvNch μ ≤ 223 E^60` and
`lvNch μ ≤ 223 · 2^μ` (`lvNch_le_E`, `lvNch_le_pow`), and at `γ_r = lvGr μ = 2^(⌈βμ⌉+12)`:
`γ_r ≤ 8192 E^15`, `⌈log₂ γ_r⌉ + 1 ≤ 2μ`, `cutGran γ_r ≤ 19216 E^3`,
`⌈(H(γ_r) (γ_r + 1)²)^{1/3}⌉ ≤ 11001 E^11` (`lvGr_*`); hence
`(lvNch + 1) F(γ_r) G(γ_r) (H(γ_r) + ⌈log₂ γ_r⌉ + 1) ≤ 2·10^11 κo² μ² E^74`.
The size threshold: `n₀ = 2^30` (`lv_n0`).
-/

namespace Chazelle.Core

namespace DrvLC

open Chazelle.Cost L41

@[expose] public section

/-! ## The size threshold -/

theorem five_ceilBeta_le (g : ℕ) : 5 * Cost.ceilBeta g ≤ g + 5 := by
  have h := L41.ceilBeta_le_real g
  have : ((5 * Cost.ceilBeta g : ℕ) : ℝ) ≤ ((g + 5 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- **(a)** The levels' size threshold. -/
theorem lv_n0 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 2 ^ (Cost.ceilBeta (topGrade n) + 13) + 200 ≤ n := by
  refine ⟨2 ^ 30 + 2, fun n hn => ?_⟩
  unfold topGrade
  set p := Nat.clog 2 (n - 1) with hp
  have hp30 : 30 ≤ p := by
    by_contra h
    push Not at h
    have h1 : n - 1 ≤ 2 ^ p := Nat.le_pow_clog (by norm_num) _
    have h2 : 2 ^ p ≤ 2 ^ 29 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 29 + 2 ≤ 2 ^ 30 := by norm_num
    omega
  have hlt : 2 ^ (p - 1) < n - 1 := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n - 1)
      (by have : (2 : ℕ) ≤ 2 ^ 30 := by norm_num
          omega)
    simpa [Nat.pred_eq_sub_one, ← hp] using this
  have hcb := five_ceilBeta_le p
  have h1 : 2 ^ (Cost.ceilBeta p + 13) ≤ 2 ^ (p - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 200 ≤ 2 ^ (p - 2) := by
    have : (2 : ℕ) ^ 8 ≤ 2 ^ (p - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-! ## Bounds in `E = 2^(μ/75)` -/

/-- `E = 2^(μ/75)`. -/
noncomputable def E (μ : ℕ) : ℝ := (2 : ℝ) ^ ((μ : ℝ) / 75)

theorem E_pos (μ : ℕ) : 0 < E μ := by unfold E; positivity

theorem E_one_le (μ : ℕ) : 1 ≤ E μ := by unfold E; exact L41.one_le_E μ

theorem E_pow_nonneg (μ k : ℕ) : 0 ≤ E μ ^ k := pow_nonneg (E_pos μ).le k

theorem E_pow_ge {μ a b : ℕ} (h : a ≤ b) : E μ ^ a ≤ E μ ^ b := pow_le_pow_right₀ (E_one_le μ) h

/-- `lemma41Nat μ ≥ μ² E^74`. -/
theorem lemma41Nat_ge (μ : ℕ) : (μ : ℝ) ^ 2 * E μ ^ 74 ≤ (lemma41Nat μ : ℝ) := by
  have h := Nat.le_ceil ((μ : ℝ) ^ 2 * ((Nat.clog 2 μ : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * μ))
  have hE : E μ ^ 74 = (2 : ℝ) ^ ((74 : ℝ) / 75 * μ) := by
    unfold E; rw [L41.E_pow]; congr 1; push_cast; ring
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ ((74 : ℝ) / 75 * μ) := by positivity
  unfold lemma41Nat
  rw [hE]
  calc (μ : ℝ) ^ 2 * (2 : ℝ) ^ ((74 : ℝ) / 75 * μ)
      ≤ (μ : ℝ) ^ 2 * ((Nat.clog 2 μ : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * μ) := by
        apply mul_le_mul_of_nonneg_right _ hp
        nlinarith
    _ ≤ _ := h

/-- `2^μ = E^75`. -/
theorem two_pow_eq_E (μ : ℕ) : (2 : ℝ) ^ μ = E μ ^ 75 := by
  unfold E; rw [L41.E_pow, ← Real.rpow_natCast]; congr 1; push_cast; field_simp

/-- `E^15 ≤ 2^⌈βμ⌉`. -/
theorem E15_le (μ : ℕ) : E μ ^ 15 ≤ (2 : ℝ) ^ Cost.ceilBeta μ := by
  unfold E; rw [L41.E_pow, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := L41.le_ceilBeta_real μ
  push_cast; linarith

theorem regCap_eq : DrvR.regCap = 130 := rfl

/-- The chord bound times its denominator. -/
theorem lvNch_mul (μ : ℕ) :
    DrvR.lvNch μ * (3 * 2 ^ (Cost.ceilBeta μ + 10) + 1) ≤ 18480 * (20 * 2 ^ μ + 17) := by
  unfold DrvR.lvNch
  rw [regCap_eq]
  exact Nat.div_mul_le_self _ _

/-- `lvNch μ ≤ 223 · 2^μ`. -/
theorem lvNch_le_pow (μ : ℕ) : DrvR.lvNch μ ≤ 223 * 2 ^ μ := by
  have h := lvNch_mul μ
  have h1 : 3072 ≤ 3 * 2 ^ (Cost.ceilBeta μ + 10) + 1 := by
    have : (2 : ℕ) ^ 10 ≤ 2 ^ (Cost.ceilBeta μ + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : DrvR.lvNch μ * 3072 ≤ DrvR.lvNch μ * (3 * 2 ^ (Cost.ceilBeta μ + 10) + 1) :=
    Nat.mul_le_mul_left _ h1
  have h3 : 1 ≤ 2 ^ μ := Nat.one_le_two_pow
  generalize DrvR.lvNch μ * (3 * 2 ^ (Cost.ceilBeta μ + 10) + 1) = a at h h2
  generalize 2 ^ μ = T at h h3 ⊢
  generalize DrvR.lvNch μ = L at h2 ⊢
  omega

/-- `lvNch μ ≤ 223 E^60`. -/
theorem lvNch_le_E (μ : ℕ) : (DrvR.lvNch μ : ℝ) ≤ 223 * E μ ^ 60 := by
  have h := lvNch_mul μ
  have hR : (DrvR.lvNch μ : ℝ) * (3072 * (2 : ℝ) ^ Cost.ceilBeta μ) ≤ 683760 * (2 : ℝ) ^ μ := by
    have h' : ((DrvR.lvNch μ * (3 * 2 ^ (Cost.ceilBeta μ + 10) + 1) : ℕ) : ℝ) ≤
        ((18480 * (20 * 2 ^ μ + 17) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ μ := one_le_pow₀ (by norm_num)
    have e10 : (2 : ℝ) ^ (Cost.ceilBeta μ + 10) = 1024 * (2 : ℝ) ^ Cost.ceilBeta μ := by
      rw [pow_add]; norm_num; ring
    rw [e10] at h'
    have hL : (0 : ℝ) ≤ (DrvR.lvNch μ : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h15 := E15_le μ
  have hL : (0 : ℝ) ≤ (DrvR.lvNch μ : ℝ) := Nat.cast_nonneg _
  have hEp : 0 < E μ ^ 15 := pow_pos (E_pos μ) 15
  rw [two_pow_eq_E μ] at hR
  have h1 : (DrvR.lvNch μ : ℝ) * (3072 * E μ ^ 15) ≤ 683760 * E μ ^ 75 :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hL) hR
  have e75 : E μ ^ 75 = E μ ^ 15 * E μ ^ 60 := by rw [← pow_add]
  rw [e75] at h1
  have h2 : (DrvR.lvNch μ : ℝ) * 3072 ≤ 683760 * E μ ^ 60 := by
    have : E μ ^ 15 * ((DrvR.lvNch μ : ℝ) * 3072) ≤ E μ ^ 15 * (683760 * E μ ^ 60) := by
      nlinarith
    exact le_of_mul_le_mul_left this hEp
  have : (0 : ℝ) ≤ E μ ^ 60 := E_pow_nonneg μ 60
  nlinarith

/-! ## The oracle costs at `γ_r = lvGr μ` -/

theorem lvGr_clog (μ : ℕ) : Nat.clog 2 (DrvR.lvGr μ) = Cost.ceilBeta μ + 12 := by
  unfold DrvR.lvGr; exact Nat.clog_pow 2 _ (by norm_num)

theorem lvGr_clog_le {μ : ℕ} (h : 15 ≤ μ) : Nat.clog 2 (DrvR.lvGr μ) + 1 ≤ 2 * μ := by
  rw [lvGr_clog]; have := five_ceilBeta_le μ; omega

theorem ceilBeta_real (μ : ℕ) : (Cost.ceilBeta μ : ℝ) ≤ (μ : ℝ) / 5 + 1 := L41.ceilBeta_le_real μ

/-- `γ_r ≤ 8192 E^15`. -/
theorem lvGr_le_E (μ : ℕ) : (DrvR.lvGr μ : ℝ) ≤ 8192 * E μ ^ 15 := by
  have h := L41.two_pow_le_E (n := Cost.ceilBeta μ + 12) (lam := μ) (k := 15) (b := 13)
    (by have := ceilBeta_real μ; push_cast; linarith)
  have h13 : (2 : ℝ) ^ (13 : ℝ) = 8192 := by norm_num
  rw [h13] at h
  unfold DrvR.lvGr E; push_cast; exact h

/-- `H(γ_r) ≤ 19216 E^3`. -/
theorem cutGran_lvGr_le (μ : ℕ) : (cutGran (DrvR.lvGr μ) : ℝ) ≤ 19216 * E μ ^ 3 := by
  unfold cutGran
  rw [lvGr_clog]
  have h1 := gradeGran_le_real (Cost.ceilBeta μ + 12)
  have h2 := L41.two_pow_le_E (n := Cost.ceilBeta (Cost.ceilBeta μ + 12)) (lam := μ) (k := 3)
    (b := 4) (by
      have a1 := ceilBeta_real (Cost.ceilBeta μ + 12)
      have a2 := ceilBeta_real μ
      push_cast at a1 ⊢; linarith)
  have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
  rw [h16] at h2
  unfold E
  linarith

/-- `⌈(H(γ_r) (γ_r + 1)²)^{1/3}⌉ ≤ 11001 E^11`. -/
theorem rpow_lvGr_le (μ : ℕ) :
    (rpowCeil (cutGran (DrvR.lvGr μ) * (DrvR.lvGr μ + 1) ^ 2) ((1 : ℝ) / 3) : ℝ) ≤
      11001 * E μ ^ 11 := by
  have hE1 : 1 ≤ E μ := E_one_le μ
  have hH := cutGran_lvGr_le μ
  have hG := lvGr_le_E μ
  have hG1 : ((DrvR.lvGr μ : ℕ) : ℝ) + 1 ≤ 8193 * E μ ^ 15 := by
    have : (1 : ℝ) ≤ E μ ^ 15 := one_le_pow₀ hE1
    linarith
  obtain ⟨X, hX⟩ : ∃ X, cutGran (DrvR.lvGr μ) * (DrvR.lvGr μ + 1) ^ 2 = X := ⟨_, rfl⟩
  obtain ⟨Hc, hHc⟩ : ∃ Hc, (cutGran (DrvR.lvGr μ) : ℝ) = Hc := ⟨_, rfl⟩
  obtain ⟨G, hGG⟩ : ∃ G, (DrvR.lvGr μ : ℝ) = G := ⟨_, rfl⟩
  have hXc : (X : ℝ) = Hc * (G + 1) ^ 2 := by rw [← hX, ← hHc, ← hGG]; push_cast; ring
  rw [hHc] at hH
  rw [hGG] at hG1
  rw [hX]
  have hG0 : (0 : ℝ) ≤ G + 1 := by
    rw [← hGG]; have := Nat.cast_nonneg (α := ℝ) (DrvR.lvGr μ); linarith
  have hXR : (X : ℝ) ≤ (11000 * E μ ^ 11) ^ 3 := by
    rw [hXc]
    calc Hc * (G + 1) ^ 2
        ≤ (19216 * E μ ^ 3) * (8193 * E μ ^ 15) ^ 2 := by
          apply mul_le_mul hH (pow_le_pow_left₀ hG0 hG1 2) (pow_nonneg hG0 2)
            (by have := E_pow_nonneg μ 3; linarith)
      _ ≤ (11000 * E μ ^ 11) ^ 3 := by
          have : (0 : ℝ) ≤ E μ ^ 33 := E_pow_nonneg μ 33
          have e1 : (19216 * E μ ^ 3) * (8193 * E μ ^ 15) ^ 2 = 1289878784784 * E μ ^ 33 := by
            ring
          have e2 : (11000 * E μ ^ 11) ^ 3 = 1331000000000 * E μ ^ 33 := by ring
          rw [e1, e2]; exact mul_le_mul_of_nonneg_right (by norm_num) this
  have hroot : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ 11000 * E μ ^ 11 := by
    have h0 : (0 : ℝ) ≤ 11000 * E μ ^ 11 := by have := E_pow_nonneg μ 11; linarith
    calc (X : ℝ) ^ ((1 : ℝ) / 3) ≤ ((11000 * E μ ^ 11) ^ 3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hXR (by norm_num)
      _ = 11000 * E μ ^ 11 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
  unfold rpowCeil
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg X) ((1 : ℝ) / 3))
  have : (1 : ℝ) ≤ E μ ^ 11 := one_le_pow₀ hE1
  linarith

/-- `F(γ_r) ≤ 22003 κo μ E^11`. -/
theorem shCost_lvGr_le (κo : ℕ) {μ : ℕ} (h : 15 ≤ μ) :
    (DrvR.shCost κo (DrvR.lvGr μ) : ℝ) ≤ 22003 * κo * μ * E μ ^ 11 := by
  unfold DrvR.shCost
  have hc : ((Nat.clog 2 (DrvR.lvGr μ) + 1 : ℕ) : ℝ) ≤ 2 * μ := by
    exact_mod_cast lvGr_clog_le h
  have hR := rpow_lvGr_le μ
  have hκ : (0 : ℝ) ≤ κo := Nat.cast_nonneg _
  have hμ : (15 : ℝ) ≤ μ := by exact_mod_cast h
  have hE : (1 : ℝ) ≤ E μ ^ 11 := one_le_pow₀ (E_one_le μ)
  have hc0 : (0 : ℝ) ≤ ((Nat.clog 2 (DrvR.lvGr μ) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hR0 : (0 : ℝ) ≤ (rpowCeil (cutGran (DrvR.lvGr μ) * (DrvR.lvGr μ + 1) ^ 2)
    ((1 : ℝ) / 3) : ℝ) := Nat.cast_nonneg _
  push_cast at hc hc0 ⊢
  have h1 : (κo : ℝ) * ((Nat.clog 2 (DrvR.lvGr μ) : ℝ) + 1) *
      (rpowCeil (cutGran (DrvR.lvGr μ) * (DrvR.lvGr μ + 1) ^ 2) ((1 : ℝ) / 3) : ℝ) ≤
      κo * (2 * μ) * (11001 * E μ ^ 11) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hc hκ) hR hR0 (by
      have : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ (κo : ℝ) * (2 * μ) := by positivity
      exact this)
  have h2 : (κo : ℝ) ≤ κo * μ * E μ ^ 11 := by
    have : (1 : ℝ) ≤ μ * E μ ^ 11 := by nlinarith
    nlinarith
  nlinarith

/-- `G(γ_r) ≤ 2 κo μ`. -/
theorem cuCost_lvGr_le (κo : ℕ) {μ : ℕ} (h : 15 ≤ μ) :
    (DrvR.cuCost κo (DrvR.lvGr μ) : ℝ) ≤ 2 * κo * μ := by
  unfold DrvR.cuCost
  have hc : ((Nat.clog 2 (DrvR.lvGr μ) + 1 : ℕ) : ℝ) ≤ 2 * μ := by
    exact_mod_cast lvGr_clog_le h
  push_cast at hc ⊢
  nlinarith

/-- `H(γ_r) + ⌈log₂ γ_r⌉ + 1 ≤ 19516 E^3`. -/
theorem hTerm_le {μ : ℕ} (h : 15 ≤ μ) :
    ((cutGran (DrvR.lvGr μ) + Nat.clog 2 (DrvR.lvGr μ) + 1 : ℕ) : ℝ) ≤ 19516 * E μ ^ 3 := by
  have hc : ((Nat.clog 2 (DrvR.lvGr μ) + 1 : ℕ) : ℝ) ≤ 2 * μ := by
    exact_mod_cast lvGr_clog_le h
  have hH := cutGran_lvGr_le μ
  have hμE : (μ : ℝ) ≤ 150 * E μ := by unfold E; exact L41.lam_le_E μ
  have hE3 : E μ ≤ E μ ^ 3 := by
    have := E_one_le μ
    calc E μ = E μ ^ 1 := (pow_one _).symm
      _ ≤ E μ ^ 3 := pow_le_pow_right₀ this (by norm_num)
  push_cast at hc ⊢
  have : (μ : ℝ) ≤ 150 * E μ := hμE
  linarith

/-! ## The level cost -/

theorem clog_lvNch_le (μ : ℕ) : Nat.clog 2 (4 * DrvR.lvNch μ + 4) ≤ μ + 10 := by
  apply Nat.clog_le_of_le_pow
  have h := lvNch_le_pow μ
  have h1 : 1 ≤ 2 ^ μ := Nat.one_le_two_pow
  have e : 2 ^ (μ + 10) = 1024 * 2 ^ μ := by rw [pow_add]; ring
  rw [e]
  generalize 2 ^ μ = T at h h1 ⊢
  omega

set_option maxHeartbeats 1000000 in
/-- **The cost arithmetic of one level (D11).** -/
theorem lvCostSpec : DrvR.LvCostSpec := by
  refine ⟨lv_n0, fun κo => ⟨200000000000 * (κo ^ 2 + 1), fun μ hμ => ?_⟩⟩
  have hμR : (15 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hL := lemma41Nat_ge μ
  have hE60 : E μ ^ 60 ≤ E μ ^ 74 := E_pow_ge (by norm_num)
  have hE0 : 0 ≤ E μ ^ 60 := E_pow_nonneg μ 60
  have hμ2 : (1 : ℝ) ≤ (μ : ℝ) ^ 2 := by nlinarith
  have hN := lvNch_le_E μ
  have hN1 : ((DrvR.lvNch μ : ℝ) + 1) ≤ 224 * E μ ^ 60 := by
    have : (1 : ℝ) ≤ E μ ^ 60 := one_le_pow₀ (E_one_le μ)
    linarith
  -- the constant
  have hκ : ∀ c : ℕ, c ≤ 200000000000 → c * lemma41Nat μ ≤
      200000000000 * (κo ^ 2 + 1) * (lemma41Nat μ + 1) := fun c hc => by
    have h1 : c * lemma41Nat μ ≤ 200000000000 * lemma41Nat μ := Nat.mul_le_mul_right _ hc
    have h2 : 200000000000 * lemma41Nat μ ≤ 200000000000 * (κo ^ 2 + 1) * (lemma41Nat μ + 1) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by nlinarith)
    exact h1.trans h2
  refine ⟨?_, ?_, ?_⟩
  · -- the chords
    have hR : (DrvR.lvNch μ : ℝ) ≤ ((223 * lemma41Nat μ : ℕ) : ℝ) := by
      push_cast
      calc (DrvR.lvNch μ : ℝ) ≤ 223 * E μ ^ 60 := hN
        _ ≤ 223 * ((μ : ℝ) ^ 2 * E μ ^ 74) := by nlinarith
        _ ≤ 223 * (lemma41Nat μ : ℝ) := by linarith
    have := (Nat.cast_le (α := ℝ)).1 hR
    exact this.trans (hκ 223 (by norm_num))
  · -- the splice
    have hc := clog_lvNch_le μ
    have hc' : ((Nat.clog 2 (4 * DrvR.lvNch μ + 4) + 1 : ℕ) : ℝ) ≤ 2 * μ := by
      have : Nat.clog 2 (4 * DrvR.lvNch μ + 4) + 1 ≤ 2 * μ := by omega
      exact_mod_cast this
    have hR : (((DrvR.lvNch μ + 1) * (Nat.clog 2 (4 * DrvR.lvNch μ + 4) + 1) : ℕ) : ℝ) ≤
        ((448 * lemma41Nat μ : ℕ) : ℝ) := by
      have hc0 : (0 : ℝ) ≤ ((Nat.clog 2 (4 * DrvR.lvNch μ + 4) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [Nat.cast_mul]
      calc ((DrvR.lvNch μ + 1 : ℕ) : ℝ) * ((Nat.clog 2 (4 * DrvR.lvNch μ + 4) + 1 : ℕ) : ℝ)
          ≤ (224 * E μ ^ 60) * (2 * μ) := by
            apply mul_le_mul (by push_cast; exact hN1) hc' hc0 (by linarith)
        _ ≤ 448 * ((μ : ℝ) ^ 2 * E μ ^ 74) := by
            have a : (μ : ℝ) * E μ ^ 60 ≤ (μ : ℝ) ^ 2 * E μ ^ 74 :=
              mul_le_mul (by nlinarith) hE60 hE0 (by positivity)
            have e : 224 * E μ ^ 60 * (2 * (μ : ℝ)) = 448 * ((μ : ℝ) * E μ ^ 60) := by ring
            rw [e]; linarith
        _ ≤ ((448 * lemma41Nat μ : ℕ) : ℝ) := by push_cast; linarith
    have := (Nat.cast_le (α := ℝ)).1 hR
    exact this.trans (hκ 448 (by norm_num))
  · -- the restoration rounds
    have hF := shCost_lvGr_le κo hμ
    have hG := cuCost_lvGr_le κo hμ
    have hH := hTerm_le hμ
    have hE11 := E_pow_nonneg μ 11
    have hF0 : (0 : ℝ) ≤ (DrvR.shCost κo (DrvR.lvGr μ) : ℝ) := Nat.cast_nonneg _
    have hG0 : (0 : ℝ) ≤ (DrvR.cuCost κo (DrvR.lvGr μ) : ℝ) := Nat.cast_nonneg _
    have hH0 : (0 : ℝ) ≤ ((cutGran (DrvR.lvGr μ) + Nat.clog 2 (DrvR.lvGr μ) + 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hP : ((((DrvR.lvNch μ + 1) * DrvR.shCost κo (DrvR.lvGr μ) * DrvR.cuCost κo (DrvR.lvGr μ) *
        (cutGran (DrvR.lvGr μ) + Nat.clog 2 (DrvR.lvGr μ) + 1)) : ℕ) : ℝ) ≤
        (224 * E μ ^ 60) * (22003 * κo * μ * E μ ^ 11) * (2 * κo * μ) * (19516 * E μ ^ 3) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
      have hA : ((DrvR.lvNch μ + 1 : ℕ) : ℝ) ≤ 224 * E μ ^ 60 := by push_cast; exact hN1
      have p1 : (0 : ℝ) ≤ 224 * E μ ^ 60 := by linarith
      have p2 : (0 : ℝ) ≤ 22003 * κo * μ * E μ ^ 11 :=
        mul_nonneg (by positivity) hE11
      have p3 : (0 : ℝ) ≤ 2 * κo * μ := by positivity
      apply mul_le_mul _ hH hH0 (mul_nonneg (mul_nonneg p1 p2) p3)
      apply mul_le_mul _ hG hG0 (mul_nonneg p1 p2)
      exact mul_le_mul hA hF hF0 p1
    have hbig : (224 * E μ ^ 60) * (22003 * κo * μ * E μ ^ 11) * (2 * κo * μ) *
        (19516 * E μ ^ 3) = 192375925504 * ((κo : ℝ) ^ 2 * ((μ : ℝ) ^ 2 * E μ ^ 74)) := by
      have e : E μ ^ 74 = E μ ^ 60 * E μ ^ 11 * E μ ^ 3 := by rw [← pow_add, ← pow_add]
      rw [e]; ring
    rw [hbig] at hP
    have hk2 : (0 : ℝ) ≤ (κo : ℝ) ^ 2 := by positivity
    have hR : (((DrvR.lvNch μ + 1) * DrvR.shCost κo (DrvR.lvGr μ) * DrvR.cuCost κo (DrvR.lvGr μ) *
        (cutGran (DrvR.lvGr μ) + Nat.clog 2 (DrvR.lvGr μ) + 1) : ℕ) : ℝ) ≤
        ((200000000000 * (κo ^ 2 * lemma41Nat μ) : ℕ) : ℝ) := by
      refine hP.trans ?_
      push_cast
      have : (κo : ℝ) ^ 2 * ((μ : ℝ) ^ 2 * E μ ^ 74) ≤ (κo : ℝ) ^ 2 * (lemma41Nat μ : ℝ) :=
        mul_le_mul_of_nonneg_left hL hk2
      nlinarith
    have := (Nat.cast_le (α := ℝ)).1 hR
    refine this.trans ?_
    have e : 200000000000 * (κo ^ 2 + 1) * (lemma41Nat μ + 1) =
        200000000000 * (κo ^ 2 * lemma41Nat μ) + 200000000000 * (κo ^ 2 + lemma41Nat μ + 1) := by
      ring
    rw [e]
    exact Nat.le_add_right _ _

end

end DrvLC

end Chazelle.Core
