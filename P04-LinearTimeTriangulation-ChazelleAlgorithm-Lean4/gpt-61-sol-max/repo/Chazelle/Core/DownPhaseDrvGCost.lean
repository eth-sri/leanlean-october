module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.Lemma41Bridge

/-!
# Down-phase driver, region procedure (D5), part 2: the cost of one merge

A merge of the region chain (merge grade `μ ≥ 7`, pieces of granularity `γ₀`,
`2 γ'_μ ≤ γ₀ ≤ 4096 · 2^⌈βμ⌉`, at most `128` merges before, union of `M ≤ 20 (2 · 2^μ + 1)`
edges) costs (the cost of `MergeSpec` with the oracles of `ShootCutSpec`)
`κM (x + y + 1) F(γ + 1) G(γ + 1) (H(γ + 1) + ⌈log₂ (M + 1)⌉ + 1)`, where the chord counts
`x, y` of the parts are bounded by Lemma 2.3 (`x (γ₀ + 1) ≤ 18480 (2M + 1)`).  This is
`O(lemma41Nat μ)` (`mcost_le`):

* `γ + 1 ≤ γ'_{μ+65}` and `M ≤ 2^(μ+65)`, so the oracle factors are at most `phiL` at grade
  `μ + 65`, `≤ K₁ (μ + 65)² E'^14` (`L41.phiL_le`), with `E' = 2^((μ+65)/75) ≤ 2 E`;
* the chords: `x + y + 1 ≤ 2236081 E^60` (`E = 2^(μ/75)`, `γ₀ + 1 ≥ 2 · 2^(μ/5)`).
-/

namespace Chazelle.Core

namespace DrvG

open Chazelle.Cost L41

@[expose] public section

/-- The cost of one merge (the shape of `MergeSpec`'s cost with a constant `κ`). -/
def mcost (κM : ℕ) (F G H : ℕ → ℕ) (x y γ M : ℕ) : ℕ :=
  κM * (x + y + 1) * F (γ + fuseLoss) * G (γ + fuseLoss) *
    (H (γ + fuseLoss) + Nat.clog 2 (M + 1) + 1)

/-- The constant of `mcost_le`. -/
def mcK (κM κ : ℕ) : ℕ := κM * κ ^ 2 * 14704 * 3 * 19368 * 121 * 8192 * 2236081 + 1

theorem ceilBeta_add_65 (μ : ℕ) : ceilBeta μ + 13 ≤ ceilBeta (μ + 65) := by
  unfold ceilBeta
  rw [beta_eq]
  have e : (1 / 5 : ℝ) * ((μ + 65 : ℕ) : ℝ) = (1 / 5 : ℝ) * μ + (13 : ℕ) := by grind
  rw [e, Nat.ceil_add_natCast (by positivity)]

/-- The granularity of the merges is served at grade `μ + 65`. -/
theorem gamma_le_gradeGran {μ γ₀ γ : ℕ} (hg1 : γ₀ ≤ 4096 * 2 ^ ceilBeta μ) (hγ : γ ≤ γ₀ + 128) :
    γ + fuseLoss ≤ gradeGran (μ + 65) := by
  have h1 : 2 ^ (ceilBeta μ + 13) ≤ 2 ^ ceilBeta (μ + 65) :=
    Nat.pow_le_pow_right (by norm_num) (ceilBeta_add_65 μ)
  core_grind

theorem M_le_pow {μ M : ℕ} (hM : M ≤ 20 * (2 * 2 ^ μ + 1)) : M ≤ 2 ^ (μ + 65) := by
  grind

/-- The oracle factors of one merge are at most those of grade `μ + 65`. -/
theorem mcost_le_phiL (κM κ : ℕ) {μ γ₀ γ M x y : ℕ} (hg1 : γ₀ ≤ 4096 * 2 ^ ceilBeta μ)
    (hγ : γ ≤ γ₀ + 128) :
    mcost κM (scF κ) (scG κ) cutGran x y γ M ≤
      (x + y + 1) * phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran (μ + 65)) M := by
  have hg := gamma_le_gradeGran hg1 hγ
  have hF := scF_mono κ hg
  have hG := scG_mono κ hg
  have hH := cutGran_mono hg
  unfold mcost phiL
  calc κM * (x + y + 1) * scF κ (γ + fuseLoss) * scG κ (γ + fuseLoss) *
        (cutGran (γ + fuseLoss) + Nat.clog 2 (M + 1) + 1)
      ≤ κM * (x + y + 1) * scF κ (gradeGran (μ + 65)) * scG κ (gradeGran (μ + 65)) *
        (cutGran (gradeGran (μ + 65)) + Nat.clog 2 (M + 1) + 1) := by gcongr
    _ = (x + y + 1) * (κM * scF κ (gradeGran (μ + 65)) * scG κ (gradeGran (μ + 65)) *
        (cutGran (gradeGran (μ + 65)) + Nat.clog 2 (M + 1) + 1)) := by ring

/-- `E^75 = 2^μ`. -/
theorem E_pow_75 (μ : ℕ) : ((2 : ℝ) ^ ((μ : ℝ) / 75)) ^ 75 = (2 : ℝ) ^ μ := by
  simp_all [E_pow, Real.rpow_natCast] 

/-- **The cost of one merge of the region chain is `O(lemma41Nat μ)`.** -/
theorem mcost_le (κM κ : ℕ) {μ γ₀ γ M x y : ℕ} (h7 : 7 ≤ μ) (hg0 : 2 * gradeGran μ ≤ γ₀)
    (hg1 : γ₀ ≤ 4096 * 2 ^ ceilBeta μ) (hγ : γ ≤ γ₀ + 128) (hM : M ≤ 20 * (2 * 2 ^ μ + 1))
    (hx : x * (γ₀ + 1) ≤ 18480 * (2 * M + 1)) (hy : y * (γ₀ + 1) ≤ 18480 * (2 * M + 1)) :
    mcost κM (scF κ) (scG κ) cutGran x y γ M ≤ mcK κM κ * lemma41Nat μ := by
  have h1 := mcost_le_phiL κM κ (x := x) (y := y) (M := M) hg1 hγ
  have hφ := phiL_le κM κ (lam := μ + 65) (L := M) (by omega) (M_le_pow hM)
  set E := (2 : ℝ) ^ ((μ : ℝ) / 75) with hE
  have hE1 : 1 ≤ E := one_le_E μ
  -- `E' ^ 14 ≤ 2^13 E^14`
  have hE' : ((2 : ℝ) ^ (((μ + 65 : ℕ) : ℝ) / 75)) ^ 14 ≤ 8192 * E ^ 14 := by
    rw [E_pow, hE, E_pow]
    have : (2 : ℝ) ^ ((14 : ℕ) * ((μ + 65 : ℕ) : ℝ) / 75) =
        (2 : ℝ) ^ ((910 : ℝ) / 75) * (2 : ℝ) ^ ((14 : ℕ) * (μ : ℝ) / 75) := by
      rw [← Real.rpow_add (by norm_num)]; grind
    rw [this]
    have h13 : (2 : ℝ) ^ ((910 : ℝ) / 75) ≤ (2 : ℝ) ^ (13 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h13' : (2 : ℝ) ^ (13 : ℝ) = 8192 := by norm_num
    rw [h13'] at h13
    have : (0 : ℝ) ≤ (2 : ℝ) ^ ((14 : ℕ) * (μ : ℝ) / 75) := by positivity
    nlinarith
  -- `(μ + 65)² ≤ 121 μ²`
  have hμ : (((μ + 65 : ℕ) : ℝ)) ^ 2 ≤ 121 * (μ : ℝ) ^ 2 := by
    have : (7 : ℝ) ≤ μ := by simp_all
    push_cast; nlinarith
  -- the chords
  have hgg : (2 : ℝ) ^ ceilBeta μ ≤ gradeGran μ := by
    have : 2 ^ ceilBeta μ ≤ gradeGran μ := by unfold gradeGran; omega
    exact_mod_cast this
  have hcb : (2 : ℝ) ^ ((μ : ℝ) / 5) ≤ (2 : ℝ) ^ ceilBeta μ := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := le_ceilBeta_real μ; linarith
  have hE15 : E ^ 15 = (2 : ℝ) ^ ((μ : ℝ) / 5) := by
    grind [E_pow]
  have hγ₀ : 2 * E ^ 15 ≤ (γ₀ : ℝ) + 1 := by
    have : (2 * gradeGran μ : ℝ) ≤ γ₀ := by exact_mod_cast hg0
    grind
  have hM2 : 2 * (M : ℝ) + 1 ≤ 121 * E ^ 75 := by
    rw [E_pow_75]
    have : (M : ℝ) ≤ 20 * (2 * 2 ^ μ + 1) := by exact_mod_cast hM
    have : (1 : ℝ) ≤ 2 ^ μ := one_le_pow₀ (by norm_num)
    linarith
  have hxyR : ((x + y + 1 : ℕ) : ℝ) * ((γ₀ : ℝ) + 1) ≤ 36960 * (121 * E ^ 75) + ((γ₀ : ℝ) + 1) := by
    have hx' : (x : ℝ) * ((γ₀ : ℝ) + 1) ≤ 18480 * (2 * (M : ℝ) + 1) := by exact_mod_cast hx
    have hy' : (y : ℝ) * ((γ₀ : ℝ) + 1) ≤ 18480 * (2 * (M : ℝ) + 1) := by exact_mod_cast hy
    grind
  have hxy : ((x + y + 1 : ℕ) : ℝ) ≤ 2236081 * E ^ 60 := by
    have hg0' : (0 : ℝ) < (γ₀ : ℝ) + 1 := by positivity
    have e75 : E ^ 75 = E ^ 15 * E ^ 60 := by grind
    have hE60 : 1 ≤ E ^ 60 := one_le_pow₀ hE1
    have hE60p : 0 ≤ E ^ 60 := by positivity
    have hb : ((x + y + 1 : ℕ) : ℝ) * ((γ₀ : ℝ) + 1) ≤
        (2236081 * E ^ 60) * ((γ₀ : ℝ) + 1) := by
      have a1 : 36960 * (121 * E ^ 75) ≤ 2236080 * E ^ 60 * ((γ₀ : ℝ) + 1) := by
        rw [e75]
        have : 2 * E ^ 15 * E ^ 60 ≤ ((γ₀ : ℝ) + 1) * E ^ 60 :=
          mul_le_mul_of_nonneg_right hγ₀ hE60p
        nlinarith
      have a2 : (γ₀ : ℝ) + 1 ≤ E ^ 60 * ((γ₀ : ℝ) + 1) := by nlinarith
      nlinarith
    exact le_of_mul_le_mul_right hb hg0'
  -- lemma41Nat
  have hN : (μ : ℝ) ^ 2 * E ^ 74 ≤ lemma41Nat μ := by
    unfold lemma41Nat
    have e : E ^ 74 = (2 : ℝ) ^ ((74 : ℝ) / 75 * μ) := by
      grind [E_pow]
    rw [e]
    calc (μ : ℝ) ^ 2 * (2 : ℝ) ^ ((74 : ℝ) / 75 * μ)
        ≤ (μ : ℝ) ^ 2 * ((Nat.clog 2 μ : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * μ) := by
          have : (0 : ℝ) ≤ (μ : ℝ) ^ 2 * (2 : ℝ) ^ ((74 : ℝ) / 75 * μ) := by positivity
          
          nlinarith
      _ ≤ _ := Nat.le_ceil _
  -- assemble
  set K1 : ℝ := (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) with hK1
  
  have hφ' : (phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran (μ + 65)) M : ℝ) ≤
      K1 * (121 * (μ : ℝ) ^ 2) * (8192 * E ^ 14) := by
    calc _ ≤ K1 * (((μ + 65 : ℕ) : ℝ)) ^ 2 * ((2 : ℝ) ^ (((μ + 65 : ℕ) : ℝ) / 75)) ^ 14 := hφ
      _ ≤ K1 * (121 * (μ : ℝ) ^ 2) * (8192 * E ^ 14) := by gcongr
  have hmain : (mcost κM (scF κ) (scG κ) cutGran x y γ M : ℝ) ≤
      (K1 * 121 * 8192 * 2236081) * ((μ : ℝ) ^ 2 * E ^ 74) := by
    have h1R : (mcost κM (scF κ) (scG κ) cutGran x y γ M : ℝ) ≤
        ((x + y + 1 : ℕ) : ℝ) *
          (phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran (μ + 65)) M : ℝ) := by
      exact_mod_cast h1
    have hp0 : (0 : ℝ) ≤ (phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran (μ + 65)) M : ℝ) :=
      Nat.cast_nonneg _
    calc _ ≤ ((x + y + 1 : ℕ) : ℝ) *
          (phiL (fun _ => κM) (scF κ) (scG κ) cutGran (gradeGran (μ + 65)) M : ℝ) := h1R
      _ ≤ (2236081 * E ^ 60) * (K1 * (121 * (μ : ℝ) ^ 2) * (8192 * E ^ 14)) :=
          mul_le_mul hxy hφ' hp0 (by positivity)
      _ = (K1 * 121 * 8192 * 2236081) * ((μ : ℝ) ^ 2 * E ^ 74) := by ring
  have hfin : (mcost κM (scF κ) (scG κ) cutGran x y γ M : ℝ) ≤
      ((mcK κM κ * lemma41Nat μ : ℕ) : ℝ) := by
    have hKK : K1 * 121 * 8192 * 2236081 ≤ (mcK κM κ : ℝ) := by
      unfold mcK; grind
    have h0 : (0 : ℝ) ≤ (μ : ℝ) ^ 2 * E ^ 74 := by positivity
    push_cast
    calc _ ≤ (K1 * 121 * 8192 * 2236081) * ((μ : ℝ) ^ 2 * E ^ 74) := hmain
      _ ≤ (mcK κM κ : ℝ) * (lemma41Nat μ : ℝ) := mul_le_mul hKK hN h0 (Nat.cast_nonneg _)
  exact_mod_cast hfin

end

end DrvG

end Chazelle.Core
