module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected physical-budget proofs released under MIT-0; see
../../../../../third_party/twelfth/LICENSE-MIT-0.
Source pin: 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Manifest: ../../../../../third_party/twelfth/PHYSICAL_PACKET_ASSEMBLY_MANIFEST.json.
The new assembly uses the literal native prefix/Gram bound and keeps the
actual stationary-zeta source-to-prefix inequality as an explicit premise.
Mathlib dependencies retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonLocalizedGram
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Harmonic.Bounds
public import WeylPort.GrowthAlgebra

@[expose] public section
open Complex Filter MeasureTheory Set Topology Finset
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem atkinsonSourceCutoff_le_natural {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L) :
    (atkinsonSourceCutoff T G L : ℝ) ≤ 37*T*L^2/G^2 := by
  have hT0 : 0 < T := by linarith
  have hG2 : 0 < G^2 := sq_pos_of_pos hG
  have hGT : G^2 ≤ T := by nlinarith [Real.sq_sqrt hT0.le]
  have hL2 : 1 ≤ L^2 := by nlinarith
  have hU : 1 ≤ T*L^2/G^2 := (le_div_iff₀ hG2).2 (by nlinarith)
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 36*T*(L/G)^2)
  change (atkinsonSourceCutoff T G L : ℝ) < 36*T*(L/G)^2+1 at hceil
  have he : 36*T*(L/G)^2 = 36*(T*L^2/G^2) := by ring
  rw [he] at hceil
  have he' : 37*T*L^2/G^2 = 37*(T*L^2/G^2) := by ring
  rw [he']
  linarith

theorem atkinson_clog_le_height_log {H : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H) :
    (Nat.clog 2 N:ℝ) ≤ (1/Real.log 2+1)*Real.log (2*H) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hN0 : N = 0
  · subst N
    simp only [Nat.clog_zero_right, Nat.cast_zero]
    positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  have hceil := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hN1)
  have he := Real.natCeil_logb_natCast 2 N
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hceil
  have hl : Real.log (N:ℝ) ≤ Real.log (2*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hd := div_le_div_of_nonneg_right hl h2.le
  unfold Real.logb at hceil
  calc
    _ ≤ Real.log (2*H)/Real.log 2+Real.log (2*H) := by linarith
    _ = _ := by ring


theorem eventually_atkinson_height_log_pow_le_rpow (k : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ H : ℝ in atTop, (Real.log (2*H))^k ≤ H^ν := by
  filter_upwards [eventually_const_log_pow_le_rpow ((2:ℝ)^k) (by positivity) k hν,
    eventually_ge_atTop (2:ℝ)] with H hsmall hH
  have hH0 : 0 < H := by linarith
  have hlog2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hH
  have hlog : Real.log (2*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hp := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 2*H)) hlog k
  rw [mul_pow] at hp
  exact hp.trans hsmall



theorem atkinsonPhysicalCutoff_le_natural {H G : ℝ}
    (hH : 1 ≤ H) (hG : 0 < G) (hupper : G ≤ Real.sqrt (2*H))
    (hlog : 1 ≤ Real.log (2*H)) :
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) ≤
      74*H*(Real.log (2*H))^2/G^2 := by
  exact (atkinsonSourceCutoff_le_natural (by linarith : 1 ≤ 2*H) hG hupper hlog).trans_eq
    (by ring)

theorem atkinsonPhysical_cutoff_scale_identity {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) (q : ℝ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^(q-1/2)*ℓ^(2*q)*G^(2-2*q) := by
  have hbase : (74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^q*ℓ^(2*q)/G^(2*q) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity : 0 ≤ 74*H) (sq_nonneg ℓ),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 74) hH.le,
      ← Real.rpow_natCast,← Real.rpow_mul hℓ.le,
      ← Real.rpow_natCast,← Real.rpow_mul hG.le]
    norm_num
  rw [hbase,Real.rpow_sub hH,Real.rpow_sub hG,Real.rpow_neg hH.le,Real.rpow_two]
  ring

theorem atkinsonPhysical_diagonal_scale {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/2:ℝ) ≤
      5476*(H/G)*ℓ^3 := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  norm_num only [show (3/2:ℝ)-1/2 = 1 by norm_num,
    show 2*(3/2:ℝ) = 3 by norm_num,show 2-2*(3/2:ℝ) = -1 by norm_num,
    Real.rpow_one,Real.rpow_neg_one,Real.rpow_ofNat]
  have hc : (74:ℝ)^(3/2:ℝ) ≤ 5476 := by
    calc
      _ ≤ (74:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    _ ≤ 5476*H*ℓ^3*G⁻¹ := by gcongr
    _ = _ := by ring

theorem atkinsonPhysical_near_scale {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    (Real.sqrt H/G)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(1:ℝ)) =
      74*(H/G)*ℓ^2 := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  norm_num only [show (1:ℝ)-1/2 = 1/2 by norm_num,
    show 2*(1:ℝ) = 2 by norm_num,show 2-2*(1:ℝ) = 0 by norm_num,
    Real.rpow_one,Real.rpow_zero,Real.rpow_two,mul_one]
  rw [← Real.sqrt_eq_rpow]
  calc
    _ = 74*(Real.sqrt H)^2/G*ℓ^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hH.le]; ring











