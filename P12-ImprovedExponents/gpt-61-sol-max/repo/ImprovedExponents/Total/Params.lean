module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

/-!
# The parameters `D = ⌊n^d⌋`, `g = ⌈D^η⌉` and the dimension `Dc` of a call

For `0 < d ≤ 1` and `0 < η < 1/2`, the parameters `D(n) = ⌊n^d⌋` and `g(n) = ⌈D(n)^η⌉` satisfy,
from some `n` on, the hypotheses of Theorem 17 and the two-sided bounds `n^d/2 ≤ D ≤ n^d`,
`D^η ≤ g ≤ 2 D^η` (`HostParams`, `eventually_hostParams`). If the dimension `Dc(n)` of a call is
`Θ(D^a)` with `d a < min(ε, 1)`, then from some `n` on `1 ≤ Dc ≤ n^ε` and the powers of `Dc` are
bounded by powers of `n` (`CallParams`, `eventually_callParams`).

The two dimensions that are used: `Dc = D` (`eventually_self_bounds`) and
`Dc = ⌈⌊√D⌋/g⌉ ⌊√D⌋ = Θ(D^{1-η})` (`eventually_pieceSize_bounds`).
-/

namespace ImprovedExponents

open ThreeSumApsp.Spec Filter

/-- For `d > 0`, `n^d` is eventually at least any given number. -/
theorem eventually_le_rpow {d : ℝ} (hd0 : 0 < d) B :
    ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) ^ d :=
  ((tendsto_rpow_atTop hd0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- What is used of the parameters `D = ⌊n^d⌋` and `g = ⌈D^η⌉` at a large `n`: the hypotheses of
Theorem 17 and two-sided bounds. -/
structure HostParams (d η : ℝ) (n Dn gn : ℕ) : Prop where
  /-- `n ≥ 1`. -/
  one_le_n : 1 ≤ n
  /-- `D ≥ 16`. -/
  sixteen_le : 16 ≤ Dn
  /-- `D ≤ n`. -/
  le_n : Dn ≤ n
  /-- `g ≥ 1`. -/
  one_le_g : 1 ≤ gn
  /-- `g ≤ √D`. -/
  g_le_sqrt : (gn : ℝ) ≤ Real.sqrt Dn
  /-- `D ≤ n^d`. -/
  D_le : (Dn : ℝ) ≤ (n : ℝ) ^ d
  /-- `n^d/2 ≤ D`. -/
  le_D : (n : ℝ) ^ d / 2 ≤ Dn
  /-- `D^η ≤ g`. -/
  rpow_le_g : (Dn : ℝ) ^ η ≤ gn
  /-- `g ≤ 2 D^η`. -/
  g_le_rpow : (gn : ℝ) ≤ 2 * (Dn : ℝ) ^ η

/-- `D = ⌊n^d⌋` and `g = ⌈D^η⌉` satisfy `HostParams` from some `n` on. -/
theorem eventually_hostParams {d η} {D g : ℕ → ℕ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊) :
    ∀ᶠ n : ℕ in atTop, HostParams d η n (D n) (g n) := by
  have hτ : 0 < 1 / 2 - η := by linarith
  filter_upwards [eventually_le_rpow hd0 (max 16 (2 * (2 : ℝ) ^ (1 / (1 / 2 - η)))),
    eventually_ge_atTop 1] with n hn hn1

  have  := (le_max_left _ _).trans hn
  have  := (le_max_right _ _).trans hn
  have hfl : (D n : ℝ) ≤ (n : ℝ) ^ d := by rw [hD]; exact Nat.floor_le (by positivity)
  have  : (n : ℝ) ^ d < (D n : ℝ) + 1 := by rw [hD]; exact Nat.lt_floor_add_one _
  have hD16 : 16 ≤ D n := by aesop (add safe apply [Nat.le_floor])
  have   := mod_cast hD16

  have  : 1 ≤ (D n : ℝ) ^ η := Real.one_le_rpow (by linarith) hη0.le

  have  : (g n : ℝ) < (D n : ℝ) ^ η + 1 := by
    grind [Nat.ceil_lt_add_one]

  have  := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / (1 / 2 - η))) ^ (1 / 2 - η) := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
      _ ≤ (D n : ℝ) ^ (1 / 2 - η) := Real.rpow_le_rpow (by positivity) (by linarith) hτ.le
  have  : Real.sqrt (D n) = (D n : ℝ) ^ η * (D n : ℝ) ^ (1 / 2 - η) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
    congr 1
    ring
  refine ⟨hn1, hD16, ?_, ?_, ?_, hfl, by linarith, by rw [hg]; exact Nat.le_ceil _, by linarith⟩
  · have :=
      hfl.trans ((Real.rpow_le_rpow_of_exponent_le (mod_cast hn1) hd1).trans_eq (Real.rpow_one _))
    exact_mod_cast this
  · ram_safe
  · ram_safe

namespace HostParams

variable {d η : ℝ} {n Dn gn : ℕ}

variable (h : HostParams d η n Dn gn)

include h in
/-- `g ≤ 2 n^{dη}`. -/
theorem g_le (hη0 : 0 ≤ η) :
    (gn : ℝ) ≤ 2 * (n : ℝ) ^ (d * η) := by
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) h.D_le hη0
  rw [← Real.rpow_mul (Nat.cast_nonneg _)] at h1
  linarith [h.g_le_rpow]

variable (hη0 : 0 ≤ η) (hη1 : η ≤ 1)

include h hη0 hη1 in
/-- `n^{dη}/2 ≤ g`. -/
theorem le_g  :
    (n : ℝ) ^ (d * η) / 2 ≤ gn := by

  have h1 := Real.rpow_le_rpow (by positivity) h.le_D hη0
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul (Nat.cast_nonneg _)] at h1
  have h2 : (2 : ℝ) ^ η ≤ 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1).trans_eq (Real.rpow_one _)
  have  : (n : ℝ) ^ (d * η) / 2 ≤ (n : ℝ) ^ (d * η) / (2 : ℝ) ^ η :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  linarith [h.rpow_le_g]

include h hη0 hη1 in
/-- `1/g ≤ 2 n^{-dη}`. -/
theorem inv_g_le  :
    1 / (gn : ℝ) ≤ 2 * (n : ℝ) ^ (-(d * η)) := by

  have hN0 : (0 : ℝ) < n := mod_cast h.one_le_n

  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_div_iff₀ (mod_cast h.one_le_g) (by positivity)]
  linarith [h.le_g hη0 hη1]

include h in
/-- `1/√D ≤ 2 n^{-d/2}`. -/
theorem inv_sqrt_le :
    1 / Real.sqrt Dn ≤ 2 * (n : ℝ) ^ (-(d / 2)) := by
  have hN0 : (0 : ℝ) < n := mod_cast h.one_le_n


  have  : (n : ℝ) ^ (d / 2) ≤ 2 * Real.sqrt Dn := by

    rw [(by
      grind [Real.sqrt_eq_rpow, Real.rpow_mul]
     : (n : ℝ) ^ (d / 2) = Real.sqrt (n ^ d)), Real.sqrt_le_iff]
    ram_safe
  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_div_iff₀ (Real.sqrt_pos.2 (by ram_arith : (0 : ℝ) < Dn)) (by positivity)]
  linarith

end HostParams

/-- What is used of the dimension `Dc` of a call at a large `n`: it is at least 1 and at most
`n^ε` and `n`, and its powers `Dc^{-γ}` and `Dc^q` are at most constants times powers of `n`. -/
structure CallParams (d a ε γ q K₁ K₂ : ℝ) (n Dcn : ℕ) : Prop where
  /-- `Dc ≥ 1`. -/
  one_le : 1 ≤ Dcn
  /-- `Dc ≤ n^ε`. -/
  le_rpow : (Dcn : ℝ) ≤ (n : ℝ) ^ ε
  /-- `Dc ≤ n`. -/
  le_n : (Dcn : ℝ) ≤ n
  /-- `Dc^{-γ} ≤ K₁ n^{-daγ}`. -/
  neg_rpow_le : (Dcn : ℝ) ^ (-γ) ≤ K₁ * (n : ℝ) ^ (d * a * -γ)
  /-- `Dc^q ≤ K₂ n^{daq}`. -/
  rpow_le : (Dcn : ℝ) ^ q ≤ K₂ * (n : ℝ) ^ (d * a * q)

/-- If `Dc = Θ(D^a)` with `d a < min(ε, 1)`, then `CallParams` holds from some `n` on, with
constants that depend only on the constants of `Θ` and on `a`, `γ`, `q`. -/
theorem eventually_callParams {d η a ε γ q c₁ c₂} {D g Dc : ℕ → ℕ} (ha0 : 0 < a)
    (hda1 : d * a < 1) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hthin : d * a < ε) (hc₁ : 0 < c₁)
    (hP : ∀ᶠ n : ℕ in atTop, HostParams d η n (D n) (g n))
    (hDc : ∀ᶠ n : ℕ in atTop,
      c₁ * (D n : ℝ) ^ a ≤ (Dc n : ℝ) ∧ (Dc n : ℝ) ≤ c₂ * (D n : ℝ) ^ a) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ᶠ n : ℕ in atTop, CallParams d a ε γ q K₁ K₂ n (Dc n) := by

  have  : 0 < c₁ / (2 : ℝ) ^ a := by positivity
  refine ⟨(c₁ / (2 : ℝ) ^ a) ^ (-γ), max c₂ 1 ^ q, by positivity, by positivity, ?_⟩
  filter_upwards [hP, hDc, eventually_le_rpow (sub_pos.2 (lt_min hthin hda1)) (max c₂ 1)] with n P hY hn
  obtain ⟨hYl, hYu⟩ := hY
  have hN1 : (1 : ℝ) ≤ n := mod_cast P.one_le_n
  have hN0 : (0 : ℝ) < n := by linarith

  have hXa : (D n : ℝ) ^ a ≤ (n : ℝ) ^ (d * a) := by
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) P.D_le ha0.le

  have hXa0 : 0 ≤ (D n : ℝ) ^ a := by positivity
  have hlow := by
    calc c₁ / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a) = c₁ * ((n : ℝ) ^ (d * a) / (2 : ℝ) ^ a) := by ring
      _ ≤ c₁ * (D n : ℝ) ^ a := mul_le_mul_of_nonneg_left (by
        rw [Real.rpow_mul hN0.le, ← Real.div_rpow (by positivity) (by norm_num)]
        exact Real.rpow_le_rpow (by positivity) P.le_D ha0.le
      ) hc₁.le
      _ ≤ Dc n := hYl
  have hup : (Dc n : ℝ) ≤ max c₂ 1 * (n : ℝ) ^ (d * a) :=
    hYu.trans (mul_le_mul (le_max_left _ _) hXa hXa0 (by positivity))
  have hup' := by
    calc max c₂ 1 * (n : ℝ) ^ (d * a) ≤ (n : ℝ) ^ (min ε 1 - d * a) * (n : ℝ) ^ (d * a) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (n : ℝ) ^ min ε 1 := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
  have hlow0 : 0 < c₁ / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a) := by positivity
  have hY0 := hlow0.trans_le hlow
  refine ⟨Nat.succ_le_of_lt (mod_cast hY0), ?_, ?_, ?_, ?_⟩
  · exact (hup.trans hup').trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  · exact (hup.trans hup').trans
      ((Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)).trans_eq (Real.rpow_one _))
  · calc (Dc n : ℝ) ^ (-γ) ≤ (c₁ / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a)) ^ (-γ) :=
          Real.rpow_le_rpow_of_nonpos hlow0 hlow (by linarith)
      _ = (c₁ / (2 : ℝ) ^ a) ^ (-γ) * (n : ℝ) ^ (d * a * -γ) := by
          grind [Real.mul_rpow, Real.rpow_mul]
  · calc (Dc n : ℝ) ^ q ≤ (max c₂ 1 * (n : ℝ) ^ (d * a)) ^ q := Real.rpow_le_rpow hY0.le hup hq
      _ = max c₂ 1 ^ q * (n : ℝ) ^ (d * a * q) := by
          grind [Real.mul_rpow, Real.rpow_mul]

/-! ## The two dimensions of a call -/

/-- `D^{1-η}/8 ≤ ⌈⌊√D⌋/g⌉ ⌊√D⌋ ≤ 2 D^{1-η}` for parameters as in `HostParams`. -/
theorem HostParams.pieceSize_bounds {d η} {n Dn gn} (P : HostParams d η n Dn gn) :
    1 / 8 * Dn ^ (1 - η) ≤ ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ∧
      (pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) ≤ 2 * (Dn : ℝ) ^ (1 - η) := by
  have hX0 : (0 : ℝ) < Dn := by ram_arith
  have hg0 : (0 : ℝ) < gn := mod_cast P.one_le_g

  have hS1 : (Nat.sqrt Dn : ℝ) ≤ Real.sqrt Dn := Real.nat_sqrt_le_real_sqrt
  have  : Real.sqrt Dn < (Nat.sqrt Dn : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hgS : (gn : ℝ) ≤ Nat.sqrt Dn := by
    have : gn ≤ Nat.sqrt Dn := by
      rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
      exact Nat.le_floor P.g_le_sqrt
    exact_mod_cast this
  have hS0 : (0 : ℝ) ≤ Nat.sqrt Dn := Nat.cast_nonneg _
  have hpiece : pieceSizeNat Dn gn = ⌈Nat.sqrt Dn / (gn : ℝ)⌉₊ :=
    (Nat.ceil_div_eq_ceilDiv _ P.one_le_g).symm

  have  : (pieceSizeNat Dn gn : ℝ) < (Nat.sqrt Dn : ℝ) / gn + 1 := by
    rw [hpiece]; exact Nat.ceil_lt_add_one (by positivity)
  have  := (one_le_div hg0).2 hgS
  have hSS :=
    (mul_le_mul hS1 hS1 hS0 (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hX0.le)


  rw [(by
    rw [Real.rpow_sub hX0, Real.rpow_one]
   : (Dn : ℝ) ^ (1 - η) = (Dn : ℝ) / (Dn : ℝ) ^ η), Nat.cast_mul]
  constructor
  · calc 1 / 8 * ((Dn : ℝ) / (Dn : ℝ) ^ η) = (Dn : ℝ) / 4 / (2 * (Dn : ℝ) ^ η) := by ring
      _ ≤ (Nat.sqrt Dn : ℝ) * Nat.sqrt Dn / gn :=
          div_le_div₀ (mul_nonneg hS0 hS0) (by
            have  : (1 : ℝ) ≤ gn := mod_cast P.one_le_g

            have  := Real.mul_self_sqrt hX0.le
            nlinarith
          ) hg0 P.g_le_rpow
      _ = (Nat.sqrt Dn : ℝ) / gn * Nat.sqrt Dn := by ring
      _ ≤ (pieceSizeNat Dn gn : ℝ) * Nat.sqrt Dn := mul_le_mul_of_nonneg_right (by
        rw [hpiece]; exact Nat.le_ceil _
      ) hS0
  · calc (pieceSizeNat Dn gn : ℝ) * Nat.sqrt Dn
        ≤ 2 * ((Nat.sqrt Dn : ℝ) / gn) * Nat.sqrt Dn :=
          mul_le_mul_of_nonneg_right (by linarith) hS0
      _ = 2 * ((Nat.sqrt Dn : ℝ) * Nat.sqrt Dn / gn) := by ring
      _ ≤ 2 * ((Dn : ℝ) / (Dn : ℝ) ^ η) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ hX0.le hSS (by positivity) P.rpow_le_g) (by norm_num)

/-- The dimension `Dc = ⌈⌊√D⌋/g⌉ ⌊√D⌋` of the middle part is `Θ(D^{1-η})`. -/
def eventually_pieceSize_bounds {d η} {D g : ℕ → ℕ}
    (hP : ∀ᶠ n : ℕ in atTop, HostParams d η n (D n) (g n)) :=
  hP.mono fun _ P => P.pieceSize_bounds

/-- The hypothesis on the dimension of a call, for the dimension `⌈⌊√D⌋/g⌉ ⌊√D⌋` of the middle
part and `a = 1 - η`, where `D = ⌊n^d⌋` and `g = ⌈D^η⌉`; the constants are `1/8` and `2`. -/
theorem exists_bounds_pieceSize {d η : ℝ} {D g : ℕ → ℕ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hη0 : 0 < η) (hη1 : η < 1 / 2) (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊)
    (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * D n ^ (1 - η) ≤ (pieceSizeNat (D n) (g n) * Nat.sqrt (D n) : ℕ) ∧
        (pieceSizeNat (D n) (g n) * Nat.sqrt (D n) : ℕ) ≤ c₂ * D n ^ (1 - η) :=
  ⟨1 / 8, 2, by norm_num,
    eventually_pieceSize_bounds (eventually_hostParams hd0 hd1 hη0 hη1 hD hg)⟩

end ImprovedExponents
