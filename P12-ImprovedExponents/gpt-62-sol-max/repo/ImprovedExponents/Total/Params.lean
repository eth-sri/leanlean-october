module

public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ImprovedExponents.Pipeline.HostBound

@[expose] public section

/-!
# The parameters `D = ⌊n^d⌋`, `g = ⌈D^η⌉` and the dimension `Dc` of a call

For `0 < d ≤ 1` and `0 < η < 1/2`, the parameters `D(n) = ⌊n^d⌋` and `g(n) = ⌈D(n)^η⌉` satisfy,
from some `n` on, the hypotheses of Theorem 17 and the two-sided bounds `n^d/2 ≤ D ≤ n^d`,
`D^η ≤ g ≤ 2 D^η` (`HostParams`, `eventually_hostParams`). If the dimension `Dc(n)` of a call is
`Θ(D^a)` with `d a < min(ε, 1)`, then from some `n` on `1 ≤ Dc ≤ n^ε` and the powers of `Dc` are
bounded by powers of `n` (`theta_rpow`, `callSizes`).

The actual call dimension is `Dc = ⌈⌊√D⌋/g⌉ ⌊√D⌋ = Θ(D^{1-η})`.
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Filter Asymptotics

/-- For `d > 0`, `n^d` is eventually at least any given number. -/
theorem eventually_le_rpow {d : ℝ} (hd0 : 0 < d) (B : ℝ) :
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
theorem eventually_hostParams {d η : ℝ} {D g : ℕ → ℕ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊) :
    ∀ᶠ n : ℕ in atTop, HostParams d η n (D n) (g n) := by
  have hτ : 0 < 1 / 2 - η := by linarith
  filter_upwards [eventually_le_rpow hd0 (max 16 (2 * (2 : ℝ) ^ (1 / (1 / 2 - η)))),
    eventually_ge_atTop 1] with n hn hn1
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h16 : (16 : ℝ) ≤ (n : ℝ) ^ d := (le_max_left _ _).trans hn
  have hB : 2 * (2 : ℝ) ^ (1 / (1 / 2 - η)) ≤ (n : ℝ) ^ d := (le_max_right _ _).trans hn
  have hfl : (D n : ℝ) ≤ (n : ℝ) ^ d := by rw [hD]; exact Nat.floor_le (by positivity)
  have hlt : (n : ℝ) ^ d < (D n : ℝ) + 1 := by rw [hD]; exact Nat.lt_floor_add_one _
  have hD16 : 16 ≤ D n := by rw [hD]; exact Nat.le_floor (by exact_mod_cast h16)
  have hX16 : (16 : ℝ) ≤ D n := by exact_mod_cast hD16
  have hX0 : (0 : ℝ) < D n := by linarith
  have hXη1 : 1 ≤ (D n : ℝ) ^ η := Real.one_le_rpow (by linarith) hη0.le
  have hgl : (D n : ℝ) ^ η ≤ g n := by rw [hg]; exact Nat.le_ceil _
  have hgu : (g n : ℝ) < (D n : ℝ) ^ η + 1 := by
    rw [hg]; exact Nat.ceil_lt_add_one (by positivity)
  have hhalf : (2 : ℝ) ^ (1 / (1 / 2 - η)) ≤ (D n : ℝ) := by linarith
  have h2 : (2 : ℝ) ≤ (D n : ℝ) ^ (1 / 2 - η) :=
    (Real.rpow_inv_le_iff_of_pos (by norm_num) (by positivity) hτ).1 (by simpa [one_div] using hhalf)
  have hsqrt : Real.sqrt (D n) = (D n : ℝ) ^ η * (D n : ℝ) ^ (1 / 2 - η) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    simp
  refine ⟨hn1, hD16, ?_, ?_, ?_, hfl, by linarith, hgl, by linarith⟩
  · have : (D n : ℝ) ≤ (n : ℝ) :=
      hfl.trans ((Real.rpow_le_rpow_of_exponent_le hN1 hd1).trans_eq (Real.rpow_one _))
    exact_mod_cast this
  · have : (1 : ℝ) ≤ g n := hXη1.trans hgl
    exact_mod_cast this
  nlinarith

/-- Two-sided bounds of nonnegative functions give asymptotic equivalence up to constants. -/
theorem theta_of_bounds {f g : ℕ → ℝ} {l u : ℝ} (hl : 0 < l)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (h : ∀ᶠ n in atTop, l * g n ≤ f n ∧ f n ≤ u * g n) : f =Θ[atTop] g := by
  refine ⟨.of_bound u ?_, .of_bound l⁻¹ ?_⟩
  · filter_upwards [h] with n hn
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_nonneg (hg n)] using hn.2
  · filter_upwards [h] with n hn
    simp [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_nonneg (hg n), inv_mul_eq_div]
    exact (le_div_iff₀ hl).2 (by simpa [mul_comm] using hn.1)

/-- Both positive and negative powers preserve two-sided asymptotic bounds. -/
theorem theta_rpow {f : ℕ → ℝ} {a : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : f =Θ[atTop] fun n : ℕ => (n : ℝ) ^ a) (r : ℝ) :
    (fun n => f n ^ r) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ (a * r) :=
  (h.rpow (.of_forall hf) (.of_forall fun n => Real.rpow_nonneg n.cast_nonneg a)).trans_eventuallyEq
    (.of_forall fun n => (Real.rpow_mul n.cast_nonneg _ _).symm)

variable {d η : ℝ} {D g : ℕ → ℕ}

/-- The floor of `n^d` has order `n^d`. -/
theorem hostThetaD (h : ∀ᶠ n in atTop, HostParams d η n (D n) (g n)) :
    (fun n => (D n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ d :=
  theta_of_bounds (l := 1 / 2) (u := 1) (by norm_num) (by intro; positivity)
    (by intro; positivity) (h.mono fun _ p => by simpa [div_eq_mul_inv, mul_comm] using ⟨p.le_D, p.D_le⟩)

/-- The rounded group count has order `D^η`. -/
theorem hostThetaG (h : ∀ᶠ n in atTop, HostParams d η n (D n) (g n)) :
    (fun n => (g n : ℝ)) =Θ[atTop] fun n : ℕ => (D n : ℝ) ^ η :=
  theta_of_bounds (l := 1) (u := 2) zero_lt_one (by intro; positivity)
    (by intro; positivity) (h.mono fun _ p => by simpa using ⟨p.rpow_le_g, p.g_le_rpow⟩)

/-- A dimension of order `n^s` is eventually positive and below any larger power. -/
theorem callSizes {Dc : ℕ → ℕ} {s ε : ℝ}
    (h : (fun n => (Dc n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ s)
    (hε : s < ε) (h1 : s < 1) :
    ∀ᶠ n in atTop, 1 ≤ Dc n ∧ (Dc n : ℝ) ≤ (n : ℝ) ^ ε ∧ (Dc n : ℝ) ≤ n := by
  filter_upwards [h.eq_zero_iff, IsBigOPow.eventually_abs_le h.1 hε,
    IsBigOPow.eventually_abs_le h.1 h1, eventually_gt_atTop 0] with n h0 ha hb hn
  exact ⟨Nat.one_le_iff_ne_zero.2 (by simpa using h0.not.mpr (by positivity)),
    (le_abs_self _).trans ha, (le_abs_self _).trans (by simpa using hb)⟩

/-! ## The two dimensions of a call -/

/-- `D^{1-η}/8 ≤ ⌈⌊√D⌋/g⌉ ⌊√D⌋ ≤ 2 D^{1-η}` for parameters as in `HostParams`. -/
theorem HostParams.pieceSize_bounds {d η : ℝ} {n Dn gn : ℕ} (P : HostParams d η n Dn gn) :
    1 / 8 * (Dn : ℝ) ^ (1 - η) ≤ ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ∧
      ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ≤ 2 * (Dn : ℝ) ^ (1 - η) := by
  let S := Nat.sqrt Dn
  let Q := pieceSizeNat Dn gn * S
  have hg : gn ≤ S := by
    change gn ≤ Nat.sqrt Dn
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.le_floor P.g_le_sqrt
  have hs : 1 ≤ S := P.one_le_g.trans hg
  have hlo : Dn ≤ 4 * (Q * gn) := by
    have hd := Nat.lt_succ_sqrt Dn
    have hmul := Nat.mul_le_mul (show S + 1 ≤ 2 * S by omega) (show S + 1 ≤ 2 * S by omega)
    have hcov := Nat.mul_le_mul_right S ((Nat.ceilDiv_le_iff P.one_le_g).mp (le_refl (S ⌈/⌉ gn)))
    change S * S ≤ pieceSizeNat Dn gn * gn * S at hcov
    dsimp [Q]
    nlinarith [show Dn < (S + 1) * (S + 1) from hd]
  have hhi : Q * gn ≤ 2 * Dn := by
    have h := (Nat.ceilDiv_mul_lt (a := S) P.one_le_g).le.trans (show S + gn ≤ 2 * S by omega)
    have hh := Nat.mul_le_mul_right S h
    change pieceSizeNat Dn gn * gn * S ≤ 2 * S * S at hh
    dsimp [Q]
    nlinarith [Nat.sqrt_le Dn]
  change 1 / 8 * (Dn : ℝ) ^ (1 - η) ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * (Dn : ℝ) ^ (1 - η)
  have hD : (0 : ℝ) < Dn := by exact_mod_cast (by norm_num : 0 < 16).trans_le P.sixteen_le
  have hη : (0 : ℝ) < (Dn : ℝ) ^ η := by positivity
  simp only [Real.rpow_sub hD, Real.rpow_one, ← mul_div_assoc]
  rw [div_le_iff₀ hη, le_div_iff₀ hη]
  constructor
  · have hL : (Dn : ℝ) ≤ 4 * ((Q : ℝ) * gn) := by exact_mod_cast hlo
    nlinarith [mul_le_mul_of_nonneg_left P.g_le_rpow (Nat.cast_nonneg Q)]
  · exact (mul_le_mul_of_nonneg_left P.rpow_le_g (Nat.cast_nonneg Q)).trans (by exact_mod_cast hhi)

end ImprovedExponents
