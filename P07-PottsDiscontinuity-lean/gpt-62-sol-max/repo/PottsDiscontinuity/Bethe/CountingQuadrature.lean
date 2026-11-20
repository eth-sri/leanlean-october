module

public import PottsDiscontinuity.Bethe.Theorem23Comparison
public import PottsDiscontinuity.Bethe.AsymptoticPartition

/-! The Bethe counting function makes consecutive root gaps cells of equal mass.
The trapezoid rule in that mass coordinate leaves only the endpoint deficit to first order. -/

@[expose] public section

open Set MeasureTheory Finset

namespace PottsDiscontinuity.Bethe

local notation "J" => Icc (-Real.pi) Real.pi

theorem abs_sub_le_of_hasDerivAt {a b E : ℝ} {g G : ℝ → ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (G x) x) (hG : ∀ x ∈ Icc a b, |G x| ≤ E)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |g x - g y| ≤ E * |x - y| := by
  simpa only [Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) (fun t ht => by simpa [Real.norm_eq_abs] using hG t ht) hy hx

private theorem rescale_cell_error {N w z v E : ℝ} (hN : 0 < N)
    (h : |v - z * (w / N)| ≤ E * (w / N)) : |N * v - z * w| ≤ E * w := by
  have h' := mul_le_mul_of_nonneg_left h hN.le
  rwa [← abs_of_pos hN, ← abs_mul, abs_of_pos hN, mul_sub, ← mul_assoc N z, mul_comm N z,
    mul_assoc z N, mul_div_cancel₀ w hN.ne', mul_left_comm N E, mul_div_cancel₀ w hN.ne'] at h'

theorem abs_weighted_intervalIntegral_le {a b C : ℝ} {f D : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ D x) (hbound : ∀ x ∈ Icc a b, |f x| ≤ C) :
    |∫ x in a..b, f x * D x| ≤ C * ∫ x in a..b, D x := by
  rw [← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans
    (intervalIntegral.integral_mono_on hab ((hf.mul hD).abs.intervalIntegrable_of_Icc hab)
      ((hD.const_mul C).intervalIntegrable_of_Icc hab) fun x hx => ?_)
  rw [abs_mul, abs_of_nonneg (hpos x hx)]
  exact mul_le_mul_of_nonneg_right (hbound x hx) (hpos x hx)

private theorem interval_weighted_error {a b E : ℝ} {F D u v V : ℝ → ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (D x) x)
    (hV : ∀ x ∈ Icc a b, HasDerivAt V (v x * D x) x)
    (hD : ContinuousOn D (Icc a b)) (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 ≤ D x) (herr : ∀ x ∈ Icc a b, |u x - v x| ≤ E) :
    |(∫ x in a..b, u x * D x) - (V b - V a)| ≤ E * (F b - F a) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hV x (uIcc_of_le hab ▸ hx)) ((hv.mul hD).intervalIntegrable_of_Icc hab)
  have hm := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hF x (uIcc_of_le hab ▸ hx)) (hD.intervalIntegrable_of_Icc hab)
  rw [← hi, ← hm, ← intervalIntegral.integral_sub (f := fun x => u x * D x) (g := fun x => v x * D x) ((hu.mul hD).intervalIntegrable_of_Icc hab)
    ((hv.mul hD).intervalIntegrable_of_Icc hab)]
  simpa only [Pi.sub_apply, sub_mul] using abs_weighted_intervalIntegral_le hab (hu.sub hv) hD hpos herr

private theorem interval_trapezoid {a b c E : ℝ} {F D g G : ℝ → ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (D x) x) (hD : ContinuousOn D (Icc a b))
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (G x) x)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ D x)
    (herr : ∀ x ∈ Icc a b, |G x - c * D x| ≤ E) :
    |(∫ x in a..b, g x * D x) - (g a + g b) / 2 * (F b - F a)| ≤
      E * (b - a) * (F b - F a) := by
  let L (x : ℝ) := g x - c * F x
  let mid := (L a + L b) / 2
  let V (x : ℝ) := c / 2 * F x ^ 2 + mid * F x
  have hL (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt L (G x - c * D x) x :=
    (hg x hx).sub ((hF x hx).const_mul c)
  have hV (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt V ((c * F x + mid) * D x) x := by
    convert (((hF x hx).pow 2).const_mul (c / 2)).add ((hF x hx).const_mul mid) using 1 <;> ring
  have hcf : ContinuousOn F (Icc a b) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hcg : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have heq : V b - V a = (g a + g b) / 2 * (F b - F a) := by dsimp [V, mid, L]; ring
  rw [← heq]
  refine interval_weighted_error hab hF hV hD hcg ((hcf.const_mul c).add continuousOn_const) hpos fun x hx => ?_
  have ha := abs_sub_le_of_hasDerivAt hL herr hx ⟨le_rfl, hab⟩
  have hb := abs_sub_le_of_hasDerivAt hL herr hx ⟨hab, le_rfl⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at ha
  rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at hb
  change |g x - (c * F x + mid)| ≤ _
  rw [show g x - (c * F x + mid) = ((L x - L a) + (L x - L b)) / 2 by dsimp [L, mid]; ring,
    abs_div, abs_two]
  have h := abs_add_le (L x - L a) (L x - L b)
  linarith [mul_nonneg ((abs_nonneg _).trans (herr x hx)) (sub_nonneg.mpr hab)]

/-- A lower bound on the counting derivative controls lengths in the counting coordinate. -/
theorem counting_length_le {F D : ℝ → ℝ} {m u v : ℝ} (hm : 0 < m)
    (hF : ∀ x, HasDerivAt F (D x) x) (hpos : ∀ x ∈ J, m ≤ D x)
    (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v) : v - u ≤ (F v - F u) / m := by
  have hd : Differentiable ℝ F := fun x => (hF x).differentiableAt
  rw [le_div_iff₀ hm, mul_comm]
  exact (convex_Icc _ _).mul_sub_le_image_sub_of_le_deriv hd.continuous.continuousOn hd.differentiableOn
    (fun x hx => (hF x).deriv.symm ▸ hpos x (interior_subset hx)) u hu v hv huv

theorem betheCountingFunction_neg {Δ : ℝ} {N n : ℕ} {p : Fin n → ℝ} (hp : p ∈ S_n n) (x : ℝ) :
    betheCountingFunction Δ N n p (-x) = -betheCountingFunction Δ N n p x := by
  unfold betheCountingFunction
  rw [← Equiv.sum_comp Fin.revPerm (fun j => theta Δ (-x) (p j))]
  simp_rw [show ∀ j, p (Fin.revPerm j) = -p j from hp.2.2, theta_neg_neg, sum_neg_distrib]
  ring

theorem betheCountingFunction_pi {Δ : ℝ} {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hN : 0 < N) :
    betheCountingFunction Δ N n p Real.pi = ((N : ℝ) - n) / (2 * N) := by
  have h := betheCountingFunction_period (Δ := Δ) hN p (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, betheCountingFunction_neg hp] at h
  rw [mul_comm 2 (N : ℝ), div_mul_eq_div_div]
  linarith

theorem betheCountingFunction_zero {Δ : ℝ} {N n : ℕ} {p : Fin n → ℝ} (hp : p ∈ S_n n) :
    betheCountingFunction Δ N n p 0 = 0 := by
  have h := betheCountingFunction_neg (Δ := Δ) (N := N) hp 0
  rw [neg_zero] at h
  linarith

private theorem trapezoid_sum {k : ℕ} (g : Fin (k + 1) → ℝ) :
    (∑ j : Fin k, (g j.castSucc + g j.succ) / 2) + (g 0 + g (Fin.last k)) / 2 = ∑ j, g j := by
  rw [← sum_div, sum_add_distrib]
  have h₁ := Fin.sum_univ_succ g
  have h₂ := Fin.sum_univ_castSucc g
  linarith

/-- Deficit-corrected quadrature for a symmetric root tuple. The assumptions on the test
function and the counting derivative are uniform bounds on the physical interval. -/
theorem bethe_counting_quadrature {Δ : ℝ} (hΔ : Δ < -1) {N n r : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hcount : N = 2 * (n + r))
    (hBE : DiscreteBetheEquation Δ N n p) {g G : ℝ → ℝ} {m A L M B : ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hL : 0 ≤ L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hpos : ∀ x ∈ J, m ≤ betheCountingDerivative Δ N n p x)
    (hLipD : ∀ x ∈ J, ∀ y ∈ J, |betheCountingDerivative Δ N n p x -
      betheCountingDerivative Δ N n p y| ≤ M * |x - y|)
    (hg : ∀ x ∈ J, HasDerivAt g (G x) x) (hG : ∀ x ∈ J, |G x| ≤ A)
    (hLipG : ∀ x ∈ J, ∀ y ∈ J, |G x - G y| ≤ L * |x - y| + B) :
    |(∑ j, g (p j)) - (N : ℝ) * (∫ x in (-Real.pi)..Real.pi, g x * betheCountingDerivative Δ N n p x) +
      (r : ℝ) * (g (-Real.pi) + g Real.pi)| ≤
      ((L + A / m * M) / m ^ 2 + 2 * A * ((r : ℝ) + 1 / 2) * (r + 1) / m) / N + B / m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let F := betheCountingFunction Δ N (k + 1) p
  let D := betheCountingDerivative Δ N (k + 1) p
  let b := (r : ℝ) + 1 / 2
  let C := L + A / m * M
  have hN : 0 < N := by omega
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hbpos : 0 < b := by positivity
  have hC : 0 ≤ C := by positivity
  have hcnt : (N : ℝ) = 2 * ((k : ℝ) + 1 + r) := by exact_mod_cast hcount
  have hF (x : ℝ) : HasDerivAt F (D x) x := hasDerivAt_betheCountingFunction hΔ _ _ p x
  have hD : Continuous D := continuous_betheCountingDerivative hΔ _ _ p
  have hpr (j : Fin (k + 1)) : p j ∈ J := Ioo_subset_Icc_self (hp.1 j)
  have hroot (j : Fin (k + 1)) : F (p j) = ((j.val : ℝ) - (k : ℝ) / 2) / (N : ℝ) := by
    dsimp [F]
    rw [betheCountingFunction_root_value hN p hBE]
    unfold discreteBetheIndex
    push_cast
    ring
  have hboundary : F Real.pi = (k / 2 + b) / (N : ℝ) := by
    dsimp [F]
    rw [betheCountingFunction_pi hp hN, div_mul_eq_div_div]
    congr 1
    dsimp [b]; push_cast; linarith
  have hpneg : F (-Real.pi) = -F Real.pi := betheCountingFunction_neg hp _
  have hincL : F (p 0) - F (-Real.pi) = b / N := by simp [hroot, hpneg, hboundary]; ring
  have hincR : F Real.pi - F (p (Fin.last k)) = b / N := by simp [hroot, hboundary]; ring
  have hinc (j : Fin k) : F (p j.succ) - F (p j.castSucc) = 1 / (N : ℝ) := by
    simp [hroot, Fin.val_succ, Fin.val_castSucc]; ring
  have hsub {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) : Icc u v ⊆ J := ordConnected_Icc.out hu hv
  have hlen {u v : ℝ} := @counting_length_le F D m u v hm hF hpos
  have htrap (j : Fin k) : |(N : ℝ) * (∫ x in p j.castSucc..p j.succ, g x * D x) -
      (g (p j.castSucc) + g (p j.succ)) / 2| ≤ C / (m * N) ^ 2 + B / (m * N) := by
    let u := p j.castSucc
    let v := p j.succ
    have huv : u ≤ v := hp.2.1.monotone (by simp [Fin.le_def])
    have hu := hpr j.castSucc
    have hv := hpr j.succ
    have hI := hsub hu hv
    have hDu := hpos u hu
    have huD : 0 < D u := hm.trans_le hDu
    let c := G u / D u
    have hc : |c| ≤ A / m := by
      rw [abs_div, abs_of_pos huD]
      exact (div_le_div_of_nonneg_right (hG _ hu) huD.le).trans
        (div_le_div_of_nonneg_left hA hm hDu)
    have herror (x : ℝ) (hx : x ∈ Icc u v) : |G x - c * D x| ≤ C * (v - u) + B := by
      have hid : G x - c * D x = (G x - G u) + c * (D u - D x) := by
        dsimp [c]; field_simp; ring
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_sub_comm (D u) (D x)]
      have ha := hLipG x (hI hx) u hu
      have hb := hLipD x (hI hx) u hu
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at ha hb
      have hxv : x - u ≤ v - u := by linarith [hx.2]
      have h := mul_le_mul hc (hb.trans (mul_le_mul_of_nonneg_left hxv hM)) (abs_nonneg _) (by positivity)
      nlinarith only [ha.trans (add_le_add_left (mul_le_mul_of_nonneg_left hxv hL) B), h]
    have h := interval_trapezoid huv (fun x _ => hF x) hD.continuousOn
      (fun x hx => hg x (hI hx)) (fun x hx => hm.le.trans (hpos x (hI hx))) herror
    have hincj : F v - F u = 1 / (N : ℝ) := hinc j
    rw [hincj] at h
    have hl := hlen hu hv huv
    rw [hincj, div_div, mul_comm (N : ℝ)] at hl
    have hquad := pow_le_pow_left₀ (sub_nonneg.mpr huv) hl 2
    have h' := rescale_cell_error hNc h
    simp only [mul_one] at h'
    refine h'.trans (le_trans (?_ : _ ≤ C * (1 / (m * N)) ^ 2 + B * (1 / (m * N))) ?_)
    · nlinarith only [mul_le_mul_of_nonneg_left hquad hC, mul_le_mul_of_nonneg_left hl hB]
    · ring_nf; rfl
  have hbot : -Real.pi ∈ J := ⟨le_rfl, neg_le_self Real.pi_nonneg⟩
  have htop : Real.pi ∈ J := ⟨hbot.2, le_rfl⟩
  have hcg : ContinuousOn g J := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hcell {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v) (hinc : F v - F u = b / N)
      {x z : ℝ} (hx : x ∈ Icc u v) (hz : z ∈ Icc u v) : |g x - g z| ≤ A * (b / N / m) := by
    refine (abs_sub_le_of_hasDerivAt hg hG (hsub hu hv hx) (hsub hu hv hz)).trans
      (mul_le_mul_of_nonneg_left (le_trans ?_ (hinc ▸ hlen hu hv huv)) hA)
    exact abs_le.mpr (by constructor <;> linarith [hx.1, hx.2, hz.1, hz.2])
  have htail {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v) (hinc : F v - F u = b / N)
      {z : ℝ} (hz : z ∈ Icc u v) :
      |(N : ℝ) * (∫ x in u..v, g x * D x) - g z * b| ≤ A * (b / N / m) * b := by
    have hIv := hsub hu hv
    have h := interval_weighted_error (v := fun _ => g z) huv (fun x _ => hF x)
      (fun x _ => (hF x).const_mul (g z)) hD.continuousOn (hcg.mono hIv) continuousOn_const
      (fun x hx => hm.le.trans (hpos x (hIv hx))) (fun _ hx => hcell hu hv huv hinc hx hz)
    rw [← mul_sub, hinc] at h
    exact rescale_cell_error hNc h
  have hu := (hp.1 0).1.le
  have hv := (hp.1 (Fin.last k)).2.le
  have hleft := htail hbot (hpr 0) hu hincL ⟨le_rfl, hu⟩
  have hright := htail (hpr (Fin.last k)) htop hv hincR ⟨hv, le_rfl⟩
  have hendL := hcell hbot (hpr 0) hu hincL ⟨hu, le_rfl⟩ ⟨le_rfl, hu⟩
  have hendR := hcell (hpr (Fin.last k)) htop hv hincR ⟨le_rfl, hv⟩ ⟨hv, le_rfl⟩
  have hsplit : (∫ x in (-Real.pi)..Real.pi, g x * D x) =
      (∫ x in (-Real.pi)..p 0, g x * D x) +
      (∑ j : Fin k, ∫ x in p j.castSucc..p j.succ, g x * D x) +
      (∫ x in p (Fin.last k)..Real.pi, g x * D x) := by
    let I (v : ℝ) := ∫ x in (-Real.pi)..v, g x * D x
    have hI (v : ℝ) (hv : v ∈ J) : IntervalIntegrable (fun x => g x * D x) volume (-Real.pi) v :=
      ((hcg.mul hD.continuousOn).mono (ordConnected_Icc.uIcc_subset hbot hv)).intervalIntegrable
    have hsub' (u v : ℝ) (hu : u ∈ J) (hv : v ∈ J) :
        (∫ x in u..v, g x * D x) = I v - I u :=
      (intervalIntegral.integral_interval_sub_left (hI v hv) (hI u hu)).symm
    change I Real.pi = I (p 0) + _ + _
    rw [hsub' _ _ (hpr _) htop]
    simp_rw [hsub' _ _ (hpr _) (hpr _), sum_sub_distrib]
    have h₁ := Fin.sum_univ_succ (I ∘ p)
    have h₂ := Fin.sum_univ_castSucc (I ∘ p)
    simp only [Function.comp_apply] at h₁ h₂
    linarith
  let E (j : Fin k) := (N : ℝ) * (∫ x in p j.castSucc..p j.succ, g x * D x) -
    (g (p j.castSucc) + g (p j.succ)) / 2
  have hsum : |∑ j, E j| ≤ C / m ^ 2 / N + B / m := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => htrap j).trans ?_)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hk : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
    have h := mul_le_mul_of_nonneg_right hk (show 0 ≤ C / (m * (N : ℝ)) ^ 2 + B / (m * (N : ℝ)) by positivity)
    exact h.trans_eq (by field_simp)
  have hS := trapezoid_sum (g ∘ p)
  simp only [Function.comp_apply] at hS
  rw [hsplit, mul_add, mul_add, mul_sum, ← hS]
  dsimp only [E] at hsum
  rw [sum_sub_distrib] at hsum
  have htailBound : (2 * A * b * (r + 1) / m) / (N : ℝ) =
      2 * (A * (b / N / m) * b) + A * (b / N / m) := by dsimp [b]; ring
  conv_rhs => rw [add_div, htailBound]
  rw [abs_le] at hsum hleft hright hendL hendR ⊢
  dsimp [C, b] at hsum hleft hright hendL hendR ⊢
  constructor <;> linarith only [hsum.1, hsum.2, hleft.1, hleft.2, hright.1, hright.2,
    hendL.1, hendL.2, hendR.1, hendR.2]

/-- A coarser but simpler quadrature bound for bounded tests with bounded derivative. -/
noncomputable def countingQuadBound (m M A : ℝ) (r : ℕ) : ℝ :=
  (A / m * M) / m ^ 2 + 2 * A * ((r : ℝ) + 1 / 2) * (r + 1) / m +
    2 * A / m + 2 * r * A

theorem bethe_counting_quadrature_of_bounded_deriv {Δ : ℝ} (hΔ : Δ < -1) {N n r : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hcount : N = 2 * (n + r))
    (hBE : DiscreteBetheEquation Δ N n p) {g G : ℝ → ℝ} {m A M : ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hpos : ∀ x ∈ J, m ≤ betheCountingDerivative Δ N n p x)
    (hLip : ∀ x ∈ J, ∀ y ∈ J, |betheCountingDerivative Δ N n p x -
      betheCountingDerivative Δ N n p y| ≤ M * |x - y|)
    (hg : ∀ x ∈ J, HasDerivAt g (G x) x) (hG : ∀ x ∈ J, |G x| ≤ A)
    (hgb : ∀ x ∈ J, |g x| ≤ A) :
    |(∑ j, g (p j)) / (N : ℝ) - (∫ x in (-Real.pi)..Real.pi, g x * betheCountingDerivative Δ N n p x)| ≤
      countingQuadBound m M A r / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := bethe_counting_quadrature hΔ hp hn hcount hBE (L := 0) (B := 2 * A)
    hm hA le_rfl hM (by positivity) hpos hLip hg hG
    (fun x hx y hy => by simpa [two_mul] using (abs_sub (G x) (G y)).trans (add_le_add (hG x hx) (hG y hy)))
  have htop := hgb Real.pi ⟨neg_le_self Real.pi_nonneg, le_rfl⟩
  have hbot := hgb (-Real.pi) ⟨le_rfl, neg_le_self Real.pi_nonneg⟩
  have he := (abs_add_le (g (-Real.pi)) (g Real.pi)).trans (add_le_add hbot htop)
  have hR := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg r : 0 ≤ (r : ℝ))
  simp only [zero_add] at h
  have hh := h.trans (add_le_add_left (div_le_self (by positivity) hN1) _)
  have hid : (∑ j, g (p j)) / (N : ℝ) -
      (∫ x in (-Real.pi)..Real.pi, g x * betheCountingDerivative Δ N n p x) =
      ((∑ j, g (p j)) - (N : ℝ) * (∫ x in (-Real.pi)..Real.pi, g x * betheCountingDerivative Δ N n p x)) / N := by
    field_simp
  rw [hid, abs_div, abs_of_pos hN]
  apply div_le_div_of_nonneg_right _ hN.le
  have ht := abs_sub ((∑ j, g (p j)) - (N : ℝ) * (∫ x in (-Real.pi)..Real.pi,
    g x * betheCountingDerivative Δ N n p x) + (r : ℝ) * (g (-Real.pi) + g Real.pi))
    ((r : ℝ) * (g (-Real.pi) + g Real.pi))
  rw [add_sub_cancel_right, abs_mul, abs_of_nonneg (Nat.cast_nonneg r : 0 ≤ (r : ℝ))] at ht
  unfold countingQuadBound
  linarith only [ht, hh, hR]

end PottsDiscontinuity.Bethe
