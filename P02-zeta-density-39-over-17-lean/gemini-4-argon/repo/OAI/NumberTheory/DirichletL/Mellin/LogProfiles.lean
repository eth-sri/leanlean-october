module
public import OAI.NumberTheory.DirichletL.Mellin.ExponentialSmoothing

@[expose] public section

namespace OAI

open scoped BigOperators Topology
open MulChar AddChar Filter Asymptotics MeasureTheory


namespace FiniteRingSieve

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

omit [DecidableEq R] in
private theorem sum_chars_zero {a : R} (ha : a ≠ 1) :
    (∑ χ : MulChar R ℂ, χ a) = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

theorem sum_chars (a : R) :
    (∑ χ : MulChar R ℂ, χ a) =
      if a = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  split_ifs with ha
  · subst a
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
      simpa only [Nat.card_eq_fintype_card] using
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ
    exact_mod_cast hc
  · exact sum_chars_zero ha

theorem unit_char_orthogonal (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by
  calc
    _ = ∑ χ : MulChar R ℂ, χ ((u⁻¹ * v : Rˣ) : R) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
        Units.val_mul, map_mul]
    _ = if ((u⁻¹ * v : Rˣ) : R) = 1 then (Fintype.card Rˣ : ℂ) else 0 :=
      sum_chars _
    _ = _ := by simp only [Units.val_eq_one, inv_mul_eq_one]

end FiniteRingSieve

namespace FiniteFieldSieve

variable {F : Type*} [Field F] [Fintype F]

theorem primitive_gauss_norm_sq (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm : ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) =
      gaussSum χ ψ * star (gaussSum χ ψ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply, mul_comm]
  apply Complex.ofReal_inj.mp
  rw [hnorm]
  exact h

end FiniteFieldSieve


open Real
open scoped FourierTransform SchwartzMap ContDiff


namespace FourierBridge

theorem schwartz_log_inversion (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    g y = ∫ t : ℝ,
      Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) * (𝓕 g) t := by
  have hinv : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) = g := by simp
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f y) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul] using h.symm

theorem fourier_coefficient_moment (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0) (𝓕 g)) := by
  simpa using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume (𝓕 g) J 0

theorem exp_argument_derivative_bound
    (R a y H : ℝ) (i : ℕ)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : ℝ => R * Real.exp (a * z)) y‖ ≤
      (H ^ 2 * (1 + R)) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hR,
    abs_of_pos (Real.exp_pos _), abs_pow]
  have hpowH : H ≤ H ^ i := by
    calc H = H ^ 1 := by ring
         _ ≤ H ^ i := pow_le_pow_right₀ hH hi
  have hpowR : R ≤ (1 + R) ^ i := by
    calc R ≤ 1 + R := by linarith
         _ = (1 + R) ^ 1 := by ring
         _ ≤ (1 + R) ^ i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * (|a| ^ i * Real.exp (a * y)) ≤ R * (H ^ i * H) := by gcongr
    _ ≤ (1 + R) ^ i * (H ^ i * H ^ i) := by gcongr
    _ = (H ^ 2 * (1 + R)) ^ i := by simp only [mul_pow, pow_two]; ring

theorem coupled_factor_derivative_bound
    (F : ℝ → ℂ) (R a y H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hj : j ≤ n)
    (_hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
      j.factorial * (CF / (1 + R * Real.exp (a * y)) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hden : 0 < (1 + R * Real.exp (a * y)) ^ (A + n) := by positivity
  apply norm_iteratedFDeriv_comp_le hF harg (by simp) y
  · intro i hi
    apply (le_div_iff₀ hden).mpr
    simpa [mul_comm] using hFdecay i (hi.trans hj) _ hu
  · intro i hi₁ hi₂
    exact exp_argument_derivative_bound R a y H i hR hH ha hexp hi₁

theorem derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl

theorem coupled_factor_uniform_derivative
    (F : ℝ → ℂ) (R a y m H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hexpLower : m ≤ Real.exp (a * y))
    (hexpUpper : Real.exp (a * y) ≤ H)
    (hj : j ≤ n) (hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
        (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hcomp := coupled_factor_derivative_bound F R a y H CF A n j hF hR hH
    ha hexpUpper hj hCF hFdecay
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  have hlower : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpLower)]
  exact (mul_le_mul_of_nonneg_left hcomp hscale).trans
    (derivative_scale_absorption R (R * Real.exp (a * y)) m H CF A n j
      hR hm (by linarith) hCF (by positivity) hlower hj)

theorem fourier_seminorm_from_derivative_integrals
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
  have hpoint (w : ℝ) :=
    Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := ⊤) (N := ⊤) (f := (g : ℝ → ℂ)) (g.smooth ⊤)
      (by intro a b ha hb; exact g.integrable_pow_mul_iteratedFDeriv volume a b)
      (k := 0) (n := k) (by simp) (by simp) w
  have hpoint' (w : ℝ) :
      ‖w‖ ^ k * ‖(𝓕 g) w‖ ≤
        (2 : ℝ) ^ k *
          ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
            ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
    simpa [SchwartzMap.fourier_coe] using hpoint w
  apply SchwartzMap.seminorm_le_bound ℝ k 0 (𝓕 g) (by positivity)
  intro w
  simpa using hpoint' w

theorem uniform_fourier_seminorm_transfer
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (_hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := by
  let V : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hI (i : ℕ) (hi : i ≤ k) :
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤ V * C := by
    have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume g 0 i
    have hbase' :
        (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) := by
      simpa [V] using hbase
    calc
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          S * (V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) :=
        mul_le_mul_of_nonneg_left hbase' hS
      _ = V * (S * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) := by ring
      _ ≤ V * C := mul_le_mul_of_nonneg_left (hsource i hi) hV
  have hFourier := fourier_seminorm_from_derivative_integrals g k
  calc
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      S * ((2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) :=
      mul_le_mul_of_nonneg_left hFourier hS
    _ = (2 : ℝ) ^ k *
      ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        S * (∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ (2 : ℝ) ^ k *
      ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), V * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p.1 = 0 := by
        have hlt := Finset.mem_range.mp (Finset.mem_product.mp hp).1
        omega
      have hp2 : p.2 ≤ k := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      simpa [hp0] using hI p.2 hp2
    _ = (2 : ℝ) ^ k * (k + 1) * V * C := by
      simp []
      ring
    _ = (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := rfl

theorem uniform_fourier_coefficient_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  let K := J + p
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfourier_zero := uniform_fourier_seminorm_transfer g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hfourier_K := uniform_fourier_seminorm_transfer g K S C hS hC
    (by intro i hi; exact hsource i (by simpa [K, p] using hi))
  have hmoment := fourier_coefficient_moment g J
  calc
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
        S * (V * ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          (SchwartzMap.seminorm ℝ K 0) (𝓕 g))) :=
      mul_le_mul_of_nonneg_left (by simpa [V, K, p] using hmoment) hS
    _ = V * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        S * (SchwartzMap.seminorm ℝ K 0) (𝓕 g)) := by ring
    _ ≤ V * ((2 : ℝ) ^ 0 * (0 + 1) * V * C +
        (2 : ℝ) ^ K * (K + 1) * V * C) := by
      apply mul_le_mul_of_nonneg_left _ hV
      exact add_le_add (by simpa [V] using hfourier_zero)
        (by simpa [K, V] using hfourier_K)
    _ = _ := by simp [V, K, p, Nat.cast_add]

noncomputable def coefficientMomentBound (J : ℕ) (C : ℝ) : ℝ :=
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  V * (V * C + (2 : ℝ) ^ (J + p) * (J + p + 1) * V * C)

theorem coefficientMomentBound_nonneg (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ coefficientMomentBound J C := by
  unfold coefficientMomentBound
  positivity

theorem uniform_fourier_one_plus_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hIrhs : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hpow := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hintegral :
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
    calc
      _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
          (‖b t‖ + ‖t‖ ^ J * ‖b t‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (by intro t; positivity))
          hIrhs (Filter.Eventually.of_forall hpoint)
      _ = (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
        rw [integral_const_mul, integral_add hI0 hIJ]
  have hbound0 := uniform_fourier_coefficient_moment g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hboundJ := uniform_fourier_coefficient_moment g J S C hS hC hsource
  calc
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        S * ((2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖))) :=
      mul_le_mul_of_nonneg_left hintegral hS
    _ = (2 : ℝ) ^ J *
        (S * (∫ t : ℝ, ‖b t‖) +
          S * (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by ring
    _ ≤ (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa [coefficientMomentBound, b] using hbound0
      · simpa [coefficientMomentBound, b] using hboundJ

noncomputable def logPhase (t y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)

theorem logPhase_add (t u v : ℝ) :
    logPhase t (u + v) = logPhase t u * logPhase t v := by
  unfold logPhase
  convert Complex.exp_add _ _ using 1 ; push_cast ; ring_nf

theorem logPhase_zero (t : ℝ) : logPhase t 0 = 1 := by
  simp [logPhase]

theorem logPhase_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ℝ) (z : ι → ℝ) :
    logPhase t (∑ i ∈ s, z i) = ∏ i ∈ s, logPhase t (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logPhase_zero]
  | @insert i s hi ih => simp [hi, logPhase_add, ih]

theorem coupled_cutoff_active
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (V : ℝ → ℂ) (a y M : ι → ℝ)
    (hwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hVone : ∀ s,
      |s| ≤ ∑ j : ι, |a j| * M j → V s = 1)
    (hprod : (∏ j : ι, W j (y j)) ≠ 0) :
    V (∑ j : ι, a j * y j) = 1 := by
  classical
  apply hVone
  calc
    |∑ j : ι, a j * y j| ≤ ∑ j : ι, |a j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : ι, |a j| * M j := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonzero : W j (y j) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwindow j (y j) hnonzero) (abs_nonneg _)

theorem exists_complex_smooth_cutoff (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : ℝ → ℂ,
      HasCompactSupport V ∧
      ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      tsupport V ⊆ Set.Icc (-(T + 1)) (T + 1) ∧
      V 0 = 1 := by
  let U : Set ℝ := Set.Ioo (-(T + 1)) (T + 1)
  let K : Set ℝ := Set.Icc (-T) T
  have hU : IsOpen U := isOpen_Ioo
  have hK : IsClosed K := isClosed_Icc
  have hKU : K ⊆ U := by
    intro s hs
    rcases hs with ⟨hleft, hright⟩
    constructor <;> linarith
  obtain ⟨f, hf, _, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hK hKU
  let V : ℝ → ℂ := fun s => (f s : ℂ)
  have hf' : ContDiff ℝ ∞ f := by simpa using hf
  have hVs : ContDiff ℝ ∞ V := Complex.ofRealCLM.contDiff.comp hf'
  have hVsupport : Function.support V = Function.support f := by
    ext s
    simp [V, Function.mem_support]
  have hVsupportI : Function.support V ⊆
      Set.Icc (-(T + 1)) (T + 1) := by
    intro s hs
    rw [hVsupport, hsupport] at hs
    exact ⟨hs.1.le, hs.2.le⟩
  have hVtsupportI : tsupport V ⊆
      Set.Icc (-(T + 1)) (T + 1) :=
    closure_minimal hVsupportI isClosed_Icc
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hVsupportI
  have hone' : ∀ s, |s| ≤ T → V s = 1 := by
    intro s hs
    have hsK : s ∈ K := by simpa [K, abs_le] using hs
    have hfs : f s = 1 := (hone s).mp hsK
    simp [V, hfs]
  exact ⟨V, hVc, hVs, hone', hVtsupportI,
    hone' 0 (by simpa using hT)⟩

theorem exists_complex_smooth_cutoff_with_derivative_bounds
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by
  obtain ⟨V, hVc, hVs, hVone, hVsupport, _⟩ :=
    exists_complex_smooth_cutoff T hT
  obtain ⟨CW, hCW, hVderiv⟩ :=
    hVc.exists_bound_iteratedFDeriv hVs K
  refine ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, ?_⟩
  intro y hy
  obtain ⟨i, hi, hnonzero⟩ := hy
  have hyderiv : y ∈ Function.support (iteratedFDeriv ℝ i V) := by
    simpa [Function.mem_support] using hnonzero
  have hysupport : y ∈ tsupport V :=
    (support_iteratedFDeriv_subset i) hyderiv
  have hyinterval := hVsupport hysupport
  have hylower : -(T + 1) ≤ y := hyinterval.1
  have hyupper : y ≤ T + 1 := hyinterval.2
  constructor
  · exact Real.exp_le_exp.mpr hylower
  constructor
  · exact Real.exp_le_exp.mpr hyupper
  · exact abs_le.mpr ⟨hylower, hyupper⟩

noncomputable def schwartzDerivativeDecayConstant
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ∑ i ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 i) F +
        (SchwartzMap.seminorm ℝ M i) F)

theorem schwartzDerivativeDecayConstant_nonneg
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by
  unfold schwartzDerivativeDecayConstant
  positivity

theorem schwartz_derivative_decay_finite
    (F : 𝓢(ℝ, ℂ)) (A K j i : ℕ) (u : ℝ)
    (hj : j ≤ K) (hi : i ≤ j) (hu : 0 ≤ u) :
    (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤
      schwartzDerivativeDecayConstant F (A + K) K := by
  let M := A + K
  let T : ℝ := (SchwartzMap.seminorm ℝ 0 i) F +
    (SchwartzMap.seminorm ℝ M i) F
  let N : ℝ := ‖iteratedFDeriv ℝ i F u‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (1 + u) ^ (A + j) ≤ (1 + u) ^ M :=
    pow_le_pow_right₀ (by linarith) (by dsimp [M]; omega)
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu M
  have htwo : (2 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
  have hsum : (1 + u) ^ M * N ≤ (2 : ℝ) ^ M *
      (N + u ^ M * N) := by
    calc
      (1 + u) ^ M * N ≤
          (2 : ℝ) ^ (M - 1) * (1 ^ M + u ^ M) * N :=
        mul_le_mul_of_nonneg_right hadd hN
      _ ≤ (2 : ℝ) ^ M * (1 ^ M + u ^ M) * N := by
        gcongr
      _ = (2 : ℝ) ^ M * (N + u ^ M * N) := by
        simp; ring
  have h0 : N ≤ (SchwartzMap.seminorm ℝ 0 i) F := by
    simpa [N] using SchwartzMap.le_seminorm ℝ 0 i F u
  have hM : u ^ M * N ≤ (SchwartzMap.seminorm ℝ M i) F := by
    simpa [N, Real.norm_eq_abs, abs_of_nonneg hu] using
      SchwartzMap.le_seminorm ℝ M i F u
  have hT : N + u ^ M * N ≤ T := add_le_add h0 hM
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hTsum : T ≤ ∑ k ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 k) F +
        (SchwartzMap.seminorm ℝ M k) F) := by
    apply Finset.single_le_sum
      (f := fun k : ℕ =>
        (SchwartzMap.seminorm ℝ 0 k) F +
          (SchwartzMap.seminorm ℝ M k) F)
      (a := i)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hi.trans hj))
  calc
    (1 + u) ^ (A + j) * N ≤ (1 + u) ^ M * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ ≤ (2 : ℝ) ^ M * (N + u ^ M * N) := hsum
    _ ≤ (2 : ℝ) ^ M * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2 : ℝ) ^ M *
        (∑ k ∈ Finset.range (K + 1),
          ((SchwartzMap.seminorm ℝ 0 k) F +
            (SchwartzMap.seminorm ℝ M k) F)) :=
      mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ = schwartzDerivativeDecayConstant F (A + K) K := rfl
