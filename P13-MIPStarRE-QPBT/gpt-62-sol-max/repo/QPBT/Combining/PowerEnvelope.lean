module

public import QPBT.Games.ErrorFunctions

/-! A calculus for polynomial growth in the size and power decay in the noise. -/

@[expose] public section

namespace MIPStarRE.QPBT

/-- Parameters of a small-error regime: the size is at least one and the noise is in `[0,1]`. -/
structure ErrorDomain (Ω : Type*) where
  size : Ω → ℝ
  noise : Ω → ℝ
  size_ge_one : ∀ w, 1 ≤ size w
  noise_nonneg : ∀ w, 0 ≤ noise w
  noise_le_one : ∀ w, noise w ≤ 1

theorem IsPolyErr.nonneg_at {f : ℝ → ℝ} (h : IsPolyErr f) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ f x := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact (h x hx).1

theorem IsPolyErr₂.nonneg_at {f : ℝ → ℝ → ℝ} (h : IsPolyErr₂ f) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ f x y := by
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact (h x y hx hy).1

/-- A capped bound only has to be proved on the unit square. -/
theorem min_one_le_power_envelope {x y r s C z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hC : 1 ≤ C)
    (h : x ≤ 1 → y ≤ 1 → z ≤ C * (x ^ r + y ^ s)) :
    min 1 z ≤ C * (x ^ r + y ^ s) := by
  by_cases hx' : x ≤ 1
  · by_cases hy' : y ≤ 1
    · exact (min_le_right _ _).trans (h hx' hy')
    · exact (min_le_left _ _).trans (one_le_mul_of_one_le_of_one_le hC
        (by linarith [Real.rpow_nonneg hx r, Real.one_le_rpow (le_of_not_ge hy') hs]))
  · exact (min_le_left _ _).trans (one_le_mul_of_one_le_of_one_le hC
      (by linarith [Real.rpow_nonneg hy s, Real.one_le_rpow (le_of_not_ge hx') hr]))

/-- The canonical two-variable power envelope is polynomially small. -/
theorem isPolyErr₂_power_envelope {C r s : ℝ} (hC : 1 ≤ C) (hr : 0 < r) (hs : 0 < s) :
    IsPolyErr₂ (fun x y => C * (x ^ r + y ^ s)) :=
  ⟨C, r, s, hC, hr, hs, fun _ _ hx hy => ⟨by positivity, le_rfl⟩⟩

namespace ErrorDomain

variable {Ω : Type*} {D : ErrorDomain Ω} {f g : Ω → ℝ}

/-- A nonnegative error bounded by a power that vanishes at zero noise. -/
def Polynomial (D : ErrorDomain Ω) (f : Ω → ℝ) : Prop :=
  ∃ C a b : ℝ, 0 ≤ C ∧ 0 ≤ a ∧ 0 < b ∧ ∀ w,
    0 ≤ f w ∧ f w ≤ C * D.size w ^ a * D.noise w ^ b

private theorem size_pos (D : ErrorDomain Ω) (w : Ω) : 0 < D.size w :=
  zero_lt_one.trans_le (D.size_ge_one w)

theorem Polynomial.mono (hg : D.Polynomial g) (h : ∀ w, 0 ≤ f w ∧ f w ≤ g w) :
    D.Polynomial f := by
  obtain ⟨C, a, b, hC, ha, hb, hg⟩ := hg
  exact ⟨C, a, b, hC, ha, hb, fun w => ⟨(h w).1, (h w).2.trans (hg w).2⟩⟩

theorem polynomial_noise (D : ErrorDomain Ω) : D.Polynomial D.noise :=
  ⟨1, 0, 1, zero_le_one, le_rfl, zero_lt_one,
    fun w => ⟨D.noise_nonneg w, by simp⟩⟩

private theorem monomial_le (D : ErrorDomain Ω) (w : Ω) {a a' b b' : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hb' : 0 ≤ b') :
    D.size w ^ a * D.noise w ^ b ≤ D.size w ^ a' * D.noise w ^ b' :=
  mul_le_mul (Real.rpow_le_rpow_of_exponent_le (D.size_ge_one w) ha)
    (Real.rpow_le_rpow_of_exponent_ge' (D.noise_nonneg w) (D.noise_le_one w) hb' hb)
    (Real.rpow_nonneg (D.noise_nonneg w) _) (Real.rpow_nonneg (D.size_pos w).le _)

section

variable (hf : D.Polynomial f)
include hf

theorem Polynomial.add (hg : D.Polynomial g) :
    D.Polynomial (fun w => f w + g w) := by
  obtain ⟨C, a, b, hC, ha, hb, hf⟩ := hf
  obtain ⟨K, p, r, hK, hp, hr, hg⟩ := hg
  refine ⟨C + K, max a p, min b r, by positivity, ha.trans (le_max_left ..), by positivity,
    fun w => ⟨add_nonneg (hf w).1 (hg w).1, ?_⟩⟩
  have h₁ := mul_le_mul_of_nonneg_left
    (monomial_le D w (le_max_left a p) (min_le_left b r) (le_min hb.le hr.le)) hC
  have h₂ := mul_le_mul_of_nonneg_left
    (monomial_le D w (le_max_right a p) (min_le_right b r) (le_min hb.le hr.le)) hK
  linarith only [(hf w).2, (hg w).2, h₁, h₂]

/-- Multiplication by any nonnegative polynomial in the size preserves decay. -/
theorem Polynomial.mul_growth {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hg : ∀ w, 0 ≤ g w ∧ g w ≤ C * D.size w ^ a) : D.Polynomial (fun w => g w * f w) := by
  obtain ⟨K, p, b, hK, hp, hb, hf⟩ := hf
  refine ⟨C * K, a + p, b, by positivity, by positivity, hb,
    fun w => ⟨mul_nonneg (hg w).1 (hf w).1, ?_⟩⟩
  refine (mul_le_mul (hg w).2 (hf w).2 (hf w).1 ?_).trans_eq ?_
  · exact mul_nonneg hC (Real.rpow_nonneg (D.size_pos w).le _)
  · rw [Real.rpow_add (D.size_pos w)]
    ring

theorem Polynomial.scale {C : ℝ} (hC : 0 ≤ C) :
    D.Polynomial (fun w => C * f w) :=
  hf.mul_growth hC (a := 0) le_rfl (fun _ => ⟨hC, by simp⟩)

theorem Polynomial.mul_size :
    D.Polynomial (fun w => D.size w * f w) :=
  hf.mul_growth (C := 1) zero_le_one zero_le_one (fun w => ⟨(D.size_pos w).le, by simp⟩)

theorem Polynomial.rpow {p : ℝ} (hp : 0 < p) :
    D.Polynomial (fun w => f w ^ p) := by
  obtain ⟨C, a, b, hC, ha, hb, hf⟩ := hf
  refine ⟨C ^ p, a * p, b * p, Real.rpow_nonneg hC _, by positivity, by positivity,
    fun w => ⟨Real.rpow_nonneg (hf w).1 _, ?_⟩⟩
  refine (Real.rpow_le_rpow (hf w).1 (hf w).2 hp.le).trans_eq ?_
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg (D.size_pos w).le _))
      (Real.rpow_nonneg (D.noise_nonneg w) _),
    Real.mul_rpow hC (Real.rpow_nonneg (D.size_pos w).le _),
    ← Real.rpow_mul (D.size_pos w).le, ← Real.rpow_mul (D.noise_nonneg w)]

theorem Polynomial.sqrt : D.Polynomial (fun w => Real.sqrt (f w)) := by
  simpa only [Real.sqrt_eq_rpow] using hf.rpow (p := 1 / 2) (by norm_num)

theorem Polynomial.compose {err : ℝ → ℝ} (h : IsPolyErr err) :
    D.Polynomial (fun w => err (f w)) := by
  obtain ⟨C, a, hC, ha, h⟩ := h
  refine ((hf.rpow ha).scale (zero_le_one.trans hC)).mono (fun w => h _ ?_)
  obtain ⟨_, _, _, _, _, _, hf⟩ := hf
  exact (hf w).1

theorem Polynomial.compose₂ (hg : D.Polynomial g)
    {err : ℝ → ℝ → ℝ} (h : IsPolyErr₂ err) : D.Polynomial (fun w => err (f w) (g w)) := by
  obtain ⟨C, a, b, hC, ha, hb, h⟩ := h
  have h' := (((hf.rpow ha).add (hg.rpow hb)).scale (zero_le_one.trans hC))
  obtain ⟨_, _, _, _, _, _, hf⟩ := hf
  obtain ⟨_, _, _, _, _, _, hg⟩ := hg
  exact h'.mono fun w => h _ _ (hf w).1 (hg w).1

/-- Shrink the decay exponent and enlarge the prefactor at will. -/
theorem Polynomial.exists_envelope :
    ∃ C b : ℝ, 1 < C ∧ 0 < b ∧ b < 1 ∧
      ∀ w, f w ≤ C * D.size w ^ C * D.noise w ^ b := by
  obtain ⟨C, a, b, hC, ha, hb, hf⟩ := hf
  refine ⟨C + a + 2, min b (1/2), by linarith, by positivity, (min_le_right ..).trans_lt (by norm_num),
    fun w => (hf w).2.trans ?_⟩
  have hmon := monomial_le D w (show a ≤ C + a + 2 by linarith) (min_le_left b (1/2))
    (le_min hb.le (by norm_num))
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul (by linarith) hmon
    (mul_nonneg (Real.rpow_nonneg (D.size_pos w).le _) (Real.rpow_nonneg (D.noise_nonneg w) _))
    (by linarith)

end

end ErrorDomain

end MIPStarRE.QPBT
