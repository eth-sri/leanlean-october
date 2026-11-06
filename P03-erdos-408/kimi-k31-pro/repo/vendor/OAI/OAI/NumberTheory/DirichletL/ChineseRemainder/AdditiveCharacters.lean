module

public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles

@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftCRT

open AddChar

variable {K : Type*} [Field K]

theorem addChar_crt_pair (ψ : AddChar K ℂ) (m n u v z : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hbez : u * n + v * m = 1) :
    ψ (z / (m * n)) = ψ (u * z / m) * ψ (v * z / n) := by
  rw [← map_add_eq_mul]
  congr 1
  calc
    z / (m * n) = z * (u * n + v * m) / (m * n) := by rw [hbez, mul_one]
    _ = u * z / m + v * z / n := by
      field_simp

theorem normalized_crt_pair {R : Type*} [CommRing R]
    (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam c₀ r d x u w : R)
    (hlam : ι lam ≠ 0) (hc₀ : ι c₀ ≠ 0) (hr : ι r ≠ 0)
    (hbez : u * r + (lam ^ 3 * w) * c₀ = 1) :
    ψ (-(ι d * (ι x / ι lam ^ 4)) / (ι c₀ * ι r)) =
      ψ (-(ι d * ι u * (ι x / ι lam ^ 4)) / ι c₀) *
        ψ (ι (-d * w * x) / (ι lam * ι r)) := by
  have hbezK : ι u * ι r + ι (lam ^ 3 * w) * ι c₀ = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg ι hbez
  have hsplit := addChar_crt_pair ψ (ι c₀) (ι r) (ι u)
    (ι (lam ^ 3 * w)) (-(ι d * (ι x / ι lam ^ 4))) hc₀ hr hbezK
  rw [hsplit]
  congr 1
  · congr 1
    ring
  · congr 1
    simp only [map_mul, map_pow, map_neg]
    field_simp

variable {R : Type*} [CommRing R]

end ShortDraftCRT


namespace ShortDraftTrace

open Complex
open scoped ComplexConjugate

section Generic

variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)

include hω hconj

omit hconj in
private lemma lam_ne_zero : (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω

private lemma conj_lam : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω

omit hconj in
private lemma omega_sub_square : ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω

theorem trace_div_lam (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square ω hω]; field_simp

theorem trace_character_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) +
       conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)))) = 1 := by
  rw [trace_div_lam ω hω hconj a b]
  calc
    _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ b := Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

end Generic

noncomputable def ω₃ : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem omega_sq : ω₃ ^ 2 = -ω₃ - 1 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
  have hquad : ω₃ ^ 2 + ω₃ + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold ω₃
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  linear_combination hquad

theorem omega_conj : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem eisenstein_trace_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) +
       conj (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)))) = 1 := by
  apply trace_character_period ω₃
  · rw [omega_sq]; ring
  · exact omega_conj

noncomputable def breveE : AddChar ℂ ℂ where
  toFun z := Complex.exp (2 * Real.pi * Complex.I * (z + conj z))
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    have harg : 2 * Real.pi * Complex.I * (z + w + conj (z + w)) =
        2 * Real.pi * Complex.I * (z + conj z) +
          2 * Real.pi * Complex.I * (w + conj w) := by
      rw [map_add]
      ring
    rw [harg, Complex.exp_add]

theorem breveE_period_lam (a b : ℤ) :
    breveE (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) = 1 := by
  exact eisenstein_trace_period a b

private theorem lam_eq_sqrt3_mul_I :
    1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
  unfold ω₃
  ring

private theorem sub_conj_eq (z : ℂ) :
    z - conj z = 2 * (z.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring

theorem breveE_div_lam_eq_e (z : ℂ) :
    breveE (z / (1 + 2 * ω₃)) =
      Complex.exp (4 * Real.pi * Complex.I * (z.im / Real.sqrt 3)) := by
  have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hl : ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  change Complex.exp (2 * Real.pi * Complex.I *
    (z / (1 + 2 * ω₃) + conj (z / (1 + 2 * ω₃)))) = _
  rw [lam_eq_sqrt3_mul_I]
  have hc : conj (((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) =
      -(((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [map_div₀, hc, div_neg, ← sub_eq_add_neg, ← sub_div, sub_conj_eq]
  congr 1
  field_simp
  ring

end ShortDraftTrace

end OAI
