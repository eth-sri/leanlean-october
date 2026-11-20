module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

namespace DedekindZetaZeroFree

namespace KubotaDefectSymbolAlgebra

variable (K : Type*) [Field K] (M : Type*) [CommGroup M] (B : Kˣ → Kˣ → M)

theorem one_left
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (a : Kˣ) : B 1 a = 1 := by
  have h := hL 1 1 a
  rw [one_mul] at h
  exact (mul_left_cancel (by rw [mul_one]; exact h)).symm

theorem one_right
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a : Kˣ) : B a 1 = 1 := by
  have h := hR a 1 1
  rw [mul_one] at h
  exact (mul_left_cancel (by rw [mul_one]; exact h)).symm

theorem inv_left
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (a b : Kˣ) : B a⁻¹ b = (B a b)⁻¹ := by
  have h := hL a a⁻¹ b
  rw [mul_inv_cancel, (one_left K M B hL b)] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem inv_right
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a b : Kˣ) : B a b⁻¹ = (B a b)⁻¹ := by
  have h := hR a b b⁻¹
  rw [mul_inv_cancel, (one_right K M B hR a)] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem inv_inv
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a b : Kˣ) : B a⁻¹ b⁻¹ = B a b := by
  rw [(inv_left K M B hL a b⁻¹), (inv_right K M B hR a b)]
  simp

theorem div_left
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (a b c : Kˣ) : B (a / b) c = B a c / B b c := by
  rw [div_eq_mul_inv, hL a b⁻¹ c, inv_left K M B hL b c, div_eq_mul_inv]

theorem div_right
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a b c : Kˣ) : B a (b / c) = B a b / B a c := by
  rw [div_eq_mul_inv, hR a b c⁻¹, inv_right K M B hR a c, div_eq_mul_inv]

theorem skew_symmetry
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (a b : Kˣ) : B a b = (B b a)⁻¹ := by
  have h := hL a b (a * b)
  grind [eq_inv_of_mul_eq_one_left]

theorem neg_one_right
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B a (-1) = 1 := by
  have h2 : (B a (-1)) ^ 2 = 1 := by
    rw [pow_two, ← hR a (-1) (-1), show (-1 : Kˣ) * (-1) = 1 by simp]
    exact one_right K M B hR a
  have h3 := hCub a (-1)
  rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ] at h3
  simp_all [h2, one_mul]

theorem neg_one_left
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B (-1) a = 1 := by
  have h2 : (B (-1) a) ^ 2 = 1 := by
    rw [pow_two, ← hL (-1) (-1) a, show (-1 : Kˣ) * (-1) = 1 by simp]
    exact one_left K M B hL a
  have h3 := hCub (-1) a
  rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ] at h3
  simp_all [h2, one_mul]

theorem neg_self
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B a (-a) = 1 := by
  rw [show -a = a * (-1) by simp, hR a a (-1), hAlt a,
    neg_one_right K M B hR hCub a, one_mul]

end KubotaDefectSymbolAlgebra

theorem kp_kubota_defect_symbol_algebra
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (r x y z t v p q : Kˣ) :
    B (z / r) (z / (x * p)) * B (t / z) (t / (v * p * q)) /
        (B (y / x) (y / (v * q)) * B (t / r) (t / (y * p))) =
      B (t * x / (z * y)) (z * y / (r * v * q)) := by
  let skew_symmetry₀ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt
  have s_tq := skew_symmetry₀ q t
  have s_vp := skew_symmetry₀ p v
  have s_vq := skew_symmetry₀ q v
  have s_pq := skew_symmetry₀ q p
  simp only [
    div_eq_mul_inv, hL, hR,
    KubotaDefectSymbolAlgebra.one_left K M B hL, KubotaDefectSymbolAlgebra.one_right K M B hR,
    KubotaDefectSymbolAlgebra.inv_left K M B hL, KubotaDefectSymbolAlgebra.inv_right K M B hR, hAlt,
    (skew_symmetry₀ x r), (skew_symmetry₀ y r), (skew_symmetry₀ z r), (skew_symmetry₀ t r), (skew_symmetry₀ v r), (skew_symmetry₀ p r), (skew_symmetry₀ q r), (skew_symmetry₀ y x), (skew_symmetry₀ z x), (skew_symmetry₀ t x), (skew_symmetry₀ v x), (skew_symmetry₀ p x), (skew_symmetry₀ q x), (skew_symmetry₀ z y), (skew_symmetry₀ t y), (skew_symmetry₀ v y), (skew_symmetry₀ p y), (skew_symmetry₀ q y), (skew_symmetry₀ t z), (skew_symmetry₀ v z), (skew_symmetry₀ p z), (skew_symmetry₀ q z), (skew_symmetry₀ v t), (skew_symmetry₀ p t), s_tq, s_vp, s_vq, s_pq]
  apply Additive.ofMul.injective
  have omul : ∀ p q : M, Additive.ofMul (p * q) = Additive.ofMul p + Additive.ofMul q :=
    fun p q => rfl
  have oinv : ∀ p : M, Additive.ofMul p⁻¹ = - Additive.ofMul p := fun p => rfl
  have oone : Additive.ofMul (1 : M) = 0 := rfl
  simp only [div_eq_mul_inv, omul, oinv, oone, one_mul, mul_one, inv_one]
  abel

end DedekindZetaZeroFree
