module

public import NormalizerLean.NewmanCond

@[expose] public section

/-!
# Newman's theorem: valuations, the local constants, and the element γ_p of Lemma 3

* `vz p x` is the p-adic valuation of an integer (0 at 0); `vv B p x` is the same but equal to the
  large value `B` at 0, so that zero entries can be handled by `omega` uniformly.
* the ultrametric relation for e = αδ − βγ in terms of `vv`;
* v_p(h), v_p(ε), v_p(n) in terms of ν = v_p(N);
* `exists_gamma_p`: for p ∣ N an element [[x, y], [N, t]] ∈ Γ₀(N) with min(v_p(t − x), ν) = v_p(ε)
  (x ≡ 3 or 2 mod p^ν by the Chinese remainder theorem).
-/

namespace NormalizerLean

/-- p-adic valuation of an integer (junk value 0 at 0). -/
def vz (p : ℕ) (x : ℤ) : ℕ := x.natAbs.factorization p

theorem vz_mul {p : ℕ} {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : vz p (x * y) = vz p x + vz p y := by
  simp [vz, Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.2 hx)
    (Int.natAbs_ne_zero.2 hy)]

theorem vz_neg (p : ℕ) (x : ℤ) : vz p (-x) = vz p x := by simp [vz]

theorem vz_natCast (p n : ℕ) : vz p n = n.factorization p := by simp [vz]

theorem pow_dvd_iff_le_vz {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (m : ℕ) :
    (p : ℤ) ^ m ∣ x ↔ m ≤ vz p x := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast,
    hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hx)]
  rfl

theorem vz_le_of_dvd (p : ℕ) {x y : ℤ} (hy : y ≠ 0) (hxy : x ∣ y) : vz p x ≤ vz p y := by
  have hx : x ≠ 0 := by rintro rfl; exact hy (zero_dvd_iff.1 hxy)
  exact (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.2 hx) (Int.natAbs_ne_zero.2 hy)).2
    (Int.natAbs_dvd_natAbs.2 hxy) p

/-- Valuation with value `B` at 0. -/
def vv (B p : ℕ) (x : ℤ) : ℕ := if x = 0 then B else vz p x

theorem vv_of_ne {B p : ℕ} {x : ℤ} (hx : x ≠ 0) : vv B p x = vz p x := if_neg hx

theorem vv_neg (B p : ℕ) (x : ℤ) : vv B p (-x) = vv B p x := by simp [vv, vz_neg]

/-- From `X ∣ K·x·y`: v(X) ≤ v(K) + v(x) + v(y). -/
theorem le_vv2 {B p : ℕ} {X K x y : ℤ} (hK : K ≠ 0) (hB : vz p X ≤ B) (h : X ∣ K * (x * y)) :
    vz p X ≤ vz p K + vv B p x + vv B p y := by
  by_cases hx : x = 0
  · simp [vv, hx]; omega
  by_cases hy : y = 0
  · simp [vv, hy]; omega
  rw [vv_of_ne hx, vv_of_ne hy]
  have := vz_le_of_dvd p (mul_ne_zero hK (mul_ne_zero hx hy)) h
  rw [vz_mul hK (mul_ne_zero hx hy), vz_mul hx hy] at this
  omega

/-- From `X ∣ K·x²`: v(X) ≤ v(K) + 2v(x). -/
theorem le_vv_sq {B p : ℕ} {X K x : ℤ} (hK : K ≠ 0) (hB : vz p X ≤ B) (h : X ∣ K * x ^ 2) :
    vz p X ≤ vz p K + 2 * vv B p x := by
  have := le_vv2 (x := x) (y := x) hK hB (by rwa [← pow_two])
  omega

/-! ### The ultrametric inequality -/

theorem vz_sub_ge {p : ℕ} (hp : p.Prime) {A C : ℤ} (hAC : A - C ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) :
    min (vz p A) (vz p C) ≤ vz p (A - C) := by
  rw [← pow_dvd_iff_le_vz hp hAC]
  exact dvd_sub ((pow_dvd_iff_le_vz hp hA _).2 (min_le_left _ _))
    ((pow_dvd_iff_le_vz hp hC _).2 (min_le_right _ _))

theorem vz_sub_eq {p : ℕ} (hp : p.Prime) {A C : ℤ} (hAC : A - C ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0)
    (hne : vz p A ≠ vz p C) : vz p (A - C) = min (vz p A) (vz p C) := by
  apply le_antisymm _ (vz_sub_ge hp hAC hA hC)
  by_contra hlt
  push Not at hlt
  have h1 := (pow_dvd_iff_le_vz hp hAC (min (vz p A) (vz p C) + 1)).2 hlt
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 := (pow_dvd_iff_le_vz hp hC (vz p A + 1)).2 (by omega)
    rw [min_eq_left h.le] at h1
    have h3 : (p : ℤ) ^ (vz p A + 1) ∣ A := by
      have := dvd_add h1 h2
      simpa using this
    have := (pow_dvd_iff_le_vz hp hA _).1 h3
    omega
  · have h2 := (pow_dvd_iff_le_vz hp hA (vz p C + 1)).2 (by omega)
    have h3 : (p : ℤ) ^ (vz p C + 1) ∣ C := by
      rw [min_eq_right h.le] at h1
      have := dvd_sub h2 h1
      simpa using this
    have := (pow_dvd_iff_le_vz hp hC _).1 h3
    omega

/-- The ultrametric relation for e = αδ − βγ, in terms of `vv`. -/
theorem ultra_vv {B p : ℕ} (hp : p.Prime) {α β γ δ : ℤ} (he : detS α β γ δ ≠ 0)
    (hB : vz p (detS α β γ δ) < B) :
    min (vv B p α + vv B p δ) (vv B p β + vv B p γ) ≤ vz p (detS α β γ δ) ∧
      (vv B p α + vv B p δ ≠ vv B p β + vv B p γ →
        vz p (detS α β γ δ) = min (vv B p α + vv B p δ) (vv B p β + vv B p γ)) := by
  by_cases had : α = 0 ∨ δ = 0
  · have hbg : β * γ ≠ 0 := by rcases had with rfl | rfl <;> simpa using he
    have hβ : β ≠ 0 := left_ne_zero_of_mul hbg
    have hγ : γ ≠ 0 := right_ne_zero_of_mul hbg
    have hev : vz p (detS α β γ δ) = vv B p β + vv B p γ := by
      rcases had with rfl | rfl <;>
      · simp only [zero_mul, mul_zero, zero_sub, vz_neg]
        rw [vz_mul hβ hγ, vv_of_ne hβ, vv_of_ne hγ]
    have hbig : B ≤ vv B p α + vv B p δ := by
      rcases had with rfl | rfl <;> simp [vv]
    constructor <;> [omega; (intro; omega)]
  push Not at had
  by_cases hbg' : β = 0 ∨ γ = 0
  · have hev : vz p (detS α β γ δ) = vv B p α + vv B p δ := by
      rcases hbg' with rfl | rfl <;>
      · simp only [zero_mul, mul_zero, sub_zero]
        rw [vz_mul had.1 had.2, vv_of_ne had.1, vv_of_ne had.2]
    have hbig : B ≤ vv B p β + vv B p γ := by
      rcases hbg' with rfl | rfl <;> simp [vv]
    constructor <;> [omega; (intro; omega)]
  push Not at hbg'
  have hA : α * δ ≠ 0 := mul_ne_zero had.1 had.2
  have hC : β * γ ≠ 0 := mul_ne_zero hbg'.1 hbg'.2
  rw [vv_of_ne had.1, vv_of_ne had.2, vv_of_ne hbg'.1, vv_of_ne hbg'.2, ← vz_mul had.1 had.2,
    ← vz_mul hbg'.1 hbg'.2]
  exact ⟨vz_sub_ge hp he hA hC, vz_sub_eq hp he hA hC⟩

/-! ### The local constants -/

theorem factorization_24 (p : ℕ) :
    (24 : ℕ).factorization p = if p = 2 then 3 else if p = 3 then 1 else 0 := by
  rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem factorization_hPart (N p : ℕ) :
    (hPart N).factorization p = if p = 2 then min 3 (N.factorization 2 / 2) else
      if p = 3 then min 1 (N.factorization 3 / 2) else 0 := by
  unfold hPart
  rw [Nat.factorization_mul (by positivity) (by positivity), Nat.prime_two.factorization_pow,
    Nat.prime_three.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem factorization_epsPart {N : ℕ} (hN : N ≠ 0) (p : ℕ) :
    (epsPart N).factorization p = min (N.factorization p) ((24 : ℕ).factorization p) := by
  unfold epsPart
  rw [Nat.factorization_gcd hN (by norm_num)]
  rfl

theorem local_constants {N p : ℕ} (hN : N ≠ 0) :
    (hPart N).factorization p = min ((epsPart N).factorization p) (N.factorization p / 2) := by
  rw [factorization_epsPart hN, factorization_24, factorization_hPart]
  split_ifs <;> simp_all <;> omega

end NormalizerLean

namespace NormalizerLean

/-! ### The element γ_p of Lemma 3 -/

/-- If x t − y N = 1, p^ν ∣ N, x ≡ r (mod p^ν), p ∤ x, p^ρ ∥ 1 − r², then
either ν ≤ ρ, or t − x ≠ 0 with v_p(t − x) = ρ. -/
theorem gamma_val {p ν ρ : ℕ} (hp : p.Prime) {N x y t r : ℤ} (hdet : x * t - y * N = 1)
    (hN : (p : ℤ) ^ ν ∣ N) (hxr : (p : ℤ) ^ ν ∣ r - x) (hpx : IsCoprime (p : ℤ) x)
    (hρ1 : (p : ℤ) ^ ρ ∣ 1 - r ^ 2) (hρ2 : ¬ (p : ℤ) ^ (ρ + 1) ∣ 1 - r ^ 2) :
    ν ≤ ρ ∨ (ρ < ν ∧ t - x ≠ 0 ∧ vz p (t - x) = ρ) := by
  rcases le_or_gt ν ρ with h | h
  · exact Or.inl h
  right
  -- x (t − x) ≡ 1 − r² (mod p^ν)
  have hcong : (p : ℤ) ^ ν ∣ x * (t - x) - (1 - r ^ 2) := by
    have : x * (t - x) - (1 - r ^ 2) = y * N + (r - x) * (r + x) := by linear_combination hdet
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hN _) (dvd_mul_of_dvd_left hxr _)
  have hle : ∀ m ≤ ν, (p : ℤ) ^ m ∣ x * (t - x) ↔ (p : ℤ) ^ m ∣ 1 - r ^ 2 := by
    intro m hm
    have hm' : (p : ℤ) ^ m ∣ x * (t - x) - (1 - r ^ 2) := (pow_dvd_pow _ hm).trans hcong
    constructor
    · intro h1; have := dvd_sub h1 hm'; simpa using this
    · intro h1; have := dvd_add hm' h1; simpa using this
  have hcop : ∀ m, IsCoprime ((p : ℤ) ^ m) x := fun m => hpx.pow_left
  have hnot : ¬ (p : ℤ) ^ (ρ + 1) ∣ t - x := by
    intro h1
    exact hρ2 ((hle (ρ + 1) h).1 (dvd_mul_of_dvd_right h1 _))
  have hs : t - x ≠ 0 := by
    intro h0
    rw [h0] at hnot
    exact hnot (dvd_zero _)
  have hyes : (p : ℤ) ^ ρ ∣ t - x :=
    (hcop ρ).dvd_of_dvd_mul_left ((hle ρ h.le).2 hρ1)
  refine ⟨h, hs, le_antisymm ?_ ((pow_dvd_iff_le_vz hp hs ρ).1 hyes)⟩
  by_contra hc
  exact hnot ((pow_dvd_iff_le_vz hp hs (ρ + 1)).2 (by omega))

end NormalizerLean
