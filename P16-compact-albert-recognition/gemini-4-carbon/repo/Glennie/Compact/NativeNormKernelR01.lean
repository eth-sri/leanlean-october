module
public import Glennie.Diagonalization
public import Glennie.Covariance
public import Glennie.SectorModel
public import Glennie.Hilbert
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

private theorem diagonal_multiplier_sq (y : Albert) (t0 t1 t2 t01 t02 t12 q : ℝ)
    (h0 : t0 ^ 2 ≤ q) (h1 : t1 ^ 2 ≤ q) (h2 : t2 ^ 2 ≤ q)
    (h01 : t01 ^ 2 ≤ q) (h02 : t02 ^ 2 ≤ q) (h12 : t12 ^ 2 ≤ q) :
    ‖(⟨t0 * y.d0, t1 * y.d1, t2 * y.d2, t01 • y.o01, t02 • y.o02, t12 • y.o12⟩ : Albert)‖ ^ 2 ≤ q * ‖y‖ ^ 2 := by
  have hos (r : ℝ) (v : Octonion) : octNormSq (r • v) = r ^ 2 * octNormSq v := by
    simp [octNormSq, Quaternion.normSq_def', smul_eq_mul]; ring
  simp only [native_norm_sq, inner_self_coordinates, hos]
  nlinarith [mul_le_mul_of_nonneg_right h0 (sq_nonneg y.d0), mul_le_mul_of_nonneg_right h1 (sq_nonneg y.d1),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg y.d2), mul_le_mul_of_nonneg_right h01 (octNormSq_nonneg y.o01),
    mul_le_mul_of_nonneg_right h02 (octNormSq_nonneg y.o02), mul_le_mul_of_nonneg_right h12 (octNormSq_nonneg y.o12)]

private theorem diag_op_norm (F : Albert → Albert → Albert) (k : ℕ)
    (hmap : ∀ (g : CompactAutomorphism) x y, g.equiv (F x y) = F (g.equiv x) (g.equiv y))
    (hdiag : ∀ a b c (y : Albert), ‖F (diagonalAlbert a b c) y‖ ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ k * ‖y‖ ^ 2)
    (x y : Albert) : ‖F x y‖ ≤ ‖x‖ ^ k * ‖y‖ := by
  have hna (g : CompactAutomorphism) (z : Albert) : ‖g.equiv z‖ = ‖z‖ := by
    nlinarith [norm_nonneg (g.equiv z), norm_nonneg z, show ‖g.equiv z‖ ^ 2 = ‖z‖ ^ 2 by rw [native_norm_sq, native_norm_sq, g.inner_map]]
  obtain ⟨g, hg⟩ := native_diagonalization x
  set u := g.equiv x
  have hrec : g.equiv x = diagonalAlbert u.d0 u.d1 u.d2 := by apply Albert.ext <;> simp [diagonalAlbert, hg.1, hg.2.1, hg.2.2, u]
  have hns : ‖diagonalAlbert u.d0 u.d1 u.d2‖ ^ 2 = u.d0 ^ 2 + u.d1 ^ 2 + u.d2 ^ 2 := by
    rw [native_norm_sq, inner_self_coordinates]; simp [diagonalAlbert, octNormSq, Quaternion.normSq_def']
  rw [← hna g (F x y), hmap, hrec, ← hna g x, hrec, ← hna g y]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    (by rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hns]; exact hdiag _ _ _ _)

theorem jordan_norm (x y : Albert) : ‖jordan x y‖ ≤ ‖x‖ * ‖y‖ := by
  simpa only [pow_one] using diag_op_norm jordan 1 (fun g => g.map_jordan) (fun a b c y => by
    rw [show jordan (diagonalAlbert a b c) y = ⟨a * y.d0, b * y.d1, c * y.d2,
        ((a + b) / 2) • y.o01, ((a + c) / 2) • y.o02, ((b + c) / 2) • y.o12⟩ by
      ext <;> simp [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
        octDot_coordinates, octMul, octConj, smul_smul, smul_eq_mul] <;> ring <;> exact Or.inl trivial, pow_one]
    exact diagonal_multiplier_sq _ _ _ _ _ _ _ _ (by nlinarith [sq_nonneg b, sq_nonneg c])
      (by nlinarith [sq_nonneg a, sq_nonneg c]) (by nlinarith [sq_nonneg a, sq_nonneg b])
      (by nlinarith [sq_nonneg (a - b), sq_nonneg c]) (by nlinarith [sq_nonneg (a - c), sq_nonneg b])
      (by nlinarith [sq_nonneg (b - c), sq_nonneg a])) x y

theorem U_norm (x y : Albert) : ‖U x y‖ ≤ ‖x‖ ^ 2 * ‖y‖ :=
  diag_op_norm U 2 (fun g => g.map_U) (fun a b c y => by
    rw [U_diagonal]
    have hb1 (p q r : ℝ) : (p ^ 2) ^ 2 ≤ (p ^ 2 + q ^ 2 + r ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (q ^ 2 + r ^ 2), mul_nonneg (sq_nonneg p) (sq_nonneg q), mul_nonneg (sq_nonneg p) (sq_nonneg r)]
    have hb2 (p q r : ℝ) : (p * q) ^ 2 ≤ (p ^ 2 + q ^ 2 + r ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (p ^ 2 - q ^ 2), sq_nonneg (p ^ 2 + q ^ 2 + r ^ 2),
        mul_nonneg (sq_nonneg r) (sq_nonneg p), mul_nonneg (sq_nonneg r) (sq_nonneg q), mul_nonneg (sq_nonneg p) (sq_nonneg q)]
    exact diagonal_multiplier_sq _ _ _ _ _ _ _ _ (hb1 a b c) (by linarith [hb1 b a c]) (by linarith [hb1 c a b])
      (hb2 a b c) (by linarith [hb2 a c b]) (by linarith [hb2 b c a])) x y

private theorem U_sub_base_radius (a b w : Albert) (R : ℝ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖U a w - U b w‖ ≤ 2 * R * ‖a - b‖ * ‖w‖ := by
  have hcU_sum (u v : Albert) : ‖crossU u v w‖ ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) * ‖w‖ := by
    rw [show crossU u v w = (1 / 2 : ℝ) • (U (u + v) w - U (u - v) w) by
      simp only [crossU, U, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, jordan_comm v u]; module,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    nlinarith [norm_sub_le (U (u + v) w) (U (u - v) w), U_norm (u + v) w, U_norm (u - v) w,
      parallelogram_law_with_norm ℝ u v, norm_nonneg w]
  have hcU (u v : Albert) : ‖crossU u v w‖ ≤ 2 * ‖u‖ * ‖v‖ * ‖w‖ := by
    by_cases huv : ‖u‖ * ‖v‖ = 0
    · rcases mul_eq_zero.mp huv with h0 | h0 <;> simp [norm_eq_zero.mp h0, crossU, jordan_zero_left, jordan_zero_right]
    · have H := hcU_sum (‖v‖ • u) (‖u‖ • v)
      rw [show crossU (‖v‖ • u) (‖u‖ • v) w = (‖u‖ * ‖v‖) • crossU u v w by
        simp only [crossU, jordan_smul_left, jordan_smul_right]; module] at H
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at H
      exact le_of_mul_le_mul_left (by nlinarith) (lt_of_le_of_ne (by positivity) (Ne.symm huv))
  rw [show U a w - U b w = (1 / 2 : ℝ) • crossU (a + b) (a - b) w by
    simp only [U, crossU, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, jordan_comm b a]; module,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  nlinarith [hcU (a + b) (a - b), norm_add_le a b, mul_nonneg (norm_nonneg (a - b)) (norm_nonneg w)]

theorem phi_displacement_18 (x y z x' y' z' : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x - x'‖ ≤ δ) (hdy : ‖y - y'‖ ≤ δ) (hdz : ‖z - z'‖ ≤ δ) :
    |phi x y z - phi x' y' z'| ≤ 18 * R ^ 8 * δ := by
  have hUr {a w : Albert} {S : ℝ} (ha : ‖a‖ ≤ R) (hw : ‖w‖ ≤ S) : ‖U a w‖ ≤ R ^ 2 * S :=
    (U_norm a w).trans ((by gcongr : ‖a‖ ^ 2 * ‖w‖ ≤ R ^ 2 * ‖w‖).trans (mul_le_mul_of_nonneg_left hw (sq_nonneg R)))
  have h1 {a a' b c : Albert} (ha : ‖a‖ ≤ R) (ha' : ‖a'‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
      |phi a b c - phi a' b c| ≤ 6 * R ^ 8 * ‖a - a'‖ := by
    set F1 := U a (U b c) - U b (U a c); set F2 := U a' (U b c) - U b (U a' c)
    set H1 := U c (jordan a b); set H2 := U c (jordan a' b)
    have hF2 : ‖F2‖ ≤ 2 * R ^ 5 := by
      linarith [norm_sub_le (U a' (U b c)) (U b (U a' c)), hUr ha' (hUr hb hc), hUr hb (hUr ha' hc)]
    have hH1 : ‖H1‖ ≤ R ^ 4 := by
      linarith [hUr hc ((jordan_norm a b).trans (by gcongr : ‖a‖ * ‖b‖ ≤ R * R))]
    have hdF : ‖F1 - F2‖ ≤ 4 * R ^ 4 * ‖a - a'‖ := by
      rw [show F1 - F2 = (U a (U b c) - U a' (U b c)) - U b (U a c - U a' c) by simp only [F1, F2, U_sub_argument]; abel]
      linarith [norm_sub_le (U a (U b c) - U a' (U b c)) (U b (U a c - U a' c)),
        (U_sub_base_radius a a' _ R ha ha').trans (mul_le_mul_of_nonneg_left (hUr hb hc) (by positivity)),
        hUr hb ((U_sub_base_radius a a' c R ha ha').trans (mul_le_mul_of_nonneg_left hc (by positivity)))]
    have hdH : ‖H1 - H2‖ ≤ R ^ 3 * ‖a - a'‖ := by
      rw [show H1 - H2 = U c (jordan (a - a') b) by simp only [H1, H2, jordan_sub_left, U_sub_argument]]
      linarith [hUr hc ((jordan_norm (a - a') b).trans (by gcongr : ‖a - a'‖ * ‖b‖ ≤ ‖a - a'‖ * R))]
    rw [show phi a b c - phi a' b c = inner (F1 - F2) H1 + inner F2 (H1 - H2) by
      change inner F1 H1 - inner F2 H2 = _; simp only [inner_sub_left, inner_sub_right]; ring]
    have b1 : |inner (F1 - F2) H1| ≤ (4 * R ^ 4 * ‖a - a'‖) * R ^ 4 :=
      (abs_real_inner_le_norm (F1 - F2) H1).trans (mul_le_mul hdF hH1 (norm_nonneg _) (by positivity))
    have b2 : |inner F2 (H1 - H2)| ≤ (2 * R ^ 5) * (R ^ 3 * ‖a - a'‖) :=
      (abs_real_inner_le_norm F2 (H1 - H2)).trans (mul_le_mul hF2 hdH (norm_nonneg _) (by positivity))
    linarith [abs_add_le (inner (F1 - F2) H1) (inner F2 (H1 - H2)),
      show (4 * R ^ 4 * ‖a - a'‖) * R ^ 4 + (2 * R ^ 5) * (R ^ 3 * ‖a - a'‖) = 6 * R ^ 8 * ‖a - a'‖ by ring]
  have h2 : |phi x' y z - phi x' y' z| ≤ 6 * R ^ 8 * ‖y - y'‖ := by
    rw [show phi x' y z - phi x' y' z = -(phi y x' z - phi y' x' z) by
      rw [phi_swap_first_two y x', phi_swap_first_two y' x']; ring, abs_neg]
    exact h1 hy hy' hx' hz
  have h3 : |phi x' y' z - phi x' y' z'| ≤ 6 * R ^ 8 * ‖z - z'‖ := by
    rw [show phi x' y' z - phi x' y' z' = -(phi z y' x' - phi z' y' x') by
      rw [phi_swap_first_third z y' x', phi_swap_first_third z' y' x']; ring, abs_neg]
    exact h1 hz hz' hy' hx'
  rw [show phi x y z - phi x' y' z' = (phi x y z - phi x' y z) + (phi x' y z - phi x' y' z) + (phi x' y' z - phi x' y' z') by ring]
  have hr8 : 0 ≤ R ^ 8 := by positivity
  nlinarith [abs_add_le (phi x y z - phi x' y z + (phi x' y z - phi x' y' z)) (phi x' y' z - phi x' y' z'),
    abs_add_le (phi x y z - phi x' y z) (phi x' y z - phi x' y' z), h1 hx hx' hy hz]

def QOp {V : Type*} [AddCommGroup V] [Module ℝ V] (j : V →ₗ[ℝ] V →ₗ[ℝ] V) (a b : V) : V :=
  (2 : ℝ) • j a (j a b) - j (j a a) b

theorem native_compatible_defect_response
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Ring M] [Algebra ℝ M]
    (jE : E →ₗ[ℝ] E →ₗ[ℝ] E) (f : Albert →ₗᵢ[ℝ] E)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖) (hUE : ∀ a b, ‖QOp jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = (1 / 2 : ℝ) • (ρ a * ρ b + ρ b * ρ a))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a))
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert, ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38 * μ * R ^ 9 := by
  have hQsub (a b c : E) : QOp jE a (b - c) = QOp jE a b - QOp jE a c := by simp only [QOp, map_sub]; module
  have hQerr (a b : Albert) : ‖f (U a b) - QOp jE (f a) (f b)‖ ≤ 6 * μ * ‖a‖ ^ 2 * ‖b‖ := by
    let D (u v : Albert) : E := f (jordan u v) - jE (f u) (f v)
    rw [show f (U a b) - QOp jE (f a) (f b) =
      (2 : ℝ) • D a (jordan a b) + (2 : ℝ) • jE (f a) (D a b) - D (jordan a a) b - jE (D a a) (f b) by
        simp only [U, QOp, D, map_sub, map_smul, LinearMap.sub_apply]; module]
    have h1 : ‖D a (jordan a b)‖ ≤ μ * ‖a‖ * (‖a‖ * ‖b‖) :=
      (hdef a (jordan a b)).trans (mul_le_mul_of_nonneg_left (jordan_norm a b) (by positivity))
    have h2 : ‖jE (f a) (D a b)‖ ≤ ‖a‖ * (μ * ‖a‖ * ‖b‖) :=
      (hE _ _).trans (by rw [f.norm_map]; exact mul_le_mul_of_nonneg_left (hdef a b) (norm_nonneg a))
    have h3 : ‖D (jordan a a) b‖ ≤ μ * (‖a‖ * ‖a‖) * ‖b‖ :=
      (hdef _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (jordan_norm a a) hμ) (norm_nonneg b))
    have h4 : ‖jE (D a a) (f b)‖ ≤ (μ * ‖a‖ * ‖a‖) * ‖b‖ :=
      (hE _ _).trans (by rw [f.norm_map]; exact mul_le_mul_of_nonneg_right (hdef a a) (norm_nonneg b))
    have hs1 : ‖(2 : ℝ) • D a (jordan a b)‖ = 2 * ‖D a (jordan a b)‖ := by norm_num [norm_smul]
    have hs2 : ‖(2 : ℝ) • jE (f a) (D a b)‖ = 2 * ‖jE (f a) (D a b)‖ := by norm_num [norm_smul]
    linarith [norm_sub_le ((2 : ℝ) • D a (jordan a b) + (2 : ℝ) • jE (f a) (D a b) - D (jordan a a) b) (jE (D a a) (f b)),
      norm_sub_le ((2 : ℝ) • D a (jordan a b) + (2 : ℝ) • jE (f a) (D a b)) (D (jordan a a) b),
      norm_add_le ((2 : ℝ) • D a (jordan a b)) ((2 : ℝ) • jE (f a) (D a b))]
  have hnest (a b c : Albert) :
      ‖f (U a (U b c)) - QOp jE (f a) (QOp jE (f b) (f c))‖ ≤ 12 * μ * ‖a‖ ^ 2 * ‖b‖ ^ 2 * ‖c‖ := by
    rw [show f (U a (U b c)) - QOp jE (f a) (QOp jE (f b) (f c)) =
      (f (U a (U b c)) - QOp jE (f a) (f (U b c))) + QOp jE (f a) (f (U b c) - QOp jE (f b) (f c)) by rw [hQsub]; abel]
    have h2 : ‖QOp jE (f a) (f (U b c) - QOp jE (f b) (f c))‖ ≤ ‖a‖ ^ 2 * (6 * μ * ‖b‖ ^ 2 * ‖c‖) := by
      simpa only [f.norm_map] using (hUE (f a) _).trans (mul_le_mul_of_nonneg_left (hQerr b c) (sq_nonneg _))
    linarith [norm_add_le (f (U a (U b c)) - QOp jE (f a) (f (U b c))) (QOp jE (f a) (f (U b c) - QOp jE (f b) (f c))),
      (hQerr a (U b c)).trans (mul_le_mul_of_nonneg_left (U_norm b c) (by positivity)), h2]
  set cA := U x (U y z) - U y (U x z)
  set cE := QOp jE (f x) (QOp jE (f y) (f z)) - QOp jE (f y) (QOp jE (f x) (f z))
  set rA := U z (jordan x y); set rE := QOp jE (f z) (jE (f x) (f y))
  have hcErr : ‖f cA - cE‖ ≤ 24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    rw [show f cA - cE = (f (U x (U y z)) - QOp jE (f x) (QOp jE (f y) (f z))) -
      (f (U y (U x z)) - QOp jE (f y) (QOp jE (f x) (f z))) by simp only [cA, cE, map_sub]; abel]
    linarith [norm_sub_le (f (U x (U y z)) - QOp jE (f x) (QOp jE (f y) (f z)))
      (f (U y (U x z)) - QOp jE (f y) (QOp jE (f x) (f z))), hnest x y z, hnest y x z]
  have hrErr : ‖f rA - rE‖ ≤ 7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    rw [show f rA - rE = (f (U z (jordan x y)) - QOp jE (f z) (f (jordan x y))) +
      QOp jE (f z) (f (jordan x y) - jE (f x) (f y)) by simp only [rA, rE, hQsub]; abel]
    have h2 : ‖QOp jE (f z) (f (jordan x y) - jE (f x) (f y))‖ ≤ ‖z‖ ^ 2 * (μ * ‖x‖ * ‖y‖) := by
      simpa only [f.norm_map] using (hUE (f z) _).trans (mul_le_mul_of_nonneg_left (hdef x y) (sq_nonneg _))
    linarith [norm_add_le (f (U z (jordan x y)) - QOp jE (f z) (f (jordan x y)))
      (QOp jE (f z) (f (jordan x y) - jE (f x) (f y))),
      (hQerr z (jordan x y)).trans (mul_le_mul_of_nonneg_left (jordan_norm x y) (by positivity)), h2]
  have hnrA : ‖f rA‖ ≤ ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    rw [f.norm_map]; linarith [(U_norm z (jordan x y)).trans (mul_le_mul_of_nonneg_left (jordan_norm x y) (sq_nonneg _))]
  have hncE : ‖cE‖ ≤ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    have hxy (a b : Albert) : ‖QOp jE (f a) (QOp jE (f b) (f z))‖ ≤ ‖a‖ ^ 2 * (‖b‖ ^ 2 * ‖z‖) := by
      simpa only [f.norm_map] using (hUE (f a) _).trans (mul_le_mul_of_nonneg_left (hUE (f b) (f z)) (sq_nonneg _))
    linarith [norm_sub_le (QOp jE (f x) (QOp jE (f y) (f z))) (QOp jE (f y) (QOp jE (f x) (f z))), hxy x y, hxy y x]
  have hQρ (a b : E) : ρ (QOp jE a b) = ρ a * ρ b * ρ a := by
    simp only [QOp, map_sub, map_smul, hj, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add, smul_smul, mul_assoc]; module
  have hnull : Inner.inner ℝ cE rE = 0 := by
    rw [hB]; simp only [cE, rE, map_sub, hQρ, hj]
    set X := ρ (f x); set Y := ρ (f y); set Z := ρ (f z); set P := X * Y * Z; set Q := Y * X * Z
    have hz0 : τ (P * Q * P + P * Q * Q - Q * P * P - Q * P * Q) = 0 := by
      simp only [map_add, map_sub, show τ (P * Q * P) = τ (Q * P * P) by simpa only [mul_assoc] using hcyclic P (Q * P),
        show τ (P * Q * Q) = τ (Q * P * Q) by simpa only [mul_assoc] using hcyclic (P * Q) Q]; ring
    rw [← show (2 : ℝ) • ((X * (Y * Z * Y) * X - Y * (X * Z * X) * Y) * (Z * ((1 / 2 : ℝ) • (X * Y + Y * X)) * Z)) =
      P * Q * P + P * Q * Q - Q * P * P - Q * P * Q by
        simp only [P, Q, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, sub_mul, mul_sub, smul_add, smul_sub, smul_smul, mul_assoc]; module,
      map_smul, smul_eq_mul] at hz0
    linarith
  rw [show phi x y z = Inner.inner ℝ (f cA - cE) (f rA) + Inner.inner ℝ cE (f rA - rE) by
    rw [show phi x y z = Inner.inner ℝ (f cA) (f rA) by rw [f.inner_map_map]; rfl,
      ← sub_zero (Inner.inner ℝ (f cA) (f rA)), ← hnull,
      _root_.inner_sub_left (f cA) cE, _root_.inner_sub_right cE (f rA) rE]; ring]
  have hb38 : (24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (‖z‖ ^ 2 * ‖x‖ * ‖y‖) +
      (2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖) ≤ 38 * μ * R ^ 9 := by
    rw [show (24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (‖z‖ ^ 2 * ‖x‖ * ‖y‖) +
      (2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖) = 38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 by ring,
      show 38 * μ * R ^ 9 = 38 * μ * R ^ 3 * R ^ 3 * R ^ 3 by ring]
    gcongr
  linarith [abs_add_le (Inner.inner ℝ (f cA - cE) (f rA)) (Inner.inner ℝ cE (f rA - rE)),
    (abs_real_inner_le_norm (f cA - cE) (f rA)).trans (mul_le_mul hcErr hnrA (norm_nonneg _) (by positivity)),
    (abs_real_inner_le_norm cE (f rA - rE)).trans (mul_le_mul hncE hrErr (norm_nonneg _) (by positivity))]

theorem represented_norms {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing M] [NormedAlgebra ℝ M] (jE : E →ₗ[ℝ] E →ₗ[ℝ] E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (jE a b) = (1 / 2 : ℝ) • (ρ a * ρ b + ρ b * ρ a)) :
    (∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖) ∧ (∀ a b, ‖QOp jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [← ρ.norm_map (jE a b), hj, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith [norm_add_le (ρ a * ρ b) (ρ b * ρ a), norm_mul_le (ρ a) (ρ b), norm_mul_le (ρ b) (ρ a),
      ρ.norm_map a, ρ.norm_map b, show ‖ρ a‖ * ‖ρ b‖ = ‖a‖ * ‖b‖ by simp only [ρ.norm_map],
      show ‖ρ b‖ * ‖ρ a‖ = ‖a‖ * ‖b‖ by simp only [ρ.norm_map]; ring]
  · rw [← ρ.norm_map (QOp jE a b), show ρ (QOp jE a b) = ρ a * ρ b * ρ a by
      change ρ.toLinearMap (QOp jE a b) = _
      simp only [QOp, map_sub, map_smul, LinearIsometry.coe_toLinearMap, hj,
        smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add, smul_smul, mul_assoc]; module]
    linarith [(norm_mul_le (ρ a * ρ b) (ρ a)).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)),
      show ‖ρ a‖ * ‖ρ b‖ * ‖ρ a‖ = ‖a‖ ^ 2 * ‖b‖ by simp only [ρ.norm_map]; ring]

end
end Glennie.Compact.NativeNormKernel
