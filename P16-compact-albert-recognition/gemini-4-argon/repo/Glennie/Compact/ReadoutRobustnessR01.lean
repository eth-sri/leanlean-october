module

public import Glennie.Diagonalization
public import Glennie.Sector
public import Glennie.Hilbert
public import Glennie.Covariance
public import Glennie.Theorems.Frames
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie.Compact.ReadoutRobustnessR01
open Glennie
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem norm_map (g : CompactAutomorphism) (x : Albert) : ‖g.equiv x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), native_norm_sq, native_norm_sq, g.inner_map]

theorem native_cauchy (x y : Albert) : |inner x y| ≤ ‖x‖ * ‖y‖ :=
  abs_real_inner_le_norm x y

private theorem octNormSq_smul (r : ℝ) (v : Octonion) :
    octNormSq (r • v) = r ^ 2 * octNormSq v := by
  simp [octNormSq, Quaternion.normSq_def', smul_eq_mul]; ring

private theorem diagonal_norm_sq (a b c : ℝ) :
    ‖diagonalAlbert a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [native_norm_sq, inner_self_coordinates]
  simp [diagonalAlbert, octNormSq, Quaternion.normSq_def']

private theorem diagonal_jordan (a b c : ℝ) (y : Albert) :
    jordan (diagonalAlbert a b c) y =
      ⟨a * y.d0, b * y.d1, c * y.d2, ((a + b) / 2) • y.o01, ((a + c) / 2) • y.o02, ((b + c) / 2) • y.o12⟩ := by
  ext <;> simp only [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul,
    octConj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
    Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
    Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, smul_eq_mul] <;> ring

private theorem diagonal_multiplier_sq (y : Albert) (t0 t1 t2 t01 t02 t12 q : ℝ)
    (h0 : t0 ^ 2 ≤ q) (h1 : t1 ^ 2 ≤ q) (h2 : t2 ^ 2 ≤ q)
    (h01 : t01 ^ 2 ≤ q) (h02 : t02 ^ 2 ≤ q) (h12 : t12 ^ 2 ≤ q) :
    ‖(⟨t0 * y.d0, t1 * y.d1, t2 * y.d2, t01 • y.o01, t02 • y.o02, t12 • y.o12⟩ : Albert)‖ ^ 2 ≤ q * ‖y‖ ^ 2 := by
  simp only [native_norm_sq, inner_self_coordinates, octNormSq_smul]
  nlinarith [mul_le_mul_of_nonneg_right h0 (sq_nonneg y.d0),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg y.d1),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg y.d2),
    mul_le_mul_of_nonneg_right h01 (octNormSq_nonneg y.o01),
    mul_le_mul_of_nonneg_right h02 (octNormSq_nonneg y.o02),
    mul_le_mul_of_nonneg_right h12 (octNormSq_nonneg y.o12)]

private theorem diagonal_reconstruct (x : Albert) (hx : IsDiagonal x) :
    x = diagonalAlbert x.d0 x.d1 x.d2 := by
  ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

theorem jordan_norm (x y : Albert) : ‖jordan x y‖ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨g, hg⟩ := native_diagonalization x
  rw [← norm_map g (jordan x y), ← norm_map g x, ← norm_map g y, g.map_jordan,
    diagonal_reconstruct (g.equiv x) hg]
  set a := (g.equiv x).d0; set b := (g.equiv x).d1; set c := (g.equiv x).d2
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, diagonal_norm_sq, diagonal_jordan]
  refine diagonal_multiplier_sq _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

theorem U_norm (x y : Albert) : ‖U x y‖ ≤ ‖x‖ ^ 2 * ‖y‖ := by
  obtain ⟨g, hg⟩ := native_diagonalization x
  rw [← norm_map g (U x y), ← norm_map g x, ← norm_map g y, g.map_U,
    diagonal_reconstruct (g.equiv x) hg]
  set a := (g.equiv x).d0; set b := (g.equiv x).d1; set c := (g.equiv x).d2
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, diagonal_norm_sq, U_diagonal]
  refine diagonal_multiplier_sq _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c,
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b), mul_nonneg (sq_nonneg a) (sq_nonneg c),
      mul_nonneg (sq_nonneg b) (sq_nonneg c)]

private theorem crossU_norm_sum_sq (x y w : Albert) :
    ‖crossU x y w‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * ‖w‖ := by
  have hp : crossU x y w = (1 / 2 : ℝ) • (U (x + y) w - U (x - y) w) := by
    simp only [crossU, U, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, jordan_comm y x]; module
  rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 := (norm_sub_le (U (x + y) w) (U (x - y) w)).trans (add_le_add (U_norm (x + y) w) (U_norm (x - y) w))
  have h2 := parallelogram_law_with_norm ℝ x y
  nlinarith [norm_nonneg w]

private theorem crossU_norm (x y w : Albert) :
    ‖crossU x y w‖ ≤ 2 * ‖x‖ * ‖y‖ * ‖w‖ := by
  by_cases hxy : ‖x‖ * ‖y‖ = 0
  · rcases mul_eq_zero.mp hxy with hx | hy
    · simp [norm_eq_zero.mp hx, crossU, jordan_zero_left, jordan_zero_right]
    · simp [norm_eq_zero.mp hy, crossU, jordan_zero_left, jordan_zero_right]
  · have hpos : 0 < ‖x‖ * ‖y‖ := lt_of_le_of_ne (by positivity) (Ne.symm hxy)
    have H := crossU_norm_sum_sq (‖y‖ • x) (‖x‖ • y) w
    have hsmul : crossU (‖y‖ • x) (‖x‖ • y) w = (‖x‖ * ‖y‖) • crossU x y w := by
      simp only [crossU, jordan_smul_left, jordan_smul_right, smul_smul]; module
    rw [hsmul, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hpos, abs_norm, abs_norm] at H
    nlinarith

theorem U_sub_base_radius (a b w : Albert) (R : ℝ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖U a w - U b w‖ ≤ 2 * R * ‖a - b‖ * ‖w‖ := by
  have hp : U a w - U b w = (1 / 2 : ℝ) • crossU (a + b) (a - b) w := by
    simp only [U, crossU, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, jordan_comm b a]; module
  rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 := crossU_norm (a + b) (a - b) w
  have h2 : ‖a + b‖ ≤ 2 * R := (norm_add_le a b).trans (by linarith)
  have h3 : 0 ≤ ‖a - b‖ * ‖w‖ := by positivity
  nlinarith

theorem phi_displacement_18 (x y z x' y' z' : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x - x'‖ ≤ δ) (hdy : ‖y - y'‖ ≤ δ) (hdz : ‖z - z'‖ ≤ δ) :
    |phi x y z - phi x' y' z'| ≤ 18 * R ^ 8 * δ := by
  have hUn {u w : Albert} {S : ℝ} (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ S) : ‖U u w‖ ≤ R ^ 2 * S :=
    (U_norm u w).trans (by gcongr)
  have hFn {a b c : Albert} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
      ‖U a (U b c) - U b (U a c)‖ ≤ 2 * R ^ 5 := by
    have h1 := hUn ha (hUn hb hc)
    have h2 := hUn hb (hUn ha hc)
    have h3 := norm_sub_le (U a (U b c)) (U b (U a c))
    linarith [show R ^ 2 * (R ^ 2 * R) = R ^ 5 by ring]
  have hHn {a b c : Albert} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
      ‖U c (jordan a b)‖ ≤ R ^ 4 := by
    have h1 : ‖jordan a b‖ ≤ R * R := (jordan_norm a b).trans (by gcongr)
    have h2 := hUn hc h1
    linarith [show R ^ 2 * (R * R) = R ^ 4 by ring]
  have h1st {a a' b c : Albert} (ha : ‖a‖ ≤ R) (ha' : ‖a'‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
      |phi a b c - phi a' b c| ≤ 6 * R ^ 8 * ‖a - a'‖ := by
    have hF : ‖(U a (U b c) - U b (U a c)) - (U a' (U b c) - U b (U a' c))‖ ≤ 4 * R ^ 4 * ‖a - a'‖ := by
      have heq : (U a (U b c) - U b (U a c)) - (U a' (U b c) - U b (U a' c)) =
          (U a (U b c) - U a' (U b c)) - U b (U a c - U a' c) := by simp only [U_sub_argument]; abel
      rw [heq]
      have s1 : ‖U a (U b c) - U a' (U b c)‖ ≤ 2 * R * ‖a - a'‖ * (R ^ 2 * R) :=
        (U_sub_base_radius a a' (U b c) R ha ha').trans (mul_le_mul_of_nonneg_left (hUn hb hc) (by positivity))
      have s2 : ‖U b (U a c - U a' c)‖ ≤ R ^ 2 * (2 * R * ‖a - a'‖ * R) :=
        hUn hb ((U_sub_base_radius a a' c R ha ha').trans (mul_le_mul_of_nonneg_left hc (by positivity)))
      have s3 := norm_sub_le (U a (U b c) - U a' (U b c)) (U b (U a c - U a' c))
      linarith [show 2 * R * ‖a - a'‖ * (R ^ 2 * R) + R ^ 2 * (2 * R * ‖a - a'‖ * R) = 4 * R ^ 4 * ‖a - a'‖ by ring]
    have hH : ‖U c (jordan a b) - U c (jordan a' b)‖ ≤ R ^ 3 * ‖a - a'‖ := by
      have heq : U c (jordan a b) - U c (jordan a' b) = U c (jordan (a - a') b) := by
        simp only [jordan_sub_left, U_sub_argument]
      rw [heq]
      have s1 : ‖jordan (a - a') b‖ ≤ ‖a - a'‖ * R := (jordan_norm (a - a') b).trans (by gcongr)
      have s2 := hUn hc s1
      linarith [show R ^ 2 * (‖a - a'‖ * R) = R ^ 3 * ‖a - a'‖ by ring]
    have hp : phi a b c - phi a' b c =
        inner ((U a (U b c) - U b (U a c)) - (U a' (U b c) - U b (U a' c))) (U c (jordan a b)) +
        inner (U a' (U b c) - U b (U a' c)) (U c (jordan a b) - U c (jordan a' b)) := by
      simp only [phi, inner_sub_left, inner_sub_right]; ring
    have c1 : |phi a b c - phi a' b c| ≤
        ‖(U a (U b c) - U b (U a c)) - (U a' (U b c) - U b (U a' c))‖ * ‖U c (jordan a b)‖ +
        ‖U a' (U b c) - U b (U a' c)‖ * ‖U c (jordan a b) - U c (jordan a' b)‖ := by
      rw [hp]; exact (abs_add_le _ _).trans (add_le_add (native_cauchy _ _) (native_cauchy _ _))
    have c2 := mul_le_mul hF (hHn ha hb hc) (norm_nonneg _) (by positivity)
    have c3 := mul_le_mul (hFn ha' hb hc) hH (norm_nonneg _) (by positivity)
    linarith [show 4 * R ^ 4 * ‖a - a'‖ * R ^ 4 + 2 * R ^ 5 * (R ^ 3 * ‖a - a'‖) = 6 * R ^ 8 * ‖a - a'‖ by ring]
  have s1 := h1st hx hx' hy hz
  have s2 : |phi x' y z - phi x' y' z| ≤ 6 * R ^ 8 * ‖y - y'‖ := by
    rw [show phi x' y z - phi x' y' z = -(phi y x' z - phi y' x' z) by
      rw [phi_swap_first_two y x', phi_swap_first_two y' x']; ring, abs_neg]
    exact h1st hy hy' hx' hz
  have s3 : |phi x' y' z - phi x' y' z'| ≤ 6 * R ^ 8 * ‖z - z'‖ := by
    rw [show phi x' y' z - phi x' y' z' = -(phi z y' x' - phi z' y' x') by
      rw [phi_swap_first_third z y' x', phi_swap_first_third z' y' x']; ring, abs_neg]
    exact h1st hz hz' hy' hx'
  have htri : |phi x y z - phi x' y' z'| ≤
      |phi x y z - phi x' y z| + |phi x' y z - phi x' y' z| + |phi x' y' z - phi x' y' z'| := by
    rw [show phi x y z - phi x' y' z' =
      (phi x y z - phi x' y z) + (phi x' y z - phi x' y' z) + (phi x' y' z - phi x' y' z') by ring]
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hR8 : 0 ≤ R ^ 8 := by positivity
  nlinarith

def quadraticWith {E : Type*} [AddCommGroup E] [Module ℝ E] (j : E → E → E) (a b : E) : E :=
  (2 : ℝ) • j a (j a b) - j (j a a) b

def phiWith {E : Type*} [AddCommGroup E] [Module ℝ E] (j : E → E → E) (B : E → E → ℝ) (x y z : E) : ℝ :=
  B (quadraticWith j x (quadraticWith j y z) - quadraticWith j y (quadraticWith j x z)) (quadraticWith j z (j x y))

theorem null_defect_response_radius {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jE : E → E → E) (f : Albert →ₗ[ℝ] E) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (hsubL : ∀ x y z, jE (x - y) z = jE x z - jE y z)
    (hsubR : ∀ x y z, jE x (y - z) = jE x y - jE x z)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUE : ∀ a b, ‖quadraticWith jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hnull : ∀ a b c, phiWith jE (Inner.inner ℝ) a b c = 0)
    (μ R : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hdef : ∀ a b : Albert, ‖f (jordan a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (x y z : Albert) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z| ≤ 38 * μ * R ^ 9 := by
  let fIso : Albert →ₗᵢ[ℝ] E := ⟨f, hf⟩
  have hQsub (a b c : E) : quadraticWith jE a (b - c) = quadraticWith jE a b - quadraticWith jE a c := by
    simp only [quadraticWith, hsubR]; module
  have hQ (a b : Albert) : ‖f (U a b) - quadraticWith jE (f a) (f b)‖ ≤ 6 * μ * ‖a‖ ^ 2 * ‖b‖ := by
    let D u v := f (jordan u v) - jE (f u) (f v)
    have hexp : f (U a b) - quadraticWith jE (f a) (f b) =
        (2 : ℝ) • D a (jordan a b) + (2 : ℝ) • jE (f a) (D a b) - D (jordan a a) b - jE (D a a) (f b) := by
      simp only [U, quadraticWith, D, map_sub, map_smul, hsubL, hsubR]; module
    have h1 : ‖D a (jordan a b)‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ :=
      (hdef a (jordan a b)).trans (by have := jordan_norm a b; nlinarith [norm_nonneg a, mul_nonneg hμ (norm_nonneg a)])
    have h2 : ‖jE (f a) (D a b)‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ :=
      (hE (f a) (D a b)).trans (by rw [hf]; have := hdef a b; nlinarith [norm_nonneg a])
    have h3 : ‖D (jordan a a) b‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ :=
      (hdef (jordan a a) b).trans (by have := jordan_norm a a; nlinarith [norm_nonneg b, mul_nonneg hμ (norm_nonneg b)])
    have h4 : ‖jE (D a a) (f b)‖ ≤ μ * ‖a‖ ^ 2 * ‖b‖ :=
      (hE (D a a) (f b)).trans (by rw [hf]; have := hdef a a; nlinarith [norm_nonneg b])
    have htri : ‖f (U a b) - quadraticWith jE (f a) (f b)‖ ≤
        2 * ‖D a (jordan a b)‖ + 2 * ‖jE (f a) (D a b)‖ + ‖D (jordan a a) b‖ + ‖jE (D a a) (f b)‖ := by
      rw [hexp]
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)
      exact (norm_add_le _ _).trans (by norm_num [norm_smul])
    linarith
  have hnest {a b c : Albert} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
      ‖f (U a (U b c)) - quadraticWith jE (f a) (quadraticWith jE (f b) (f c))‖ ≤ 12 * μ * R ^ 5 := by
    have heq : f (U a (U b c)) - quadraticWith jE (f a) (quadraticWith jE (f b) (f c)) =
        (f (U a (U b c)) - quadraticWith jE (f a) (f (U b c))) +
        quadraticWith jE (f a) (f (U b c) - quadraticWith jE (f b) (f c)) := by
      rw [hQsub]; abel
    have hUbc : ‖U b c‖ ≤ R ^ 2 * R := (U_norm b c).trans (by gcongr)
    have h1 : ‖f (U a (U b c)) - quadraticWith jE (f a) (f (U b c))‖ ≤ 6 * μ * R ^ 2 * (R ^ 2 * R) :=
      (hQ a (U b c)).trans (by gcongr)
    have h2 : ‖quadraticWith jE (f a) (f (U b c) - quadraticWith jE (f b) (f c))‖ ≤ R ^ 2 * (6 * μ * R ^ 2 * R) := by
      refine (hUE _ _).trans ?_
      rw [hf]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg a) ha 2)
        ((hQ b c).trans (by gcongr)) (norm_nonneg _) (by positivity)
    rw [heq]
    have htri := norm_add_le (f (U a (U b c)) - quadraticWith jE (f a) (f (U b c)))
      (quadraticWith jE (f a) (f (U b c) - quadraticWith jE (f b) (f c)))
    linarith [show 6 * μ * R ^ 2 * (R ^ 2 * R) + R ^ 2 * (6 * μ * R ^ 2 * R) = 12 * μ * R ^ 5 by ring]
  let commA := U x (U y z) - U y (U x z)
  let commE := quadraticWith jE (f x) (quadraticWith jE (f y) (f z)) -
    quadraticWith jE (f y) (quadraticWith jE (f x) (f z))
  let rightA := U z (jordan x y)
  let rightE := quadraticWith jE (f z) (jE (f x) (f y))
  have hF : ‖f commA - commE‖ ≤ 24 * μ * R ^ 5 := by
    have heq : f commA - commE =
        (f (U x (U y z)) - quadraticWith jE (f x) (quadraticWith jE (f y) (f z))) -
        (f (U y (U x z)) - quadraticWith jE (f y) (quadraticWith jE (f x) (f z))) := by
      simp only [commA, commE, map_sub]; abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith [hnest hx hy hz, hnest hy hx hz])
  have hH : ‖f rightA - rightE‖ ≤ 7 * μ * R ^ 4 := by
    have heq : f rightA - rightE =
        (f (U z (jordan x y)) - quadraticWith jE (f z) (f (jordan x y))) +
        quadraticWith jE (f z) (f (jordan x y) - jE (f x) (f y)) := by
      simp only [rightA, rightE, hQsub]; abel
    have hxy : ‖jordan x y‖ ≤ R * R := (jordan_norm x y).trans (by gcongr)
    have h1 : ‖f (U z (jordan x y)) - quadraticWith jE (f z) (f (jordan x y))‖ ≤ 6 * μ * R ^ 2 * (R * R) :=
      (hQ z (jordan x y)).trans (by gcongr)
    have h2 : ‖quadraticWith jE (f z) (f (jordan x y) - jE (f x) (f y))‖ ≤ R ^ 2 * (μ * R * R) := by
      refine (hUE _ _).trans ?_
      rw [hf]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz 2)
        ((hdef x y).trans (by gcongr)) (norm_nonneg _) (by positivity)
    rw [heq]
    have htri := norm_add_le (f (U z (jordan x y)) - quadraticWith jE (f z) (f (jordan x y)))
      (quadraticWith jE (f z) (f (jordan x y) - jE (f x) (f y)))
    linarith [show 6 * μ * R ^ 2 * (R * R) + R ^ 2 * (μ * R * R) = 7 * μ * R ^ 4 by ring]
  have hnH : ‖f rightA‖ ≤ R ^ 4 := by
    rw [hf]
    have hxy : ‖jordan x y‖ ≤ R * R := (jordan_norm x y).trans (by gcongr)
    exact (U_norm z (jordan x y)).trans (by calc ‖z‖ ^ 2 * ‖jordan x y‖ ≤ R ^ 2 * (R * R) := by gcongr
      _ = R ^ 4 := by ring)
  have hnF : ‖commE‖ ≤ 2 * R ^ 5 := by
    have h1 : ‖quadraticWith jE (f x) (quadraticWith jE (f y) (f z))‖ ≤ R ^ 2 * (R ^ 2 * R) := by
      refine (hUE _ _).trans ?_
      rw [hf]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hx 2)
        ((hUE (f y) (f z)).trans (by rw [hf, hf]; gcongr)) (norm_nonneg _) (by positivity)
    have h2 : ‖quadraticWith jE (f y) (quadraticWith jE (f x) (f z))‖ ≤ R ^ 2 * (R ^ 2 * R) := by
      refine (hUE _ _).trans ?_
      rw [hf]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy 2)
        ((hUE (f x) (f z)).trans (by rw [hf, hf]; gcongr)) (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (by linarith [show R ^ 2 * (R ^ 2 * R) = R ^ 5 by ring])
  have hexp : phi x y z =
      Inner.inner ℝ (f commA - commE) (f rightA) + Inner.inner ℝ commE (f rightA - rightE) := by
    have h0 := hnull (f x) (f y) (f z)
    change Inner.inner ℝ commE rightE = 0 at h0
    have h1 : phi x y z = Inner.inner ℝ (f commA) (f rightA) :=
      (fIso.inner_map_map commA rightA).symm
    rw [h1, _root_.inner_sub_left, _root_.inner_sub_right, h0]; ring
  have c1 : |phi x y z| ≤ ‖f commA - commE‖ * ‖f rightA‖ + ‖commE‖ * ‖f rightA - rightE‖ := by
    rw [hexp]
    exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
  have c2 := mul_le_mul hF hnH (norm_nonneg _) (by positivity)
  have c3 := mul_le_mul hnF hH (norm_nonneg _) (by positivity)
  linarith [show 24 * μ * R ^ 5 * R ^ 4 + 2 * R ^ 5 * (7 * μ * R ^ 4) = 38 * μ * R ^ 9 by ring]

def symmProd {M : Type*} [Ring M] [Algebra ℝ M] (a b : M) : M := (1 / 2 : ℝ) • (a * b + b * a)

theorem quadratic_eq_sandwich {M : Type*} [Ring M] [Algebra ℝ M] (a b : M) :
    quadraticWith symmProd a b = a * b * a := by
  simp only [quadraticWith, symmProd, smul_mul_assoc, mul_smul_comm,
    mul_add, add_mul, smul_add, smul_smul, mul_assoc]
  module

theorem map_quadraticWith {E M : Type*} [AddCommGroup E] [Module ℝ E] [Ring M] [Algebra ℝ M]
    (j : E → E → E) (ρ : E →ₗ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ρ (quadraticWith j a b) = quadraticWith symmProd (ρ a) (ρ b) := by
  simp only [quadraticWith, map_sub, map_smul, hj]

theorem phiWith_eq_zero_of_compatible_trace {E M : Type*} [AddCommGroup E] [Module ℝ E]
    [Ring M] [Algebra ℝ M] (j : E → E → E) (B : E → E → ℝ) (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, B a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a)) (x y z : E) :
    phiWith j B x y z = 0 := by
  unfold phiWith
  rw [hB]
  simp only [map_sub, map_quadraticWith j ρ hj, hj]
  let P := ρ x * ρ y * ρ z
  let Q := ρ y * ρ x * ρ z
  have hexpand :
      (2 : ℝ) • ((quadraticWith symmProd (ρ x) (quadraticWith symmProd (ρ y) (ρ z)) -
        quadraticWith symmProd (ρ y) (quadraticWith symmProd (ρ x) (ρ z))) *
        quadraticWith symmProd (ρ z) (symmProd (ρ x) (ρ y))) =
      P * Q * P + P * Q * Q - Q * P * P - Q * P * Q := by
    simp only [P, Q, quadratic_eq_sandwich, symmProd, smul_mul_assoc, mul_smul_comm,
      mul_add, add_mul, sub_mul, smul_add, smul_sub, smul_smul, mul_assoc]
    module
  have h₁ : τ (P * Q * P) = τ (Q * P * P) := by simpa only [mul_assoc] using hcyclic P (Q * P)
  have h₂ : τ (P * Q * Q) = τ (Q * P * Q) := by simpa only [mul_assoc] using hcyclic (P * Q) Q
  have hz : τ (P * Q * P + P * Q * Q - Q * P * P - Q * P * Q) = 0 := by
    simp only [map_add, map_sub, h₁, h₂]; ring
  rw [← hexpand, map_smul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem represented_product_norm {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing M] [NormedAlgebra ℝ M] (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ‖j a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← ρ.norm_map (j a b), hj, symmProd, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h1 := (norm_add_le (ρ a * ρ b) (ρ b * ρ a)).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  simp only [ρ.norm_map] at h1
  linarith

theorem represented_quadratic_norm {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing M] [NormedAlgebra ℝ M] (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ‖quadraticWith j a b‖ ≤ ‖a‖ ^ 2 * ‖b‖ := by
  rw [← ρ.norm_map (quadraticWith j a b)]
  change ‖ρ.toLinearMap (quadraticWith j a b)‖ ≤ _
  rw [map_quadraticWith j ρ.toLinearMap hj, quadratic_eq_sandwich]
  change ‖ρ a * ρ b * ρ a‖ ≤ ‖a‖ ^ 2 * ‖b‖
  have h1 := (norm_mul_le (ρ a * ρ b) (ρ a)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  simp only [ρ.norm_map] at h1
  linarith [show ‖a‖ * ‖b‖ * ‖a‖ = ‖a‖ ^ 2 * ‖b‖ by ring]

def diagonalNProduct {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => a i * b i)

theorem diagonalN_product_norm {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    ‖diagonalNProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq (diagonalNProduct a b),
    EuclideanSpace.real_norm_sq_eq b, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have ha : (a i) ^ 2 ≤ ‖a‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (a i)) (norm_nonneg a)).mpr (PiLp.norm_apply_le a i)
  change (a i * b i) ^ 2 ≤ ‖a‖ ^ 2 * (b i) ^ 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)

theorem diagonalN_quadratic_norm {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    ‖quadraticWith diagonalNProduct a b‖ ≤ ‖a‖ ^ 2 * ‖b‖ := by
  have hsand : quadraticWith diagonalNProduct a b = diagonalNProduct a (diagonalNProduct a b) := by
    ext i; change 2 * (a i * (a i * b i)) - (a i * a i) * b i = a i * (a i * b i); ring
  rw [hsand]
  exact (diagonalN_product_norm _ _).trans (by
    have := diagonalN_product_norm a b
    nlinarith [norm_nonneg a])

theorem diagonalN_phi_zero {n : ℕ} (x y z : EuclideanSpace ℝ (Fin n)) :
    phiWith diagonalNProduct (Inner.inner ℝ) x y z = 0 := by
  unfold phiWith
  have h0 : quadraticWith diagonalNProduct x (quadraticWith diagonalNProduct y z) -
      quadraticWith diagonalNProduct y (quadraticWith diagonalNProduct x z) = 0 := by
    ext i
    change (2 * (x i * (x i * (2 * (y i * (y i * z i)) - (y i * y i) * z i))) -
      (x i * x i) * (2 * (y i * (y i * z i)) - (y i * y i) * z i)) -
      (2 * (y i * (y i * (2 * (x i * (x i * z i)) - (x i * x i) * z i))) -
      (y i * y i) * (2 * (x i * (x i * z i)) - (x i * x i) * z i)) = 0
    ring
  rw [h0, _root_.inner_zero_left]

end
end Glennie.Compact.ReadoutRobustnessR01
