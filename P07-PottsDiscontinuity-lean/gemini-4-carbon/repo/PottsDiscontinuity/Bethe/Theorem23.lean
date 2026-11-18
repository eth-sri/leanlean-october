module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Implicit
public import PottsDiscontinuity.Bethe.AsymptoticQuadrature
public import PottsDiscontinuity.Bethe.DiscreteBase
public import PottsDiscontinuity.Bethe.Theorem23Bootstrap

/-! # Theorem 2.3: analytic continuation and `O(1/N)` density control of Bethe roots -/

@[expose] public section

open Set Filter
open scoped BigOperators Topology

namespace PottsDiscontinuity.Bethe

/-! ### Phase difference `G` and partial derivatives of `θ` -/

private noncomputable def discreteBetheG (Δ x y : ℝ) : ℝ := theta Δ x y - theta Δ (-x) y
private noncomputable abbrev thetaPartialFirst (Δ x y : ℝ) : ℝ := d1Theta Δ x y
private noncomputable def thetaPartialSecond (Δ x y : ℝ) : ℝ := deriv (fun t => theta Δ x t) y

private theorem thetaPartialSecond_eq_neg_d1Theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    thetaPartialSecond Δ x y = -d1Theta Δ y x := by
  have heq : (fun t => theta Δ x t) = fun t => -theta Δ t x := funext fun t => theta_swap Δ t x
  unfold thetaPartialSecond d1Theta; rw [heq]
  exact ((analyticAt_theta_left hΔ y x).differentiableAt.hasDerivAt.neg).deriv

private theorem deriv_discreteBetheG_right {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    deriv (fun t => discreteBetheG Δ x t) y = thetaPartialSecond Δ x y - thetaPartialSecond Δ (-x) y :=
  deriv_fun_sub (analyticAt_theta_right hΔ x y).differentiableAt (analyticAt_theta_right hΔ (-x) y).differentiableAt

private theorem exists_uniform_discreteBetheG_deriv_bounds {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀,
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi, |deriv (fun t => discreteBetheG Δ x t) y| ≤ C) ∧
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi, ∀ z ∈ Icc (-Real.pi) Real.pi,
        |deriv (fun t => discreteBetheG Δ x t) y - deriv (fun t => discreteBetheG Δ x t) z| ≤ C * |y - z|) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_d1Theta_bounds hΔ₀
  refine ⟨2 * C, by positivity, fun Δ hΔ => ?_⟩
  have hvalid := lt_of_le_of_lt hΔ hΔ₀
  have hneg {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) : -x ∈ Icc (-Real.pi) Real.pi := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have heq (x y : ℝ) : deriv (fun t => discreteBetheG Δ x t) y = -d1Theta Δ y x + d1Theta Δ y (-x) := by
    rw [deriv_discreteBetheG_right hvalid, thetaPartialSecond_eq_neg_d1Theta hvalid, thetaPartialSecond_eq_neg_d1Theta hvalid]; ring
  refine ⟨fun x hx y hy => ?_, fun x hx y hy z hz => ?_⟩
  · rw [heq]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    linarith [((hb Δ hΔ).1 y hy x hx).1, ((hb Δ hΔ).1 y hy (-x) (hneg hx)).1]
  · rw [heq, heq, show -d1Theta Δ y x + d1Theta Δ y (-x) - (-d1Theta Δ z x + d1Theta Δ z (-x)) =
      -(d1Theta Δ y x - d1Theta Δ z x) + (d1Theta Δ y (-x) - d1Theta Δ z (-x)) by ring]
    have h₁ := (hb Δ hΔ).2 y hy x hx z hz x hx
    have h₂ := (hb Δ hΔ).2 y hy (-x) (hneg hx) z hz (-x) (hneg hx)
    simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (y - z))] at h₁ h₂
    refine (abs_add_le _ _).trans ?_; rw [abs_neg]; linarith

private theorem hasDerivAt_discreteBetheG_kMap {Δ : ℝ} (hΔ : Δ < -1) (α β : ℝ) :
    HasDerivAt (fun t => discreteBetheG Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) t))
      (Xi (2 * lamOf Δ) (α - β) - Xi (2 * lamOf Δ) (-α - β)) β := by
  let lam := lamOf Δ
  have hlam : 0 < 2 * lam := by linarith [lamOf_pos hΔ]
  have hfun : (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t)) =
      fun t => kMap (2 * lam) (-α - t) - kMap (2 * lam) (α - t) := by
    funext t; unfold discreteBetheG
    rw [← kMap_neg lam α, theta_kMap_lamOf hΔ α t, theta_kMap_lamOf hΔ (-α) t]; ring
  rw [hfun]
  have harg1 : HasDerivAt (fun t : ℝ => -α - t) (-1) β :=
    ((hasDerivAt_const β (-α)).sub (hasDerivAt_id β)).congr_deriv (by ring)
  have harg2 : HasDerivAt (fun t : ℝ => α - t) (-1) β :=
    ((hasDerivAt_const β α).sub (hasDerivAt_id β)).congr_deriv (by ring)
  exact (((hasDerivAt_kMap hlam (-α - β)).comp β harg1).sub
    ((hasDerivAt_kMap hlam (α - β)).comp β harg2)).congr_deriv (by dsimp [lam]; ring)

private theorem discreteBetheG_endpoint_bound {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) ≤
      4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) ∧
    4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) < 2 * Real.pi := by
  have hΔ' : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  let t := -Real.sin x; let dm := Real.cos x - 1 - 2 * Δ; let dp := Real.cos x + 1 - 2 * Δ
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1)
  have hdm : 0 < dm := by dsimp [dm]; linarith [Real.neg_one_le_cos x]
  have hdp : 0 < dp := by dsimp [dp]; linarith [Real.neg_one_le_cos x]
  have hform : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * Real.arctan (t / (2 * (-Δ) * (Real.cos x - Δ))) := by
    have hraw : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
        4 * (Real.arctan (t / dm) + Real.arctan (-t / dp)) := by
      unfold discreteBetheG theta
      simp only [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg, Real.sin_pi, Real.cos_pi,
        sub_zero, neg_zero, neg_div, Real.arctan_neg, t, dp, dm]; ring_nf
    have hprod : (t / dm) * (-t / dp) < 1 := by
      linarith [mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht hdm.le) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hdp.le)]
    rw [hraw, Real.arctan_add hprod]; congr 2
    have hcos : 0 < Real.cos x - Δ := by linarith [Real.neg_one_le_cos x]
    have hden : 2 * (-Δ) * (Real.cos x - Δ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (by linarith)) hcos.ne'
    have hden2 : dm * dp + t ^ 2 ≠ 0 := by positivity
    have hdenid : dm * dp + t ^ 2 = 4 * (-Δ) * (Real.cos x - Δ) := by dsimp [dm, dp, t]; nlinarith [Real.sin_sq_add_cos_sq x]
    field_simp [hdm.ne', hdp.ne', hden, hden2]
    rw [show dm * dp - -t ^ 2 = dm * dp + t ^ 2 by ring, hdenid]
    have hΔne : Δ ≠ 0 := by linarith
    field_simp [hΔne, hcos.ne']; ring
  rw [hform]
  let d := -Δ; let d₀ := -Δ₀; let c := Real.cos x
  have hd₀ : 1 < d₀ := by dsimp [d₀]; linarith
  have hd : d₀ ≤ d := by dsimp [d, d₀]; linarith
  have hc : -1 ≤ c := Real.neg_one_le_cos x
  have hcd : 0 < c + d := by linarith
  have hs₀ : 0 < d₀ ^ 2 - 1 := by nlinarith
  have hs : 0 < d ^ 2 - 1 := by nlinarith
  let w₀ := Real.sqrt (d₀ ^ 2 - 1); let w := Real.sqrt (d ^ 2 - 1)
  have hw₀ : 0 < w₀ := Real.sqrt_pos.mpr hs₀; have hw : 0 < w := Real.sqrt_pos.mpr hs
  have hsq : (t * w) ^ 2 ≤ (c + d) ^ 2 := by
    dsimp [t, c, w]; rw [mul_pow, Real.sq_sqrt hs.le]
    nlinarith [sq_nonneg (Real.cos x * d + 1), Real.sin_sq_add_cos_sq x]
  have hroot : t * w ≤ c + d := by nlinarith [mul_nonneg ht hw.le]
  have hdpos : 0 < d := by linarith
  have hd₀pos : 0 < d₀ := by linarith
  have harg : t / (2 * d * (c + d)) ≤ 1 / (2 * d₀ * w₀) := by
    have hleft : t / (c + d) ≤ 1 / w := (div_le_div_iff₀ hcd hw).2 (by nlinarith)
    have hprod : d₀ * w₀ ≤ d * w := mul_le_mul hd (Real.sqrt_le_sqrt (by nlinarith)) hw₀.le hdpos.le
    calc t / (2 * d * (c + d)) = (1 / (2 * d)) * (t / (c + d)) := by field_simp
      _ ≤ (1 / (2 * d)) * (1 / w) := mul_le_mul_of_nonneg_left hleft (by positivity)
      _ = 1 / (2 * d * w) := by field_simp
      _ ≤ 1 / (2 * d₀ * w₀) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have habs : |Δ₀| = d₀ := abs_of_neg (by linarith)
  refine ⟨mul_le_mul_of_nonneg_left (Real.arctan_le_arctan_iff.2 ?_) (by norm_num),
    by nlinarith [Real.arctan_lt_pi_div_two (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))), Real.pi_pos]⟩
  rw [habs, show Δ₀ ^ 2 = d₀ ^ 2 by dsimp [d₀]; ring]
  dsimp only [d, c, w₀] at harg
  convert harg using 2

/-! ### Symmetric subspace coordinates, Jacobian `A`, and rescaled `ATilde` -/

private def discreteHalfIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩

private def discreteHalfNextIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val + 1, by have := (discreteHalfIndex n j).isLt; omega⟩

private theorem discreteHalfIndex_lt_rev {n : ℕ} (j : Fin (n / 2)) :
    discreteHalfIndex n j < Fin.rev (discreteHalfIndex n j) := by
  change j.val < n - (j.val + 1); omega

private def discreteSymBasis (n : ℕ) (j : Fin (n / 2)) : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex n j then 1 else if ell = Fin.rev (discreteHalfIndex n j) then -1 else 0

private theorem discreteSymBasis_at_half {n : ℕ} (i k : Fin (n / 2)) :
    discreteSymBasis n k (discreteHalfIndex n i) = if i = k then 1 else 0 := by
  have hinj : discreteHalfIndex n i = discreteHalfIndex n k ↔ i = k :=
    ⟨fun h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h), fun h => by subst h; rfl⟩
  have hnot : discreteHalfIndex n i ≠ Fin.rev (discreteHalfIndex n k) := fun h => by
    have := discreteHalfIndex_lt_rev i; have := discreteHalfIndex_lt_rev k
    have hv := congrArg Fin.val h; simp only [discreteHalfIndex, Fin.val_rev] at *; omega
  simp [discreteSymBasis, hinj, hnot]

private theorem discreteSymBasis_mem_R_n_sym {n : ℕ} (k : Fin (n / 2)) :
    discreteSymBasis n k ∈ R_n_sym n := by
  let a := discreteHalfIndex n k
  have haa : a ≠ Fin.rev a := (discreteHalfIndex_lt_rev k).ne
  intro j
  by_cases h₁ : j = a
  · subst j; simp [discreteSymBasis, a, haa.symm]
  · by_cases h₂ : j = Fin.rev a
    · subst j; simp [discreteSymBasis, a, haa.symm]
    · have hr₁ : Fin.rev j ≠ a := fun h => h₂ (by simpa using congrArg Fin.rev h)
      have hr₂ : Fin.rev j ≠ Fin.rev a := fun h => h₁ (by simpa using congrArg Fin.rev h)
      simp [discreteSymBasis, a, h₁, h₂, hr₁, hr₂]

private noncomputable def discreteSymLift (n : ℕ) : (Fin (n / 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun q := ∑ j, q j • discreteSymBasis n j
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [mul_smul, Finset.smul_sum]

@[simp] private theorem discreteSymLift_half (n : ℕ) (q : Fin (n / 2) → ℝ) (i : Fin (n / 2)) :
    discreteSymLift n q (discreteHalfIndex n i) = q i := by
  simp [discreteSymLift, Finset.sum_apply, discreteSymBasis_at_half]

@[simp] private theorem discreteSymLift_single (n : ℕ) (i : Fin (n / 2)) :
    discreteSymLift n (Pi.single i 1) = discreteSymBasis n i := by
  simp [discreteSymLift, Pi.single_apply, ite_smul, Finset.sum_ite_eq']

private theorem discreteSymLift_mem (n : ℕ) (q : Fin (n / 2) → ℝ) :
    discreteSymLift n q ∈ R_n_sym n := by
  change (∑ j, q j • discreteSymBasis n j) ∈ R_n_sym n
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (discreteSymBasis_mem_R_n_sym j)

private theorem discreteSym_ext {n : ℕ} {p q : Fin n → ℝ}
    (hp : p ∈ R_n_sym n) (hq : q ∈ R_n_sym n)
    (h : ∀ i : Fin (n / 2), p (discreteHalfIndex n i) = q (discreteHalfIndex n i)) : p = q := by
  funext j
  by_cases hj : j.val < n / 2
  · exact h ⟨j.val, hj⟩
  · by_cases hr : (Fin.rev j).val < n / 2
    · have he := h ⟨(Fin.rev j).val, hr⟩
      change p (Fin.rev j) = q (Fin.rev j) at he; linarith [hp j, hq j]
    · have hfix : Fin.rev j = j := Fin.ext (by simp only [Fin.val_rev] at hr ⊢; omega)
      have hpj := hp j; have hqj := hq j; rw [hfix] at hpj hqj; linarith

private theorem discreteSymLift_coordinates {n : ℕ} (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) :
    discreteSymLift n (fun i => p (discreteHalfIndex n i)) = p :=
  discreteSym_ext (discreteSymLift_mem _ _) hp fun _ => discreteSymLift_half _ _ _

private noncomputable def discreteBetheMatrixA (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := fun i k =>
  if i = k then
    1 + (∑ ell ∈ Finset.univ.erase (discreteHalfIndex n i),
      thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p ell)) / (N : ℝ) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (Fin.rev (discreteHalfIndex n i))) / (N : ℝ)
  else
    (thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (discreteHalfIndex n k)) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (Fin.rev (discreteHalfIndex n k)))) / (N : ℝ)

private noncomputable def discreteBetheMatrixB (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
  Matrix.diagonal fun j => (N : ℝ) * (p (discreteHalfNextIndex n j) - p (discreteHalfIndex n j))

private noncomputable def discreteBetheMatrixATilde (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
  discreteBetheMatrixA Δ N n p * discreteBetheMatrixB N n p

private noncomputable def discreteBetheResidual (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun j => p j - discreteBetheMap Δ N n p j

private theorem hasDerivAt_theta_affine {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    HasDerivAt (fun t => theta Δ (x + t * a) (y + t * b))
      (a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y) 0 := by
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hF := (analyticAt_theta_xy hΔ x y).differentiableAt.hasFDerivAt
  have h₁ : thetaPartialFirst Δ x y = fderiv ℝ F (x, y) (1, 0) :=
    ((analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt).unique
      (hF.comp_hasDerivAt (f := fun s : ℝ => ((s, y) : ℝ × ℝ)) x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  have h₂ : thetaPartialSecond Δ x y = fderiv ℝ F (x, y) (0, 1) :=
    ((analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt).unique
      (hF.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  have hpath : HasDerivAt (fun t : ℝ => ((x + t * a, y + t * b) : ℝ × ℝ)) (a, b) 0 :=
    (((hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id 0).mul_const a)).congr_deriv (by ring)).prodMk
      (((hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id 0).mul_const b)).congr_deriv (by ring))
  have hF0 : HasFDerivAt F (fderiv ℝ F (x, y)) (x + 0 * a, y + 0 * b) := by simpa using hF
  change HasDerivAt (F ∘ fun t : ℝ => ((x + t * a, y + t * b) : ℝ × ℝ)) _ 0
  refine (hF0.comp_hasDerivAt (f := fun t : ℝ => ((x + t * a, y + t * b) : ℝ × ℝ)) 0 hpath).congr_deriv ?_
  rw [show ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) by ext <;> simp, map_add, map_smul, map_smul, ← h₁, ← h₂]
  simp [smul_eq_mul]

private theorem hasDerivAt_discreteBetheResidual_basis {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p : Fin n → ℝ) (i k : Fin (n / 2)) :
    HasDerivAt (fun t => discreteBetheResidual Δ N n (fun j => p j + t * discreteSymBasis n k j)
      (discreteHalfIndex n i)) (discreteBetheMatrixA Δ N n p i k) 0 := by
  let ri := discreteHalfIndex n i; let rk := discreteHalfIndex n k; let v := discreteSymBasis n k
  have hbase : HasDerivAt (fun t : ℝ => p ri + t * v ri - 2 * Real.pi * discreteBetheIndex n ri / (N : ℝ)) (v ri) 0 :=
    ((((hasDerivAt_const (0 : ℝ) (p ri)).add ((hasDerivAt_id 0).mul_const (v ri))).sub
      (hasDerivAt_const 0 _)).congr_deriv (by ring))
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun ell _ =>
    hasDerivAt_theta_affine hΔ (p ri) (p ell) (v ri) (v ell)).div_const (N : ℝ)
  have hgen : HasDerivAt (fun t => discreteBetheResidual Δ N n (fun j => p j + t * v j) ri)
      (v ri + (∑ ell : Fin n, (v ri * thetaPartialFirst Δ (p ri) (p ell) + v ell * thetaPartialSecond Δ (p ri) (p ell))) / (N : ℝ)) 0 := by
    refine (hbase.add hsum).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    dsimp [discreteBetheResidual, discreteBetheMap]; ring
  refine hgen.congr_deriv ?_
  have hsum2 : (∑ ell : Fin n, v ell * thetaPartialSecond Δ (p ri) (p ell)) =
      thetaPartialSecond Δ (p ri) (p rk) - thetaPartialSecond Δ (p ri) (p (Fin.rev rk)) := by
    have hab : rk ≠ Fin.rev rk := (discreteHalfIndex_lt_rev k).ne
    have hpt (ell : Fin n) : v ell * thetaPartialSecond Δ (p ri) (p ell) =
        (if ell = rk then thetaPartialSecond Δ (p ri) (p rk) else 0) +
          (if ell = Fin.rev rk then -thetaPartialSecond Δ (p ri) (p (Fin.rev rk)) else 0) := by
      by_cases h1 : ell = rk
      · subst ell; simp [v, discreteSymBasis, rk, hab]
      · by_cases h2 : ell = Fin.rev rk
        · subst ell; simp [v, discreteSymBasis, rk, h1]
        · simp [v, discreteSymBasis, rk, h1, h2]
    simp_rw [hpt]; rw [Finset.sum_add_distrib]; simp [Finset.sum_ite_eq']; ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum2, show v ri = if i = k then 1 else 0 from discreteSymBasis_at_half i k]
  by_cases hik : i = k
  · subst k; simp only [↓reduceIte, one_mul, discreteBetheMatrixA]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ri)]
    have hdiag : thetaPartialFirst Δ (p ri) (p ri) + thetaPartialSecond Δ (p ri) (p ri) = 0 := by
      unfold thetaPartialFirst d1Theta thetaPartialSecond
      exact deriv_theta_diag hΔ (p ri)
    have hnum : (thetaPartialFirst Δ (p ri) (p ri) + ∑ ell ∈ Finset.univ.erase ri, thetaPartialFirst Δ (p ri) (p ell)) +
        (thetaPartialSecond Δ (p ri) (p ri) - thetaPartialSecond Δ (p ri) (p (Fin.rev ri))) =
        (∑ ell ∈ Finset.univ.erase ri, thetaPartialFirst Δ (p ri) (p ell)) -
          thetaPartialSecond Δ (p ri) (p (Fin.rev ri)) := by linear_combination hdiag
    rw [hnum]; ring
  · simp only [hik, ↓reduceIte, zero_mul, zero_add, discreteBetheMatrixA]; ring

private theorem discreteS_n_half_coord_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (j : Fin (n / 2)) : p (discreteHalfIndex n j) < 0 := by
  have hlt := hp.2.1 (discreteHalfIndex_lt_rev j)
  rw [hp.2.2 (discreteHalfIndex n j)] at hlt; linarith

private theorem discreteBetheMatrixATilde_offdiag_eq {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) (hN : 0 < N)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    discreteBetheMatrixATilde Δ N n p i k =
      (p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k)) *
        deriv (fun y => discreteBetheG Δ (p (discreteHalfIndex n i)) y) (p (discreteHalfIndex n k)) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [discreteBetheMatrixATilde, Matrix.mul_apply]
  simp [discreteBetheMatrixB, Matrix.diagonal_apply]
  rw [discreteBetheMatrixA, ite_eq_right hik, hp (discreteHalfIndex n k)]
  simp only [thetaPartialSecond]
  rw [deriv_theta_right_neg, deriv_discreteBetheG_right hΔ]; simp only [thetaPartialSecond]; field_simp [hNne]

private theorem discreteBetheMatrixATilde_offdiag_nonneg {Δ : ℝ} {N n : ℕ}
    (hΔ : Δ < -1) (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    0 ≤ discreteBetheMatrixATilde Δ N n p i k := by
  rw [discreteBetheMatrixATilde_offdiag_eq hΔ p hp.2.2 hN i k hik]
  have hgap : 0 ≤ p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k) :=
    (sub_pos.mpr (hp.2.1 (show (discreteHalfIndex n k).val < (discreteHalfNextIndex n k).val by
      dsimp [discreteHalfIndex, discreteHalfNextIndex]; omega))).le
  refine mul_nonneg hgap ?_
  let x := p (discreteHalfIndex n i); let y := p (discreteHalfIndex n k)
  have hx : x ∈ Icc (-Real.pi) 0 := ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp i).le⟩
  have hy : y ∈ Icc (-Real.pi) 0 := ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp k).le⟩
  let lam := lamOf Δ; have hlam : 0 < lam := lamOf_pos hΔ
  obtain ⟨α, hα, hkx⟩ := (bijOn_kMap hlam).2.2 ⟨hx.1, hx.2.trans Real.pi_pos.le⟩
  obtain ⟨β, hβ, hky⟩ := (bijOn_kMap hlam).2.2 ⟨hy.1, hy.2.trans Real.pi_pos.le⟩
  have hneg_pre {u w : ℝ} (hw : w ≤ 0) (hk : kMap lam u = w) : u ≤ 0 := by
    by_contra h; have hka := strictMono_kMap hlam (lt_of_not_ge h); rw [hk, kMap_zero] at hka; linarith
  have hsα := Real.sin_nonpos_of_nonpos_of_neg_pi_le (hneg_pre hx.2 hkx) hα.1
  have hsβ := Real.sin_nonpos_of_nonpos_of_neg_pi_le (hneg_pre hy.2 hky) hβ.1
  have hcos : Real.cos (-α - β) ≤ Real.cos (α - β) := by
    have : Real.cos (α - β) - Real.cos (-α - β) = 2 * Real.sin α * Real.sin β := by
      rw [Real.cos_sub, Real.cos_sub, Real.cos_neg, Real.sin_neg]; ring
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hsα hsβ]
  have hXi_le : Xi (2 * lam) (-α - β) ≤ Xi (2 * lam) (α - β) := by
    have hs : 0 < Real.sinh (2 * lam) := Real.sinh_pos_iff.mpr (by linarith)
    have hc : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by linarith)
    have hda : 0 < Real.cosh (2 * lam) - Real.cos (α - β) := by linarith [Real.cos_le_one (α - β)]
    have hdb : 0 < Real.cosh (2 * lam) - Real.cos (-α - β) := by linarith [Real.cos_le_one (-α - β)]
    exact (div_le_div_iff₀ hdb hda).2 (mul_le_mul_of_nonneg_left (by linarith) hs.le)
  have hout : HasDerivAt (fun z => discreteBetheG Δ (kMap lam α) z)
      (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β)) (kMap lam β) := by
    rw [deriv_discreteBetheG_right hΔ]
    exact ((analyticAt_theta_right hΔ _ _).differentiableAt.hasDerivAt).sub
      ((analyticAt_theta_right hΔ _ _).differentiableAt.hasDerivAt)
  have hcoeff := (hout.comp β (hasDerivAt_kMap hlam β)).unique (hasDerivAt_discreteBetheG_kMap hΔ α β)
  have hpos : 0 < Xi lam β := Xi_pos hlam β
  dsimp only [x, y] at hkx hky
  rw [← hkx, ← hky]; dsimp only [lam] at hcoeff hXi_le; nlinarith

/-! ### Coordinate residual and compactified inverse-parameter residual -/

private noncomputable def discreteCoordinateResidual (Δ : ℝ) (N n : ℕ) (q : Fin (n / 2) → ℝ) : Fin (n / 2) → ℝ :=
  fun i => discreteBetheResidual Δ N n (discreteSymLift n q) (discreteHalfIndex n i)

private theorem discreteCoordinateResidual_zero_iff {Δ : ℝ} {N n : ℕ} (hN : 0 < N) (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidual Δ N n q = 0 ↔ DiscreteBetheEquation Δ N n (discreteSymLift n q) := by
  have hsym := discreteSymLift_mem n q
  have hres : discreteBetheResidual Δ N n (discreteSymLift n q) ∈ R_n_sym n :=
    (R_n_sym n).sub_mem hsym (discreteBetheMap_mem_R_n_sym Δ N n _ hsym)
  refine ⟨fun h => (discreteBetheMap_fixed_iff_equation hN _).1
      (sub_eq_zero.mp (discreteSym_ext hres (R_n_sym n).zero_mem (congrFun h))).symm, fun h => ?_⟩
  funext i
  change discreteSymLift n q _ - discreteBetheMap Δ N n (discreteSymLift n q) _ = 0
  rw [(discreteBetheMap_fixed_iff_equation hN _).2 h, sub_self]

private theorem analyticAt_discreteCoordinateResidual {Δ : ℝ} (hΔ : Δ < -1) (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteCoordinateResidual z.1 N n z.2) (Δ, q) := by
  have hlift : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteSymLift n z.2) (Δ, q) :=
    (discreteSymLift n).toContinuousLinearMap.analyticAt _ |>.comp analyticAt_snd
  have hcoord (j : Fin n) : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteSymLift n z.2 j) (Δ, q) :=
    (((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).analyticAt _).comp hlift
  refine AnalyticAt.pi fun i => ?_
  have hsum := Finset.analyticAt_fun_sum Finset.univ fun j _ =>
    AnalyticAt.comp (g := fun w : ℝ × ℝ × ℝ => theta w.1 w.2.1 w.2.2)
      (f := fun z : ℝ × (Fin (n / 2) → ℝ) => (z.1, discreteSymLift n z.2 (discreteHalfIndex n i), discreteSymLift n z.2 j))
      (analyticAt_theta hΔ _ _) (analyticAt_fst.prod ((hcoord _).prod (hcoord j)))
  change AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
    discreteSymLift n z.2 (discreteHalfIndex n i) -
      (2 * Real.pi * discreteBetheIndex n (discreteHalfIndex n i) / (N : ℝ) -
        (∑ j : Fin n, theta z.1 (discreteSymLift n z.2 (discreteHalfIndex n i)) (discreteSymLift n z.2 j)) / (N : ℝ))) (Δ, q)
  simp only [div_eq_mul_inv]
  exact (hcoord _).sub (analyticAt_const.sub (hsum.mul analyticAt_const))

private theorem discreteCoordinateResidual_stateDerivative {Δ : ℝ} (hΔ : Δ < -1) (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteCoordinateResidual z.1 N n z.2) (Δ, q)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
      (Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q))).toContinuousLinearMap := by
  let F := fun z : ℝ × (Fin (n / 2) → ℝ) => discreteCoordinateResidual z.1 N n z.2
  let D := (fderiv ℝ F (Δ, q)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ))
  have hlin : D.toLinearMap = Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q)) := by
    refine (Pi.basisFun ℝ (Fin (n / 2))).ext fun k => funext fun i => ?_
    simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply]
    let e : Fin (n / 2) → ℝ := Pi.single k 1
    have hq : HasDerivAt (fun t : ℝ => q + t • e) e 0 := by
      convert (hasDerivAt_const (0 : ℝ) q).add ((hasDerivAt_id (0 : ℝ)).smul_const e) using 1
      all_goals first | rfl | simp only [zero_add, one_smul]
    have hF0 : HasFDerivAt F (fderiv ℝ F (Δ, q)) (Δ, q + (0 : ℝ) • e) := by
      simpa only [zero_smul, add_zero] using (analyticAt_discreteCoordinateResidual hΔ N n q).differentiableAt.hasFDerivAt
    have hscalar := ((ContinuousLinearMap.proj i : (Fin (n / 2) → ℝ) →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt 0
      (hF0.comp_hasDerivAt 0 ((hasDerivAt_const (0 : ℝ) Δ).prodMk hq))
    have heq : (fun t : ℝ => F (Δ, q + t • e) i) =
        fun t => discreteBetheResidual Δ N n (fun j => discreteSymLift n q j + t * discreteSymBasis n k j) (discreteHalfIndex n i) := by
      funext t; unfold F discreteCoordinateResidual; congr 2
      simp only [map_add, map_smul, e, discreteSymLift_single]; rfl
    change HasDerivAt (fun t => F (Δ, q + t • e) i) (D e i) 0 at hscalar
    rw [heq] at hscalar
    exact hscalar.unique (hasDerivAt_discreteBetheResidual_basis hΔ (discreteSymLift n q) i k)
  ext q' i; exact congrFun (LinearMap.congr_fun hlin q') i

private noncomputable def discreteCoordinateResidualInv (ε : ℝ) (N n : ℕ) (q : Fin (n / 2) → ℝ) : Fin (n / 2) → ℝ :=
  fun i => q i - discreteBetheMapInv ε N n (discreteSymLift n q) (discreteHalfIndex n i)

private theorem analyticAt_discreteCoordinateResidualInv {ε : ℝ} (hε : |ε| < 1) (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteCoordinateResidualInv z.1 N n z.2) (ε, q) := by
  have hlift : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteSymLift n z.2) (ε, q) :=
    (discreteSymLift n).toContinuousLinearMap.analyticAt _ |>.comp analyticAt_snd
  have hm := AnalyticAt.comp (g := fun w : ℝ × (Fin n → ℝ) => discreteBetheMapInv w.1 N n w.2)
    (f := fun z : ℝ × (Fin (n / 2) → ℝ) => (z.1, discreteSymLift n z.2))
    (analyticAt_discreteBetheMapInv hε N n _) (analyticAt_fst.prod hlift)
  exact AnalyticAt.pi fun i =>
    (((ContinuousLinearMap.proj i : (Fin (n / 2) → ℝ) →L[ℝ] ℝ).analyticAt _).comp analyticAt_snd).sub
      (((ContinuousLinearMap.proj (discreteHalfIndex n i) : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt _).comp hm)

private theorem stateDerivative_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × E → E} {t : ℝ} {q : E} (hf : DifferentiableAt ℝ F (t, q)) :
    (fderiv ℝ F (t, q)).comp (ContinuousLinearMap.inr ℝ ℝ E) = fderiv ℝ (fun v => F (t, v)) q :=
  (hf.hasFDerivAt.comp q (hasFDerivAt_prodMk_right t q)).fderiv.symm

private theorem discreteCoordinateResidualInv_eq {Δ : ℝ} (hΔ : Δ < -1) (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidualInv (1 / Δ) N n q = discreteCoordinateResidual Δ N n q := by
  funext i; simp only [discreteCoordinateResidualInv, discreteCoordinateResidual,
    discreteBetheResidual, discreteSymLift_half, discreteBetheMap_eq_inv hΔ]

private theorem discreteCoordinateResidualInv_zero (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidualInv 0 N n q = fun i =>
      (1 - (n : ℝ) / N) * q i - 2 * Real.pi * discreteBetheIndex n (discreteHalfIndex n i) / N := by
  have hsum := sum_eq_zero_of_mem_R_n_sym (discreteSymLift_mem n q)
  funext i; simp only [discreteCoordinateResidualInv, discreteBetheMapInv, thetaInv_zero,
    Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, discreteSymLift_half]; ring

/-! ### Diagonal and off-diagonal dominance of `ATilde` -/

private theorem discreteHalf_gap_le_of_cyclic_mesh {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) {d : ℝ}
    (hmesh : ∀ j : Fin (n + 1), rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤ d)
    (j : Fin (n / 2)) : p (discreteHalfNextIndex n j) - p (discreteHalfIndex n j) ≤ d := by
  let cell : Fin (n + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have ha : rootPartitionPoint n p hn cell.castSucc = p (discreteHalfIndex n j) := by
    convert rootPartitionPoint_root p hn (discreteHalfIndex n j) using 2
    exact Fin.ext (by simp [cell, discreteHalfIndex])
  have hb : rootPartitionPoint n p hn cell.succ = p (discreteHalfNextIndex n j) := by
    convert rootPartitionPoint_root p hn (discreteHalfNextIndex n j) using 2
    exact Fin.ext (by simp [cell, discreteHalfNextIndex])
  simpa only [ha, hb] using hmesh cell

private theorem exists_uniform_Bethe_matrix_nonsingular {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N →
      2 * (k + 1) ≤ N → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      (discreteBetheMatrixA Δ N (k + 1) p).det ≠ 0 := by
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ₀
  obtain ⟨Bθ, hBθ, hbound⟩ := exists_uniform_d1Theta_bounds hΔ₀
  obtain ⟨BG, hBG, hboundsG⟩ := exists_uniform_discreteBetheG_deriv_bounds hΔ₀
  let Cdiag := 2 * Real.pi * L + 2 * Bθ
  let Crow := BG * (2 * Real.pi + 3)
  let b₀ := 4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)))
  have hb₀ : b₀ < 2 * Real.pi :=
    (discreteBetheG_endpoint_bound hΔ₀ le_rfl (⟨le_rfl, by linarith [Real.pi_pos]⟩ : -Real.pi ∈ Icc (-Real.pi) 0)).2
  let E := Cdiag * (D ^ 2 + D) + Crow * D
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max 0 (E / (2 * Real.pi - b₀)))
  have hposNat : 0 < N₀ := by exact_mod_cast (le_max_left 0 _ |>.trans_lt hN₀)
  refine ⟨N₀, hposNat, fun Δ hΔ N k hlarge hs p hp hBE hmesh => ?_⟩
  have hvalid := lt_of_le_of_lt hΔ hΔ₀
  have hN : 0 < N := lt_of_lt_of_le hposNat hlarge
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hE : E / (N : ℝ) < 2 * Real.pi - b₀ := by
    rw [div_lt_iff₀ hNc]
    have ht : E / (2 * Real.pi - b₀) < (N : ℝ) := ((le_max_right _ _).trans_lt hN₀).trans_le (by exact_mod_cast hlarge)
    nlinarith [(div_lt_iff₀ (sub_pos.mpr hb₀)).mp ht]
  have hdom (i : Fin ((k + 1) / 2)) :
      ∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N (k + 1) p i j| <
        |discreteBetheMatrixATilde Δ N (k + 1) p i i| := by
    let n := k + 1
    have hn2 : 2 ≤ n := by have := i.isLt; dsimp [n]; omega
    have hhalf_mesh := discreteHalf_gap_le_of_cyclic_mesh (by omega : 0 < n) p hmesh
    -- 1. Diagonal estimate
    have hd_est : |discreteBetheMatrixATilde Δ N n p i i - 2 * Real.pi| ≤ Cdiag * (D ^ 2 + D) / (N : ℝ) := by
      let a := p (discreteHalfIndex n i); let b := p (discreteHalfNextIndex n i); let dg := b - a
      have hlt : discreteHalfIndex n i < discreteHalfNextIndex n i := show i.val < i.val + 1 by omega
      have hdg : 0 < dg := sub_pos.mpr (hp.2.1 hlt)
      have hdgm : dg ≤ D / (N : ℝ) := hhalf_mesh i
      have hcontC : Continuous (betheCountingFunction Δ N n p) :=
        continuous_iff_continuousAt.2 fun x => (hasDerivAt_betheCountingFunction hvalid N n p x).continuousAt
      obtain ⟨ξ, hξ, hmean⟩ := exists_hasDerivAt_eq_slope (betheCountingFunction Δ N n p)
        (betheCountingDerivative Δ N n p) (hp.2.1 hlt) hcontC.continuousOn
        (fun x _ => hasDerivAt_betheCountingFunction hvalid N n p x)
      rw [betheCountingFunction_root_value hN p hBE, betheCountingFunction_root_value hN p hBE, ← sub_div,
        show discreteBetheIndex n (discreteHalfNextIndex n i) - discreteBetheIndex n (discreteHalfIndex n i) = 1 by
          simp only [discreteBetheIndex, discreteHalfNextIndex, discreteHalfIndex, Nat.cast_add, Nat.cast_one, Fin.val_mk]; ring,
        div_div] at hmean
      have haI := hp.1 (discreteHalfIndex n i); have hbI := hp.1 (discreteHalfNextIndex n i)
      have hlip := hLip Δ hΔ N n hN p hp hs a ⟨by dsimp [a]; linarith [Real.pi_pos], by dsimp [a]; linarith [Real.pi_pos]⟩
        ξ ⟨by linarith [hξ.1, Real.pi_pos], by linarith [hξ.2, Real.pi_pos]⟩
      have hfd : |betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ| ≤ L * dg :=
        hlip.trans (mul_le_mul_of_nonneg_left (by rw [abs_of_nonpos (by linarith [hξ.1])]; dsimp [dg, a, b]; linarith [hξ.2]) hL.le)
      have hfirst : |2 * Real.pi * (N : ℝ) * dg * (betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ)| ≤
          (2 * Real.pi * L) * D ^ 2 / (N : ℝ) := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        have hm := mul_le_mul_of_nonneg_left hfd (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ) * dg)
        have hsq := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hdg.le (by positivity)).2 hdgm) (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ) * L)
        calc _ ≤ (2 * Real.pi * (N : ℝ) * L) * dg ^ 2 := by nlinarith only [hm]
          _ ≤ (2 * Real.pi * (N : ℝ) * L) * (D / (N : ℝ)) ^ 2 := hsq
          _ = _ := by field_simp
      have hrev := hp.1 (Fin.rev (discreteHalfIndex n i))
      have hba : |thetaPartialFirst Δ a a| ≤ Bθ := ((hbound Δ hΔ).1 a ⟨haI.1.le, haI.2.le⟩ a ⟨haI.1.le, haI.2.le⟩).1
      have hbs : |thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i)))| ≤ Bθ := by
        rw [thetaPartialSecond_eq_neg_d1Theta hvalid, abs_neg]
        exact ((hbound Δ hΔ).1 _ ⟨hrev.1.le, hrev.2.le⟩ a ⟨haI.1.le, haI.2.le⟩).1
      have hsecond : |dg * (thetaPartialFirst Δ a a + thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i))))| ≤
          (2 * Bθ) * D / (N : ℝ) := by
        rw [abs_mul, abs_of_pos hdg]
        calc _ ≤ dg * (Bθ + Bθ) := mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hba hbs)) hdg.le
          _ ≤ (D / (N : ℝ)) * (Bθ + Bθ) := mul_le_mul_of_nonneg_right hdgm (by positivity)
          _ = _ := by ring
      have hdiag_id : discreteBetheMatrixATilde Δ N n p i i - 2 * Real.pi =
          2 * Real.pi * (N : ℝ) * dg * (betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ) -
          dg * (thetaPartialFirst Δ a a + thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i)))) := by
        rw [hmean, discreteBetheMatrixATilde, discreteBetheMatrixB, Matrix.mul_diagonal]
        simp only [discreteBetheMatrixA, ↓reduceIte]
        have hsum_er := Finset.add_sum_erase Finset.univ (fun ell => thetaPartialFirst Δ a (p ell)) (Finset.mem_univ (discreteHalfIndex n i))
        unfold betheCountingDerivative; dsimp only [a, b, dg] at hdg hsum_er ⊢
        rw [← hsum_er]; field_simp [hNc.ne', hdg.ne', Real.pi_ne_zero]; ring
      rw [hdiag_id]
      have htri := abs_add_le
        (2 * Real.pi * (N : ℝ) * dg * (betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ))
        (-(dg * (thetaPartialFirst Δ a a + thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i))))))
      rw [← sub_eq_add_neg, abs_neg] at htri
      refine htri.trans ((add_le_add hfirst hsecond).trans ?_)
      rw [← add_div, div_le_div_iff_of_pos_right hNc]; dsimp [Cdiag]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * Real.pi * L) hD, mul_nonneg hBθ.le (sq_nonneg D)]
    -- 2. Off-diagonal row estimate
    have hr_est : |(∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N n p i j|) -
        (discreteBetheG Δ (p (discreteHalfIndex n i)) 0 - discreteBetheG Δ (p (discreteHalfIndex n i)) (-Real.pi))| ≤
        Crow * D / (N : ℝ) := by
      let d := D / (N : ℝ)
      have hd : 0 ≤ d := div_nonneg hD hNc.le
      let q : Fin (n / 2 + 1) → ℝ := fun j => p ⟨j.val, by omega⟩
      let f : ℝ → ℝ := discreteBetheG Δ (p (discreteHalfIndex n i))
      let g : ℝ → ℝ := deriv f
      have hq : StrictMono q := fun j₁ j₂ hj => hp.2.1 hj
      have hbox (j) : q j ∈ Icc (-Real.pi) Real.pi := ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
      have hxI : p (discreteHalfIndex n i) ∈ Icc (-Real.pi) Real.pi := ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
      have hdiff (y : ℝ) : DifferentiableAt ℝ f y :=
        (analyticAt_theta_right hvalid _ y).differentiableAt.sub (analyticAt_theta_right hvalid _ y).differentiableAt
      have hg (y : ℝ) (hy : y ∈ Icc (-Real.pi) Real.pi) : |g y| ≤ BG := (hboundsG Δ hΔ).1 _ hxI y hy
      have hqm (j : Fin (n / 2)) : q j.succ - q j.castSucc ≤ d := hhalf_mesh j
      have hquad : |(∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
          (f (q (Fin.last (n / 2))) - f (q 0))| ≤ BG * d * (2 * Real.pi) := by
        have hloc (j : Fin (n / 2)) : |(q j.succ - q j.castSucc) * g (q j.castSucc) - (f (q j.succ) - f (q j.castSucc))| ≤
            BG * d * (q j.succ - q j.castSucc) := by
          have hlt : q j.castSucc < q j.succ := hq (show j.val < j.val + 1 by omega)
          have hsub : Icc (q j.castSucc) (q j.succ) ⊆ Icc (-Real.pi) Real.pi :=
            fun x hx => ⟨(hbox _).1.trans hx.1, hx.2.trans (hbox _).2⟩
          obtain ⟨ξ, hξ, hm⟩ := exists_hasDerivAt_eq_slope f g hlt
            (fun x hx => (hdiff x).continuousAt.continuousWithinAt) (fun x _ => (hdiff x).hasDerivAt)
          have hl := ((hboundsG Δ hΔ).2 _ hxI (q j.castSucc) (hbox _) ξ (hsub ⟨hξ.1.le, hξ.2.le⟩)).trans
            ((mul_le_mul_of_nonneg_left (by rw [abs_of_neg (sub_neg.mpr hξ.1)]; linarith [hξ.2]) hBG.le).trans
              (mul_le_mul_of_nonneg_left (hqm j) hBG.le))
          rw [← show (q j.succ - q j.castSucc) * g ξ = f (q j.succ) - f (q j.castSucc) by
              rw [hm]; exact mul_div_cancel₀ _ (sub_ne_zero.mpr hlt.ne'),
            ← mul_sub, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
          calc _ ≤ (q j.succ - q j.castSucc) * (BG * d) := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hlt.le)
            _ = _ := by ring
        have htel {m : ℕ} (u : Fin (m + 1) → ℝ) : (∑ j : Fin m, (u j.succ - u j.castSucc)) = u (Fin.last m) - u 0 := by
          rw [Finset.sum_sub_distrib]; linarith [Fin.sum_univ_succ u, Fin.sum_univ_castSucc u]
        rw [← htel (fun j => f (q j)), ← Finset.sum_sub_distrib]
        calc _ ≤ ∑ j : Fin (n / 2), BG * d * (q j.succ - q j.castSucc) :=
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hloc j)
          _ = BG * d * (q (Fin.last (n / 2)) - q 0) := by rw [← Finset.mul_sum, htel q]
          _ ≤ BG * d * (2 * Real.pi) := mul_le_mul_of_nonneg_left (by linarith [(hbox (Fin.last (n / 2))).2, (hbox 0).1]) (mul_nonneg hBG.le hd)
      have hfLip {y z : ℝ} (hy : y ∈ Icc (-Real.pi) Real.pi) (hz : z ∈ Icc (-Real.pi) Real.pi) : |f y - f z| ≤ BG * |y - z| := by
        simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hdiff t)
          (fun t ht => by simpa only [Real.norm_eq_abs] using hg t ht) (convex_Icc _ _) hz hy
      have hend : 0 ≤ q (Fin.last (n / 2)) ∧ q (Fin.last (n / 2)) ≤ d := by
        let e : Fin n := ⟨n / 2, by omega⟩
        have he := hp.2.1.monotone (show Fin.rev e ≤ e by change n - (n / 2 + 1) ≤ n / 2; omega)
        rw [hp.2.2 e] at he
        let j0 : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩
        have hneg := discreteS_n_half_coord_neg hp j0
        have hm := hhalf_mesh j0
        have hnext : discreteHalfNextIndex n j0 = e := Fin.ext (show n / 2 - 1 + 1 = n / 2 by omega)
        rw [hnext] at hm
        exact ⟨by dsimp [q, e] at *; linarith, by dsimp [q, e] at *; linarith⟩
      have hrightErr : |f (q (Fin.last (n / 2))) - f 0| ≤ BG * d :=
        (hfLip (hbox _) ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩).trans
          (mul_le_mul_of_nonneg_left (by rw [sub_zero, abs_of_nonneg hend.1]; exact hend.2) hBG.le)
      have hleftErr : |f (q 0) - f (-Real.pi)| ≤ BG * d :=
        (hfLip (hbox 0) ⟨le_rfl, by linarith [Real.pi_pos]⟩).trans
          (mul_le_mul_of_nonneg_left (by
            rw [sub_neg_eq_add, abs_of_nonneg (by linarith [(hbox 0).1])]
            exact (root_mesh_consequences hp hmesh).1) hBG.le)
      have hdiagErr : |(q i.succ - q i.castSucc) * g (q i.castSucc)| ≤ BG * d := by
        have hge : 0 ≤ q i.succ - q i.castSucc := sub_nonneg.mpr (hq.monotone (Fin.castSucc_le_succ i))
        rw [abs_mul, abs_of_nonneg hge]
        calc _ ≤ (q i.succ - q i.castSucc) * BG := mul_le_mul_of_nonneg_left (hg _ (hbox _)) hge
          _ ≤ d * BG := mul_le_mul_of_nonneg_right (hqm i) hBG.le
          _ = BG * d := mul_comm _ _
      have hrow_eq : (∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N n p i j|) =
          (∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) - (q i.succ - q i.castSucc) * g (q i.castSucc) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        rw [abs_of_nonneg (discreteBetheMatrixATilde_offdiag_nonneg hvalid hN p hp i j hij),
          discreteBetheMatrixATilde_offdiag_eq hvalid p hp.2.2 hN i j hij]; rfl
      rw [hrow_eq]
      have h1 := abs_add_le ((∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) - (f (q (Fin.last (n / 2))) - f (q 0)))
        ((f (q (Fin.last (n / 2))) - f 0) - (f (q 0) - f (-Real.pi)) - (q i.succ - q i.castSucc) * g (q i.castSucc))
      have h2 := abs_add_le ((f (q (Fin.last (n / 2))) - f 0) - (f (q 0) - f (-Real.pi))) (-((q i.succ - q i.castSucc) * g (q i.castSucc)))
      have h3 := abs_add_le (f (q (Fin.last (n / 2))) - f 0) (-(f (q 0) - f (-Real.pi)))
      simp only [abs_neg] at h2 h3
      have hid : (∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) -
          (q i.succ - q i.castSucc) * g (q i.castSucc) - (f 0 - f (-Real.pi)) =
          ((∑ j : Fin (n / 2), (q j.succ - q j.castSucc) * g (q j.castSucc)) - (f (q (Fin.last (n / 2))) - f (q 0))) +
          ((f (q (Fin.last (n / 2))) - f 0) - (f (q 0) - f (-Real.pi)) - (q i.succ - q i.castSucc) * g (q i.castSucc)) := by ring
      change |_ - (f 0 - f (-Real.pi))| ≤ _; rw [hid]
      have hcEq : BG * d * (2 * Real.pi) + BG * d + BG * d + BG * d = Crow * D / (N : ℝ) := by dsimp [Crow, d]; ring
      simp only [sub_eq_add_neg, add_assoc] at h1 h2 h3 hquad hrightErr hleftErr hdiagErr hcEq ⊢
      linarith
    have hG := (discreteBetheG_endpoint_bound hΔ₀ hΔ ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp i).le⟩).1
    have hdlo := (abs_le.mp hd_est).1
    have hrup := (abs_le.mp hr_est).2
    have habs := le_abs_self (discreteBetheMatrixATilde Δ N (k + 1) p i i)
    dsimp only [E] at hE; rw [add_div] at hE; change _ ≤ b₀ at hG
    linarith only [hE, hdlo, hrup, hG, habs]
  have hdet : (discreteBetheMatrixATilde Δ N (k + 1) p).det ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag fun i => by simpa only [Real.norm_eq_abs] using hdom i
  rw [discreteBetheMatrixATilde, Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).1

/-! ### Admissible gap region, strict gap bootstrap, and base coordinates -/

private def betheGapRegion (k : ℕ) (ell u : ℝ) : Set (Fin ((k + 1) / 2) → ℝ) :=
  {q | ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q) (by omega) j.succ -
    rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q) (by omega) j.castSucc ∈ Icc ell u}

private theorem continuous_rootPartitionPoint (k : ℕ) (j : Fin (k + 3)) :
    Continuous (fun p : Fin (k + 1) → ℝ => rootPartitionPoint (k + 1) p (by omega) j) := by
  unfold rootPartitionPoint; split_ifs <;> fun_prop

private theorem betheGapRegion_mem_S_n {k : ℕ} {ell u : ℝ} (hell : 0 < ell)
    {q : Fin ((k + 1) / 2) → ℝ} (hq : q ∈ betheGapRegion k ell u) :
    discreteSymLift (k + 1) q ∈ S_n (k + 1) := by
  let p := discreteSymLift (k + 1) q
  have hsym := discreteSymLift_mem (k + 1) q
  have hgaps (j : Fin (k + 2)) : 0 < rootPartitionPoint (k + 1) p (by omega) j.succ -
      rootPartitionPoint (k + 1) p (by omega) j.castSucc := hell.trans_le (hq j).1
  have hmono : StrictMono p := Fin.strictMono_iff_lt_succ.mpr fun j => by
    let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
    have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
      convert rootPartitionPoint_root p (by omega) j.castSucc using 2
      exact Fin.ext (by simp [cell])
    have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
      convert rootPartitionPoint_root p (by omega) j.succ using 2
      exact Fin.ext (by simp [cell])
    have h := hgaps cell; rw [ha, hb] at h; exact sub_pos.mp h
  have hfirst := hgaps 0
  have ha : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc = p (Fin.last k) - 2 * Real.pi := by
    rw [show (0 : Fin (k + 2)).castSucc = ⟨0, by omega⟩ from Fin.ext (by simp), rootPartitionPoint_zero]; rfl
  have hb : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := by
    convert rootPartitionPoint_root p (by omega) (0 : Fin (k + 1)) using 2; exact Fin.ext (by simp)
  rw [ha, hb] at hfirst
  have hsym0 : p (Fin.last k) = -p 0 := by simpa using hsym 0
  refine ⟨fun j => ⟨(by linarith : -Real.pi < p 0).trans_le (hmono.monotone (Fin.zero_le j)),
    (hmono.monotone (Fin.le_last j)).trans_lt (by linarith : p (Fin.last k) < Real.pi)⟩, hmono, hsym⟩

private theorem isCompact_betheGapRegion (k : ℕ) {ell u : ℝ} (hell : 0 < ell) :
    IsCompact (betheGapRegion k ell u) := by
  have hclosed : IsClosed (betheGapRegion k ell u) := by
    simp only [betheGapRegion, ofPred_forall]
    refine isClosed_iInter fun j => ?_
    have hc (i : Fin (k + 3)) : Continuous (fun q : Fin ((k + 1) / 2) → ℝ =>
        rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q) (by omega) i) :=
      (continuous_rootPartitionPoint k i).comp (discreteSymLift (k + 1)).continuous_of_finiteDimensional
    exact isClosed_Icc.preimage ((hc j.succ).sub (hc j.castSucc))
  refine (isCompact_univ_pi fun _ : Fin ((k + 1) / 2) => isCompact_Icc (a := -Real.pi) (b := Real.pi)).of_isClosed_subset
    hclosed fun q hq j _ => ?_
  have hj := (betheGapRegion_mem_S_n hell hq).1 (discreteHalfIndex (k + 1) j)
  simpa only [Set.mem_Icc, discreteSymLift_half] using And.intro hj.1.le hj.2.le

private theorem mem_interior_betheGapRegion {k : ℕ} {ell u : ℝ} {q : Fin ((k + 1) / 2) → ℝ}
    (hq : ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q) (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q) (by omega) j.castSucc ∈ Ioo ell u) :
    q ∈ interior (betheGapRegion k ell u) := by
  rw [mem_interior_iff_mem_nhds]
  have hnear : ∀ j : Fin (k + 2), ∀ᶠ v in 𝓝 q,
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) v) (by omega) j.succ -
        rootPartitionPoint (k + 1) (discreteSymLift (k + 1) v) (by omega) j.castSucc ∈ Ioo ell u := fun j => by
    have hc (i : Fin (k + 3)) := (continuous_rootPartitionPoint k i).comp
      (discreteSymLift (k + 1)).continuous_of_finiteDimensional
    exact ((hc j.succ).sub (hc j.castSucc)).continuousAt.eventually (isOpen_Ioo.mem_nhds (hq j))
  exact (eventually_all.mpr hnear).mono fun _ hv j => ⟨(hv j).1.le, (hv j).2.le⟩

private theorem one_le_rootGapMultiplicity {N n : ℕ} (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    1 ≤ rootGapMultiplicity N n hs j := by
  unfold rootGapMultiplicity; split_ifs
  · exact_mod_cast (show 1 ≤ N + 1 - 2 * n by omega)
  · exact le_rfl

private theorem exists_uniform_strict_gap_bootstrap (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ c D K : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      8 * Real.pi * (2 * r + 1 : ℝ) < D ∧ 0 < K ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀), ∀ (N k : ℕ),
      N₀ ≤ N → N = 2 * ((k + 1) + r) →
      ∀ (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N),
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x)
        (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) p hp (by omega) hs) ≤ K / N ∧
      ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ∈ Ioo (c / (N : ℝ)) (D / (N : ℝ)) := by
  obtain ⟨mρ, hmρ, hρ⟩ := rho_uniform_lower_bound hΔ₀
  obtain ⟨mXi, hmXi, hXi⟩ := exists_uniform_Xi_lower_bound hΔ₀
  obtain ⟨M, hM⟩ := rho_uniform_upper_bound hΔ₀
  have hMpos : 0 < M := (rho_pos hΔ₀ 0).trans_le (hM Δ₀ le_rfl 0)
  let B := M + 1 / mXi
  have hB : 0 < B := by dsimp [B]; positivity
  let c := min Real.pi (1 / (2 * B))
  have hc : 0 < c := lt_min Real.pi_pos (by positivity)
  let D := 4 * (2 * r + 1 : ℝ) / mρ + 8 * Real.pi * (2 * r + 1 : ℝ)
  have hDlarge : 8 * Real.pi * (2 * r + 1 : ℝ) < D := by
    dsimp [D]; linarith [show 0 < 4 * (2 * r + 1 : ℝ) / mρ by positivity]
  have hD : 0 < D := lt_trans (by positivity) hDlarge
  obtain ⟨K, hK, hestimate⟩ := exists_uniform_density_bound_of_Bethe_mesh r hΔ₀ D hD.le
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max K (2 * K / (mρ * mXi)))
  have hN₀nat : 0 < N₀ := by exact_mod_cast (hK.trans ((le_max_left _ _).trans_lt hN₀))
  refine ⟨c, D, K, hc, min_le_left _ _, hDlarge, hK, N₀, hN₀nat,
    fun Δ hΔ N k hlarge hcount p hp hs hBE hmesh => ?_⟩
  let hb := rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) p hp (by omega) hs
  have herr := hestimate Δ hΔ N k hcount p hp hs hBE hmesh
  have hNc : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hN₀nat hlarge)
  have hcast : (N₀ : ℝ) ≤ N := by exact_mod_cast hlarge
  have hKN : K < (N : ℝ) := ((le_max_left _ _).trans_lt hN₀).trans_le hcast
  have hpt (x : ℝ) (hx : x ∈ Icc (-Real.pi) Real.pi) :
      |rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x| ≤ (K / (N : ℝ)) / mXi :=
    densityNorm_x_pointwise_le hΔ₀ hΔ _ hb (K / N) mXi hmXi (hXi Δ hΔ) herr hx
  refine ⟨herr, fun j => ⟨?_, ?_⟩⟩
  · have hgap_pos := rootPartition_gap_pos hp (by omega) j
    obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp (by omega) j
    have hρp : rootStepDensity N (k + 1) p hp (by omega) hs x ≤ B := by
      have h1 := (abs_le.mp (hpt x hx)).2
      have h2 : (K / (N : ℝ)) / mXi ≤ 1 / mXi := div_le_div_of_nonneg_right ((div_le_one hNc).2 hKN.le) hmXi.le
      dsimp [B]; linarith [hM Δ hΔ x]
    rw [rootStepDensity_on_cell hp (by omega) hs j hcell] at hρp
    have hlo : 1 / ((N : ℝ) * B) ≤ rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc := by
      rw [div_le_iff₀ (mul_pos hNc hB)]
      exact (one_le_rootGapMultiplicity hs j).trans
        (by have := (div_le_iff₀ (mul_pos hNc hgap_pos)).mp hρp; linarith)
    have hclt : c < 1 / B := (min_le_right _ _).trans_lt (one_div_lt_one_div_of_lt hB (by linarith))
    calc c / (N : ℝ) < (1 / B) / (N : ℝ) := div_lt_div_of_pos_right hclt hNc
      _ = 1 / ((N : ℝ) * B) := by rw [div_div, mul_comm B]
      _ ≤ _ := hlo
  · have hsmall : (K / (N : ℝ)) / mXi ≤ mρ / 2 := by
      rw [div_div, div_le_iff₀ (mul_pos hNc hmXi)]
      have ht : 2 * K / (mρ * mXi) < (N : ℝ) := ((le_max_right _ _).trans_lt hN₀).trans_le hcast
      nlinarith [(div_lt_iff₀ (mul_pos hmρ hmXi)).mp ht]
    have hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, mρ / 2 ≤ rootStepDensity N (k + 1) p hp (by omega) hs x := fun x hx => by
      have hxerr := hpt x hx; rw [abs_sub_comm] at hxerr
      linarith [(abs_le.mp hxerr).2, hρ Δ hΔ x hx]
    have hu := rootPartition_gap_le_of_density_lower hp (by omega) hs hmρ hlower j
    have hmass := rootGapMultiplicity_le_offset hs hcount j
    have hDlt : 2 * (2 * r + 1 : ℝ) / mρ < D := by
      have h1 : 0 < (2 * r + 1 : ℝ) / mρ := by positivity
      have h2 : 0 < 8 * Real.pi * (2 * r + 1 : ℝ) := by positivity
      dsimp [D]; rw [show 4 * (2 * r + 1 : ℝ) / mρ = 4 * ((2 * r + 1 : ℝ) / mρ) by ring,
        show 2 * (2 * r + 1 : ℝ) / mρ = 2 * ((2 * r + 1 : ℝ) / mρ) by ring]; linarith
    calc _ ≤ 2 * rootGapMultiplicity N (k + 1) hs j / (mρ * (N : ℝ)) := hu
      _ ≤ 2 * (2 * r + 1 : ℝ) / (mρ * (N : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num)) (by positivity)
      _ = (2 * (2 * r + 1 : ℝ) / mρ) / (N : ℝ) := by rw [div_div]
      _ < D / (N : ℝ) := div_lt_div_of_pos_right hDlt hNc

private noncomputable def discreteBaseCoordinates (N n : ℕ) : Fin (n / 2) → ℝ :=
  fun i => discreteBaseSolution N n (discreteHalfIndex n i)

private theorem discreteCoordinateResidualInv_base_zero {N n : ℕ} (hN : 0 < N) (hs : 2 * n ≤ N) :
    discreteCoordinateResidualInv 0 N n (discreteBaseCoordinates N n) = 0 := by
  have hp := discreteBaseSolution_mem_S_n hN hs
  have hBE := discreteBaseSolution_solves_at_infinity hN hs
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext i
  have heq := hBE (discreteHalfIndex n i)
  have hlift : discreteSymLift n (discreteBaseCoordinates N n) = discreteBaseSolution N n :=
    discreteSymLift_coordinates _ hp.2.2
  simp only [discreteCoordinateResidualInv, discreteBetheMapInv, thetaInv_zero, hlift]
  change discreteBaseSolution N n (discreteHalfIndex n i) - _ = 0
  field_simp [hNc]; nlinarith only [heq]

private theorem discreteCoordinateResidualInv_base_unique {N n : ℕ} (hN : 0 < N) (hs : 2 * n ≤ N) :
    ∃! q : Fin (n / 2) → ℝ, discreteCoordinateResidualInv 0 N n q = 0 := by
  refine ⟨discreteBaseCoordinates N n, discreteCoordinateResidualInv_base_zero hN hs, fun q hq => ?_⟩
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : (n : ℝ) < N := by exact_mod_cast (show n < N by omega)
  have ha : 0 < 1 - (n : ℝ) / N := sub_pos.mpr ((div_lt_one hNc).2 hnN)
  have hb := discreteCoordinateResidualInv_base_zero hN hs
  dsimp only at hq; rw [discreteCoordinateResidualInv_zero] at hq hb
  funext i
  have hqi := congrFun hq i; have hbi := congrFun hb i
  dsimp only [Pi.zero_apply] at hqi hbi; nlinarith only [hqi, hbi, ha]

private theorem discreteBaseCoordinates_strict_gaps {N k r : ℕ} (hN : 0 < N)
    (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ((k + 1) + r))
    {c D : ℝ} (hc : c ≤ Real.pi) (hD : 8 * Real.pi * (2 * r + 1 : ℝ) < D) (j : Fin (k + 2)) :
    rootPartitionPoint (k + 1) (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1))) (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1))) (by omega) j.castSucc ∈
      Ioo (c / (N : ℝ)) (D / (N : ℝ)) := by
  have hp := discreteBaseSolution_mem_S_n hN hs
  have hlift : discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)) = discreteBaseSolution N (k + 1) :=
    discreteSymLift_coordinates _ hp.2.2
  rw [hlift]
  have hden : ((N - (k + 1) : ℕ) : ℝ) = (N : ℝ) - (k + 1 : ℕ) := Nat.cast_sub (by omega)
  have hpos : 0 < (N : ℝ) - (k + 1 : ℕ) := sub_pos.mpr (by exact_mod_cast (show k + 1 < N by omega))
  have hmass : ((N + 1 - 2 * (k + 1) : ℕ) : ℝ) = (N : ℝ) + 1 - 2 * ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega : 2 * (k + 1) ≤ N + 1)]; push_cast; ring
  have hgap_eq : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.castSucc =
      2 * Real.pi * rootGapMultiplicity N (k + 1) hs j / ((N : ℝ) - (k + 1 : ℕ)) := by
    by_cases hj0 : j.val = 0
    · have hj : j = 0 := Fin.ext hj0; subst hj
      have ha : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) (0 : Fin (k + 2)).castSucc =
          discreteBaseSolution N (k + 1) (Fin.last k) - 2 * Real.pi := by
        rw [show (0 : Fin (k + 2)).castSucc = ⟨0, by omega⟩ from Fin.ext (by simp), rootPartitionPoint_zero]; rfl
      have hb : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) (0 : Fin (k + 2)).succ =
          discreteBaseSolution N (k + 1) 0 := by
        convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) (0 : Fin (k + 1)) using 2; exact Fin.ext (by simp)
      rw [ha, hb]; simp only [rootGapMultiplicity, Fin.val_zero, true_or, ↓reduceIte,
        discreteBaseSolution, discreteBetheIndex, Fin.val_last, hden, hmass]
      field_simp [hpos.ne']; push_cast; ring
    · by_cases hjlast : j.val = k + 1
      · have hj : j = Fin.last (k + 1) := Fin.ext hjlast; subst hj
        have ha : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) (Fin.last (k + 1)).castSucc =
            discreteBaseSolution N (k + 1) (Fin.last k) := by
          convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) (Fin.last k) using 2; exact Fin.ext (by simp)
        have hb : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) (Fin.last (k + 1)).succ =
            discreteBaseSolution N (k + 1) 0 + 2 * Real.pi := by
          rw [show (Fin.last (k + 1)).succ = ⟨k + 1 + 1, by omega⟩ from Fin.ext (by simp), rootPartitionPoint_end]; rfl
        rw [ha, hb]; simp only [rootGapMultiplicity, Fin.val_last, or_true, ↓reduceIte,
          discreteBaseSolution, discreteBetheIndex, Fin.val_zero, hden, hmass]
        field_simp [hpos.ne']; push_cast; ring
      · let lo : Fin (k + 1) := ⟨j.val - 1, by omega⟩; let hi : Fin (k + 1) := ⟨j.val, by omega⟩
        have ha : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.castSucc =
            discreteBaseSolution N (k + 1) lo := by
          convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) lo using 2
          exact Fin.ext (by simp [lo]; omega)
        have hb : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.succ =
            discreteBaseSolution N (k + 1) hi := by
          convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) hi using 2
          exact Fin.ext (by simp [hi])
        rw [ha, hb]; simp only [rootGapMultiplicity, ite_eq_right (not_or.mpr ⟨hj0, hjlast⟩),
          discreteBaseSolution, discreteBetheIndex, lo, hi, hden]
        rw [Nat.cast_sub (by omega : 1 ≤ j.val)]; push_cast; ring
  rw [hgap_eq]
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hhalf : (N : ℝ) ≤ 2 * ((N : ℝ) - (k + 1 : ℕ)) := by
    have : 2 * ((k : ℝ) + 1) ≤ N := by exact_mod_cast hs
    push_cast; linarith
  have hdenN : (N : ℝ) - (k + 1 : ℕ) ≤ N := by linarith [(Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ (k + 1 : ℕ))]
  have hm := one_le_rootGapMultiplicity hs j
  have hmcap := rootGapMultiplicity_le_offset hs hcount j
  refine ⟨(div_lt_div_of_pos_right (by linarith [Real.pi_pos] : c < 2 * Real.pi) hNc).trans_le ?_,
    (?_ : _ ≤ 4 * Real.pi * (2 * r + 1 : ℝ) / (N : ℝ)).trans_lt
      (div_lt_div_of_pos_right (by linarith [show 0 < Real.pi * (2 * r + 1 : ℝ) by positivity]) hNc)⟩
  · rw [div_le_div_iff₀ hNc hpos]
    nlinarith [mul_le_mul_of_nonneg_left hdenN (by positivity : 0 ≤ 2 * Real.pi),
      mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ))]
  · rw [div_le_div_iff₀ hpos hNc]
    nlinarith [mul_le_mul_of_nonneg_left hmcap (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ)),
      mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 * Real.pi * (2 * r + 1 : ℝ))]

/-! ### Compact analytic continuation and Theorem 2.3 -/

private theorem exists_analytic_implicit_family_on_open_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × E → E} {C : Set E} (hC : IsCompact C) {a b : ℝ} (hab : a < b)
    (hF : ∀ t ∈ Icc a b, ∀ x ∈ C, AnalyticAt ℝ F (t, x))
    (hregular : ∀ t ∈ Icc a b, ∀ x ∈ C, F (t, x) = 0 →
      x ∈ interior C ∧ ∃ e : E ≃L[ℝ] E, (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) = (e : E →L[ℝ] E))
    (hbase : ∃! x : C, F (b, x.val) = 0) :
    ∃ b' : ℝ, b < b' ∧ ∃ ψ : ℝ → E,
      AnalyticOnNhd ℝ ψ (Ioo a b') ∧ (∀ t ∈ Ioo a b', F (t, ψ t) = 0) ∧
      (∀ t ∈ Icc a b, ψ t ∈ C ∧ F (t, ψ t) = 0) := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  let R (t : Icc a b) (x : C) : Prop := F (t.val, x.val) = 0
  have hclosed : IsClosed {z : (Icc a b) × C | R z.1 z.2} := by
    refine isClosed_eq (continuous_iff_continuousAt.mpr fun z => ?_) continuous_const
    exact ContinuousAt.comp (g := F) (f := fun w : (Icc a b) × C => (w.1.val, w.2.val))
      (hF z.1.val z.1.2 z.2.val z.2.2).continuousAt
      (Continuous.continuousAt (by fun_prop))
  have hlocal (t : Icc a b) (x : C) (hx : R t x) :
      ∃ φ : Icc a b → C, ContinuousAt φ t ∧ φ t = x ∧ (∀ᶠ u in 𝓝 t, R u (φ u)) ∧
        ∃ W : Set ((Icc a b) × C), IsOpen W ∧ (t, x) ∈ W ∧ ∀ u y, (u, y) ∈ W → R u y → y = φ u := by
    obtain ⟨hint, e, he⟩ := hregular t.val t.2 x.val x.2 hx
    obtain ⟨ψ₀, hψbase, hψan, W, V, hWopen, hVopen, hWbase, hVbase, hbranch, huniq⟩ :=
      PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction_with_local_uniqueness
        (hF t.val t.2 x.val x.2) hx e he
    have hsub : ContinuousAt (Subtype.val : Icc a b → ℝ) t := continuous_subtype_val.continuousAt
    have hnearC : ∀ᶠ u : Icc a b in 𝓝 t, ψ₀ u.val ∈ C :=
      hsub.eventually (hψan.continuousAt.eventually (hψbase.symm ▸ mem_interior_iff_mem_nhds.mp hint))
    let φ : Icc a b → C := fun u => if h : ψ₀ u.val ∈ C then ⟨ψ₀ u.val, h⟩ else x
    have hφeq : (fun u : Icc a b => (φ u).val) =ᶠ[𝓝 t] fun u => ψ₀ u.val :=
      hnearC.mono fun u hu => by simp only [φ, dite_eq_left hu]
    refine ⟨φ, tendsto_subtype_rng.mpr ((hψan.continuousAt.comp hsub).congr_of_eventuallyEq hφeq),
      Subtype.ext (by have hCx : ψ₀ t.val ∈ C := hψbase ▸ x.2; simp only [φ, dite_eq_left hCx, hψbase]), ?_,
      (fun z : (Icc a b) × C => (z.1.val, z.2.val)) ⁻¹' W, hWopen.preimage (by fun_prop), hWbase,
      fun u y hy hr => Subtype.ext (by
        have hyψ := huniq u.val y.val hy hr
        have hCy : ψ₀ u.val ∈ C := hyψ ▸ y.2
        simpa only [φ, dite_eq_left hCy] using hyψ)⟩
    filter_upwards [hsub.eventually (hVopen.mem_nhds hVbase), hφeq] with u hu heq
    change F (u.val, (φ u).val) = 0; rw [heq]; exact (hbranch _ hu).2
  have hunique : ∀ t : Icc a b, ∃! x : C, R t x := by
    let U : Set (Icc a b) := {t | ∃! x, R t x}
    have hproj : IsClosed (Prod.fst '' {z : (Icc a b) × C | R z.1 z.2}) := isClosedMap_fst_of_compactSpace _ hclosed
    have hopen : IsOpen U := isOpen_iff_mem_nhds.mpr fun t ⟨x, hx, hu⟩ => by
      obtain ⟨φ, _, _, hφr, W, hWo, hWb, hWu⟩ := hlocal t x hx
      have hBc : IsClosed (Prod.fst '' ({z : (Icc a b) × C | R z.1 z.2} ∩ Wᶜ)) :=
        isClosedMap_fst_of_compactSpace _ (hclosed.inter hWo.isClosed_compl)
      have htB : t ∉ Prod.fst '' ({z : (Icc a b) × C | R z.1 z.2} ∩ Wᶜ) := by
        rintro ⟨⟨u, y⟩, ⟨hy, hnot⟩, rfl⟩; exact hnot (hu y hy ▸ hWb)
      filter_upwards [hBc.isOpen_compl.mem_nhds htB, hφr] with u huB hr
      exact ⟨φ u, hr, fun y hy => hWu u y (by by_contra hn; exact huB ⟨(u, y), ⟨hy, hn⟩, rfl⟩) hy⟩
    have hopenC : IsOpen Uᶜ := isOpen_iff_mem_nhds.mpr fun t ht => by
      by_cases hex : ∃ x, R t x
      · obtain ⟨x, hx⟩ := hex
        have hnu : ∃ y, R t y ∧ y ≠ x := by by_contra h; push Not at h; exact ht ⟨x, hx, h⟩
        obtain ⟨y, hy, hyx⟩ := hnu
        obtain ⟨φ, hφc, hφb, hφr, _⟩ := hlocal t x hx
        obtain ⟨ψ₀, hψc, hψb, hψr, _⟩ := hlocal t y hy
        filter_upwards [hφr, hψr, (hφc.ne_iff_eventually_ne hψc).mp (by rw [hφb, hψb]; exact hyx.symm)] with u h1 h2 hne ⟨z, _, hz⟩
        exact hne ((hz _ h1).trans (hz _ h2).symm)
      · have hnp : t ∉ Prod.fst '' {z : (Icc a b) × C | R z.1 z.2} := by rintro ⟨⟨u, x⟩, hx, rfl⟩; exact hex ⟨x, hx⟩
        filter_upwards [hproj.isOpen_compl.mem_nhds hnp] with u hu ⟨x, hx, _⟩ using hu ⟨(u, x), hx, rfl⟩
    have hU := IsClopen.eq_univ ⟨by simpa using hopenC.isClosed_compl, hopen⟩ ⟨⟨b, hab.le, le_rfl⟩, hbase⟩
    exact fun t => show t ∈ U from hU ▸ mem_univ t
  let q : Icc a b → C := fun t => (hunique t).choose
  have hq (t : Icc a b) : F (t.val, (q t).val) = 0 := (hunique t).choose_spec.1
  let tb : Icc a b := ⟨b, hab.le, le_rfl⟩
  obtain ⟨hbInt, eb, heb⟩ := hregular b tb.2 (q tb).val (q tb).2 (hq tb)
  obtain ⟨η, hηbase, hηan, _, Vb, _, hVb, _, hVbb, hηroot, _⟩ :=
    PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction_with_local_uniqueness
      (hF b tb.2 (q tb).val (q tb).2) (hq tb) eb heb
  have hηC : ∀ᶠ t in 𝓝 b, η t ∈ C := hηan.continuousAt.eventually (hηbase.symm ▸ mem_interior_iff_mem_nhds.mp hbInt)
  have hηzero : ∀ᶠ t in 𝓝 b, F (t, η t) = 0 := by
    filter_upwards [hVb.mem_nhds hVbb] with t ht using (hηroot t ht).2
  let ψ : ℝ → E := fun t => if ht : t ∈ Icc a b then (q ⟨t, ht⟩).val else η t
  have hψC (t) (ht : t ∈ Icc a b) : ψ t ∈ C ∧ F (t, ψ t) = 0 := by
    simp only [ψ, dite_eq_left ht]; exact ⟨(q ⟨t, ht⟩).2, hq ⟨t, ht⟩⟩
  have hηψ : η =ᶠ[𝓝 b] ψ := by
    filter_upwards [hηC, hηzero] with t ht hz
    by_cases hm : t ∈ Icc a b
    · simpa only [ψ, dite_eq_left hm] using congrArg Subtype.val
        ((hunique ⟨t, hm⟩).unique (y₁ := (⟨η t, ht⟩ : C)) hz (hq ⟨t, hm⟩))
    · simp only [ψ, dite_eq_right hm]
  obtain ⟨l, b', hlb, hnear⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hηan.congr hηψ).eventually_analyticAt.and (hηzero.mp (hηψ.mono fun t heq ht => heq ▸ ht)))
  refine ⟨b', hlb.2, ψ, fun t ht => ?_, fun t ht => ?_, hψC⟩
  · by_cases htb : t < b
    · let tt : Icc a b := ⟨t, ht.1.le, htb.le⟩
      obtain ⟨hint, e, he⟩ := hregular t tt.2 (q tt).val (q tt).2 (hq tt)
      obtain ⟨φ, hφb, hφan, hφz⟩ :=
        PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction (hF t tt.2 (q tt).val (q tt).2) (hq tt) e he
      refine hφan.congr ?_
      filter_upwards [hφan.continuousAt.eventually (hφb.symm ▸ mem_interior_iff_mem_nhds.mp hint),
        hφz, isOpen_Ioo.mem_nhds ⟨ht.1, htb⟩] with u hu hz hIoo
      have hm : u ∈ Icc a b := ⟨hIoo.1.le, hIoo.2.le⟩
      simpa only [ψ, dite_eq_left hm] using congrArg Subtype.val
        ((hunique ⟨u, hm⟩).unique (y₁ := (⟨φ u, hu⟩ : C)) hz (hq ⟨u, hm⟩))
    · exact (hnear ⟨hlb.1.trans_le (le_of_not_gt htb), ht.2⟩).1
  · by_cases htb : t ≤ b
    · exact (hψC t ⟨ht.1.le, htb⟩).2
    · exact (hnear ⟨hlb.1.trans (lt_of_not_ge htb), ht.2⟩).2

/-- Theorem 2.3 for every sufficiently large even N, with n=N/2-r. -/
theorem theorem23 (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ Δ₁ : ℝ, Δ₀ < Δ₁ ∧ Δ₁ < -1 ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      let n := N / 2 - r
      ∃ hn : 0 < n, ∃ hs : 2 * n ≤ N,
      ∃ p : ℝ → (Fin n → ℝ),
      ∃ hp : ∀ (Δ : ℝ), Δ ≤ Δ₀ → p Δ ∈ S_n n,
        (∀ Δ ≤ Δ₀, DiscreteBetheEquation Δ N n (p Δ)) ∧
        AnalyticOnNhd ℝ p (Iio Δ₁) ∧
        (∃ P : ℝ → (Fin n → ℝ), AnalyticAt ℝ P 0 ∧
          P 0 = discreteBaseSolution N n ∧ ∀ Δ ≤ Δ₀, p Δ = P (1 / Δ)) ∧
        ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀),
          densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
            (fun x => rootStepDensity N n (p Δ) (hp Δ hΔ) hn hs x - rho Δ x)
            (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) _ (hp Δ hΔ) hn hs) ≤ K / N := by
  let Δ₁ := (Δ₀ - 1) / 2
  have hΔ₁ : Δ₁ < -1 := by dsimp [Δ₁]; linarith
  have hΔ₀₁ : Δ₀ < Δ₁ := by dsimp [Δ₁]; linarith
  obtain ⟨c, D, K, hc, hcpi, hDlarge, hK, M₀, hM₀, hbootstrap⟩ := exists_uniform_strict_gap_bootstrap r hΔ₁
  have hD : 0 < D := lt_trans (by positivity) hDlarge
  obtain ⟨L₀, hL₀, hmatrix⟩ := exists_uniform_Bethe_matrix_nonsingular hΔ₁ D hD.le
  refine ⟨K, hK, max (max M₀ L₀) (2 * (r + 1)),
    lt_of_lt_of_le hM₀ ((le_max_left _ _).trans (le_max_left _ _)),
    Δ₁, hΔ₀₁, hΔ₁, fun N hlarge heven => ?_⟩
  have hMlarge : M₀ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hlarge
  have hLlarge : L₀ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hlarge
  have hrlarge : 2 * (r + 1) ≤ N := (le_max_right _ _).trans hlarge
  obtain ⟨m, hm⟩ := heven
  have hn0 : 0 < N / 2 - r := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  dsimp only; rw [hk]
  have hcount : N = 2 * ((k + 1) + r) := by omega
  have hs : 2 * (k + 1) ≤ N := by omega
  have hN : 0 < N := lt_of_lt_of_le hM₀ hMlarge
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  let C := betheGapRegion k (c / N) (D / N)
  let F := fun z : ℝ × (Fin ((k + 1) / 2) → ℝ) => discreteCoordinateResidualInv z.1 N (k + 1) z.2
  have hbaseInt : discreteBaseCoordinates N (k + 1) ∈ interior C :=
    mem_interior_betheGapRegion (discreteBaseCoordinates_strict_gaps hN hs hcount hcpi hDlarge)
  have hreg : ∀ ε ∈ Icc (1 / Δ₁) 0, ∀ q ∈ C, F (ε, q) = 0 →
      q ∈ interior C ∧ ∃ e : (Fin ((k + 1) / 2) → ℝ) ≃L[ℝ] (Fin ((k + 1) / 2) → ℝ),
        (fderiv ℝ F (ε, q)).comp (ContinuousLinearMap.inr ℝ ℝ _) = (e : _ →L[ℝ] _) := by
    intro ε hε q hq hzero
    by_cases hε0 : ε = 0
    · subst ε
      have hqb : q = discreteBaseCoordinates N (k + 1) :=
        (discreteCoordinateResidualInv_base_unique hN hs).unique hzero (discreteCoordinateResidualInv_base_zero hN hs)
      have hnN : ((k + 1 : ℕ) : ℝ) < N := by exact_mod_cast (show k + 1 < N by omega)
      have ha0 : 0 < 1 - ((k + 1 : ℕ) : ℝ) / N := sub_pos.mpr ((div_lt_one hNc).2 hnN)
      refine ⟨hqb ▸ hbaseInt, (LinearEquiv.smulOfNeZero ℝ _ (1 - ((k + 1 : ℕ) : ℝ) / N) ha0.ne').toContinuousLinearEquiv, ?_⟩
      rw [stateDerivative_eq_slice (analyticAt_discreteCoordinateResidualInv (by norm_num : |(0 : ℝ)| < 1) N (k + 1) q).differentiableAt]
      dsimp only [F]
      let bvec : Fin ((k + 1) / 2) → ℝ := fun i => 2 * Real.pi * discreteBetheIndex (k + 1) (discreteHalfIndex (k + 1) i) / N
      rw [show discreteCoordinateResidualInv 0 N (k + 1) = fun v => (1 - ((k + 1 : ℕ) : ℝ) / N) • v - bvec from
        funext (discreteCoordinateResidualInv_zero N (k + 1))]
      exact (((hasFDerivAt_id q).const_smul (1 - ((k + 1 : ℕ) : ℝ) / N)).sub_const bvec).fderiv
    · let Δ := 1 / ε
      have hneg : ε < 0 := lt_of_le_of_ne hε.2 hε0
      have hΔ : Δ ≤ Δ₁ := by simpa only [one_div_one_div] using one_div_le_one_div_of_neg_of_le hneg hε.1
      have hvalid : Δ < -1 := lt_of_le_of_lt hΔ hΔ₁
      have hInv : 1 / Δ = ε := one_div_one_div ε
      have hpS : discreteSymLift (k + 1) q ∈ S_n (k + 1) := betheGapRegion_mem_S_n (div_pos hc hNc) hq
      have hBE : DiscreteBetheEquation Δ N (k + 1) (discreteSymLift (k + 1) q) :=
        (discreteCoordinateResidual_zero_iff hN q).1 (by rw [← discreteCoordinateResidualInv_eq hvalid, hInv]; exact hzero)
      have hstrict := (hbootstrap Δ hΔ N k hMlarge hcount _ hpS hs hBE fun j => (hq j).2).2
      have hdet := hmatrix Δ hΔ N k hLlarge hs _ hpS hBE fun j => (hq j).2
      let A := discreteBetheMatrixA Δ N (k + 1) (discreteSymLift (k + 1) q)
      refine ⟨mem_interior_betheGapRegion hstrict,
        (Matrix.toLinearEquiv (Pi.basisFun ℝ _) A (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv, ?_⟩
      dsimp only [F]
      rw [← hInv, stateDerivative_eq_slice
          (analyticAt_discreteCoordinateResidualInv (abs_inverse_parameter_lt_one hvalid) N (k + 1) q).differentiableAt]
      dsimp only
      rw [funext (discreteCoordinateResidualInv_eq hvalid N (k + 1)),
        ← stateDerivative_eq_slice (analyticAt_discreteCoordinateResidual hvalid N (k + 1) q).differentiableAt,
        discreteCoordinateResidual_stateDerivative hvalid]
      ext v i; change (Matrix.toLin' A v) i = (Matrix.toLin (Pi.basisFun ℝ _) (Pi.basisFun ℝ _) A v) i
      rw [Matrix.toLin_eq_toLin']
  have ha : 1 / Δ₁ < 0 := one_div_neg.mpr (by linarith)
  obtain ⟨b, hb, ψ, hψan, _, hψC⟩ := exists_analytic_implicit_family_on_open_interval
    (isCompact_betheGapRegion k (div_pos hc hNc)) ha
    (fun ε hε q _ => analyticAt_discreteCoordinateResidualInv
      (by have h0 := abs_lt.mp (abs_inverse_parameter_lt_one hΔ₁); exact abs_lt.mpr ⟨by linarith [hε.1], by linarith [hε.2]⟩)
      N (k + 1) q)
    hreg
    ⟨⟨discreteBaseCoordinates N (k + 1), interior_subset hbaseInt⟩,
      discreteCoordinateResidualInv_base_zero hN hs, fun q hq => Subtype.ext
        ((discreteCoordinateResidualInv_base_unique hN hs).unique hq (discreteCoordinateResidualInv_base_zero hN hs))⟩
  let P : ℝ → (Fin (k + 1) → ℝ) := fun ε => discreteSymLift (k + 1) (ψ ε)
  let p : ℝ → (Fin (k + 1) → ℝ) := fun Δ => P (1 / Δ)
  have hparam (Δ : ℝ) (hΔ : Δ ≤ Δ₀) : 1 / Δ ∈ Icc (1 / Δ₁) 0 := inverse_parameter_mem hΔ₁ (hΔ.trans hΔ₀₁.le)
  have hp (Δ : ℝ) (hΔ : Δ ≤ Δ₀) : p Δ ∈ S_n (k + 1) :=
    betheGapRegion_mem_S_n (div_pos hc hNc) (hψC _ (hparam Δ hΔ)).1
  have hBE (Δ : ℝ) (hΔ : Δ ≤ Δ₀) : DiscreteBetheEquation Δ N (k + 1) (p Δ) := by
    apply (discreteCoordinateResidual_zero_iff hN (ψ (1 / Δ))).1
    rw [← discreteCoordinateResidualInv_eq (lt_of_le_of_lt hΔ hΔ₀)]
    exact (hψC _ (hparam Δ hΔ)).2
  have hPan (ε : ℝ) (hε : ε ∈ Ioo (1 / Δ₁) b) : AnalyticAt ℝ P ε :=
    (discreteSymLift (k + 1)).toContinuousLinearMap.analyticAt _ |>.comp (hψan ε hε)
  refine ⟨by omega, hs, p, hp, hBE, fun Δ hΔ => ?_, ⟨P, hPan 0 ⟨ha, hb⟩, ?_, fun _ _ => rfl⟩, fun Δ hΔ => ?_⟩
  · have hΔneg : Δ < 0 := lt_trans hΔ (lt_trans hΔ₁ (by norm_num))
    exact (hPan _ ⟨one_div_lt_one_div_of_neg_of_lt (by linarith) hΔ, (one_div_neg.mpr hΔneg).trans hb⟩).comp
      (analyticAt_const.div analyticAt_id hΔneg.ne)
  · have hqb : ψ 0 = discreteBaseCoordinates N (k + 1) :=
      (discreteCoordinateResidualInv_base_unique hN hs).unique (hψC 0 ⟨ha.le, le_rfl⟩).2
        (discreteCoordinateResidualInv_base_zero hN hs)
    dsimp only [P]; rw [hqb]
    exact discreteSymLift_coordinates _ (discreteBaseSolution_mem_S_n hN hs).2.2
  · exact (hbootstrap Δ (hΔ.trans hΔ₀₁.le) N k hMlarge hcount _ (hp Δ hΔ) hs (hBE Δ hΔ)
      fun j => ((hψC _ (hparam Δ hΔ)).1 j).2).1

end PottsDiscontinuity.Bethe
