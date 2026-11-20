module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.SpatialPrincipalIntegrationByParts

import Mathlib.Analysis.Real.Sqrt

/-!
# Smooth principal coercivity

This module derives the quantitative fixed-time principal coercivity estimate
from the exact localized integration-by-parts identity.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology
open scoped BigOperators MatrixOrder

namespace HypoellipticAleksandrov.Parabolic

/-- The constant in fixed-time principal coercivity. -/
def principalCoercivityConstant
    (d : ℕ) (lam Lam M K : ℝ) : ℝ :=
  2 * (d : ℝ) ^ 3 / lam * (M + Lam * K) ^ 2

private theorem principal_lower_pointwise
    {d : ℕ} {lam : ℝ} {O : Set (PDE.Vec d)}
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    {y : PDE.Vec d} (hy : y ∈ O) :
    lam * (η y) ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2) ≤
      (η y) ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y) := by
  have hrow (k : Fin d) :
      lam * (∑ i, spatialSecond q k i y ^ 2) ≤
        ∑ i, ∑ j, spatialSecond q k i y *
          (A y i j * spatialSecond q k j y) := by
    simpa only [PDE.vecNormSq, PDE.vecDot, Matrix.mulVec, dotProduct,
      Finset.mul_sum, pow_two] using
      (vecDot_mulVec_lower_of_loewner (hAlower y hy)
        (fun i => spatialSecond q k i y))
  have hsum :
      lam * (∑ k, ∑ i, spatialSecond q k i y ^ 2) ≤
        ∑ k, ∑ i, ∑ j, spatialSecond q k i y *
          (A y i j * spatialSecond q k j y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hrow k
  calc
    lam * (η y) ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2) =
        (η y) ^ 2 * (lam * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) := by ring
    _ ≤ (η y) ^ 2 * (∑ k, ∑ i, ∑ j, spatialSecond q k i y *
          (A y i j * spatialSecond q k j y)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg (η y))
    _ = (η y) ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Entry bounds and Cauchy–Schwarz for a weighted triple contraction. -/
private theorem abs_triple_contraction_le {d : ℕ}
    (P H : Fin d → Fin d → Fin d → ℝ) (G : Fin d → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hP : ∀ i j k, |P i j k| ≤ B) :
    |∑ i, ∑ j, ∑ k, P i j k * G k * H i j k| ≤
      B * (Real.sqrt (∑ i, ∑ j, ∑ k, H i j k ^ 2) *
        Real.sqrt ((d : ℝ) ^ 2 * ∑ k, G k ^ 2)) := by
  have hcs : (∑ i, ∑ j, ∑ k, |H i j k| * |G k|) ≤
      Real.sqrt (∑ i, ∑ j, ∑ k, H i j k ^ 2) *
        Real.sqrt ((d : ℝ) * ((d : ℝ) * ∑ k, G k ^ 2)) := by
    simpa only [Fintype.sum_prod_type, sq_abs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using
      Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d × Fin d × Fin d))
        (fun p => |H p.1 p.2.1 p.2.2|) (fun p => |G p.2.2|)
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, |P i j k * G k * H i j k| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ∑ k, B * (|H i j k| * |G k|) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
      simp only [abs_mul, mul_assoc]
      rw [mul_comm (|G k|)]
      exact mul_le_mul_of_nonneg_right (hP i j k) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := by
      simp only [← Finset.mul_sum]
      simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hcs hB

private theorem abs_scale_le {a b x R : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : |x| ≤ R) : |a * x| ≤ b * R := by
  rw [abs_mul, abs_of_nonneg ha]
  exact mul_le_mul hab h (abs_nonneg _) (ha.trans hab)

private theorem remainder_lower_pointwise
    {d : ℕ} (hd : 0 < d) {lam Lam M K : ℝ}
    {O : Set (PDE.Vec d)}
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    (hAupper : ∀ y ∈ O, A y ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ y ∈ O, ∀ i j k : Fin d,
      |spatialPartial k (fun x => A x i j) y| ≤ M)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    {y : PDE.Vec d} (hy : y ∈ O) :
    2 * (η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y))
      + η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y) ≥
      -(lam / 2 * (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) +
        principalCoercivityConstant d lam Lam M K *
          (∑ k, spatialPartial k q y ^ 2)) := by
  let e := η y
  let H := fun j k => spatialSecond q j k y
  let G := fun k => spatialPartial k q y
  let D := (d : ℝ)
  let HH := ∑ j, ∑ k, H j k ^ 2
  let GG := ∑ k, G k ^ 2
  let X := Real.sqrt (D * HH)
  let Y := Real.sqrt (D ^ 2 * GG)
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast hd
  have hLK : 0 ≤ Lam * K := mul_nonneg (hlam.le.trans hlamLam) hK
  have he : 0 ≤ e := hηnonneg y
  have he2 : e ^ 2 ≤ e := by nlinarith only [he, hηle y]
  have h1 := abs_triple_contraction_le
    (fun i j _ => spatialPartial i η y * A y i j) (fun _ j k => H j k) G hLK (by
      intro i j k
      rw [abs_mul, mul_comm Lam]
      exact mul_le_mul (hηderiv y hy i)
        (abs_apply_le_of_loewner hlam (hAlower y hy) (hAupper y hy) i j) (abs_nonneg _) hK)
  have h2 := abs_triple_contraction_le
    (fun i j _ => spatialPartial i (fun x => A x i j) y) (fun _ j k => H j k) G hM
      (fun i j _ => hAderiv y hy i j i)
  have h3 := abs_triple_contraction_le
    (fun i j k => spatialPartial k (fun x => A x i j) y) (fun i j _ => H j i) G hM (fun i j k => hAderiv y hy i j k)
  have hconst : (∑ i, ∑ j, ∑ _k : Fin d, H j i ^ 2) = D * HH := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    exact congrArg (D * ·) Finset.sum_comm
  rw [hconst] at h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  have h1' := abs_scale_le (a := 2 * e) (by positivity) (le_refl _) h1
  have h2' := abs_scale_le (sq_nonneg e) he2 h2
  have h3' := abs_scale_le (sq_nonneg e) he2 h3
  let C := M + Lam * K
  have hyoung := two_mul_le_add_mul_sq (a := e * X) (b := C * Y) (ε := lam / (2 * D))
    (div_pos hlam (mul_pos (by norm_num) hD))
  have hx : X ^ 2 = D * HH := Real.sq_sqrt (by positivity)
  have hy' : Y ^ 2 = D ^ 2 * GG := Real.sq_sqrt (by positivity)
  rw [mul_pow, mul_pow, hx, hy'] at hyoung
  have hbound : 2 * C * e * (X * Y) ≤
      lam / 2 * (e ^ 2 * HH) + principalCoercivityConstant d lam Lam M K * GG := by
    have hb : lam / (2 * D) * (e ^ 2 * (D * HH)) +
        (lam / (2 * D))⁻¹ * (C ^ 2 * (D ^ 2 * GG)) =
        lam / 2 * (e ^ 2 * HH) + principalCoercivityConstant d lam Lam M K * GG := by
      unfold principalCoercivityConstant
      dsimp only [D, C]
      field_simp [show (d : ℝ) ≠ 0 from hD.ne', hlam.ne']
    calc
      _ = 2 * (e * X) * (C * Y) := by ring
      _ ≤ _ := hyoung.trans_eq hb
  have h1'' : |2 * (e * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j * G k * H j k))| ≤
      2 * e * (Lam * K * (X * Y)) := by
    rw [← mul_assoc]
    exact h1'
  have h3'' : |e ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial k (fun x => A x i j) y * H j i * G k)| ≤ e * (M * (X * Y)) := by
    simpa only [mul_right_comm] using h3'
  have hneg₁ := neg_abs_le (2 * (e * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j * G k * H j k)))
  have hneg₂ := neg_abs_le (e ^ 2 * (∑ i, ∑ j, ∑ k,
    spatialPartial i (fun x => A x i j) y * G k * H j k))
  have hpos₃ := le_abs_self (e ^ 2 * (∑ i, ∑ j, ∑ k,
    spatialPartial k (fun x => A x i j) y * H j i * G k))
  dsimp only [C] at hbound
  change 2 * (e * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j * G k * H j k)) +
    e ^ 2 * (∑ i, ∑ j, ∑ k, spatialPartial i (fun x => A x i j) y * G k * H j k) -
    e ^ 2 * (∑ i, ∑ j, ∑ k, spatialPartial k (fun x => A x i j) y * H j i * G k) ≥
    -(lam / 2 * (e ^ 2 * HH) + principalCoercivityConstant d lam Lam M K * GG)
  change |e ^ 2 * (∑ i, ∑ j, ∑ k, spatialPartial i (fun x => A x i j) y * G k * H j k)| ≤
    e * (M * (X * Y)) at h2'
  nlinarith only [h1'', h2', h3'', hbound, hneg₁, hneg₂, hpos₃]

private theorem principal_remainder_lower_pointwise_on_support
    {d : ℕ} (lam Lam M K : ℝ)
    (O : Set (PDE.Vec d))
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    (hAupper : ∀ y ∈ O, A y ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ y ∈ O, ∀ i j k : Fin d,
      |spatialPartial k (fun x => A x i j) y| ≤ M)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    {y : PDE.Vec d} (hy : y ∈ O) :
    η y ^ 2 * (∑ i, ∑ j, ∑ k,
        A y i j * spatialSecond q k i y * spatialSecond q k j y)
      + 2 * (η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
        spatialPartial k q y * spatialSecond q j k y))
      + η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
          spatialSecond q j k y)
      - η y ^ 2 * (∑ i, ∑ j, ∑ k,
        spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
          spatialPartial k q y) ≥
      lam / 2 * (η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)) -
        principalCoercivityConstant d lam Lam M K *
          (tsupport η).indicator (fun z => ∑ k, spatialPartial k q z ^ 2) y := by
  by_cases hd : 0 < d
  · by_cases hys : y ∈ tsupport η
    · let i : Fin d := ⟨0, hd⟩
      have hM := (abs_nonneg _).trans (hAderiv y hy i i i)
      have hK := (abs_nonneg _).trans (hηderiv y hy i)
      have hr := remainder_lower_pointwise hd A q η hlam hlamLam hAlower hAupper
        hAderiv hηnonneg hηle hηderiv hM hK hy
      have hp := principal_lower_pointwise A q η hAlower hy
      rw [Set.indicator_of_mem hys]
      nlinarith only [hr, hp]
    · rw [Set.indicator_of_notMem hys, image_eq_zero_of_notMem_tsupport hys]
      ring_nf
      exact le_refl _
  · obtain rfl : d = 0 := Nat.eq_zero_of_not_pos hd
    simp

section
variable {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O) (q η : PDE.Vec d → ℝ)
  (hq : ContDiffOn ℝ 3 q O)
include hO hq

private theorem integrableOn_weighted_spatialSecond_sq
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O) :
    IntegrableOn (fun y => η y ^ 2 *
      (∑ k, ∑ i, spatialSecond q k i y ^ 2)) O := by
  have hqsecond (k i : Fin d) : ContDiffOn ℝ 0 (spatialSecond q k i) O :=
    (contDiffOn_spatialPartial hO i
      (contDiffOn_spatialPartial hO k hq)).of_le (by norm_num)
  have hsum : ContDiffOn ℝ 0
      (fun y => ∑ k, ∑ i, spatialSecond q k i y ^ 2) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun k _ =>
        ContDiffOn.sum (s := Finset.univ) fun i _ => (hqsecond k i).pow 2)
  have hη0 : ContDiffOn ℝ 0 η O := hη.contDiffOn.of_le (by simp)
  have hcompact2 : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηcompact.mul_left
  have hsupport2 : tsupport (fun y => η y ^ 2) ⊆ O :=
    (by simpa [pow_two] using tsupport_mul_subset_left.trans hηsupport)
  exact integrableOn_of_local_compactSupport hO _ ((hη0.pow 2).mul hsum)
    hcompact2.mul_right (tsupport_mul_subset_left.trans hsupport2)

private theorem integrableOn_spatialPartial_sq_tsupport
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O) :
    IntegrableOn (fun y => ∑ k, spatialPartial k q y ^ 2) (tsupport η) := by
  have hqp (k : Fin d) : ContDiffOn ℝ 0 (spatialPartial k q) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hq.of_le (by norm_num))
  have hsum : ContDiffOn ℝ 0 (fun y => ∑ k, spatialPartial k q y ^ 2) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun k _ => (hqp k).pow 2)
  exact (hsum.continuousOn.mono hηsupport).integrableOn_compact hηcompact

end

/-- Quantitative fixed-time coercivity of the negative localized principal
pairing, modulo the gradient remainder on the cutoff's topological support. -/
theorem smoothPrincipalIntegrationByParts_coercive
    {d : ℕ} (lam Lam M K : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : PDE.Vec d → PDE.Mat d) (q η : PDE.Vec d → ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y => A y i j) O)
    (hAlower : ∀ y ∈ O, lam • (1 : PDE.Mat d) ≤ A y)
    (hAupper : ∀ y ∈ O, A y ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ y ∈ O, ∀ i j k : Fin d,
      |spatialPartial k (fun x => A x i j) y| ≤ M)
    (hq : ContDiffOn ℝ 3 q O)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y)
    (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d,
      |spatialPartial i η y| ≤ K) :
    -(∫ y in O,
        (∑ i, ∑ j, A y i j * spatialSecond q j i y) *
          (-∑ k,
            (2 * η y * spatialPartial k η y * spatialPartial k q y +
              η y ^ 2 * spatialSecond q k k y)) ∂volume) ≥
      lam / 2 *
        (∫ y in O, η y ^ 2 *
          (∑ k, ∑ i, spatialSecond q k i y ^ 2) ∂volume)
      - principalCoercivityConstant d lam Lam M K *
        (∫ y in tsupport η,
          ∑ k, spatialPartial k q y ^ 2 ∂volume) := by
  let L : PDE.Vec d → ℝ := fun y =>
    η y ^ 2 * (∑ i, ∑ j, ∑ k,
      A y i j * spatialSecond q k i y * spatialSecond q k j y)
    + 2 * η y * (∑ i, ∑ j, ∑ k, spatialPartial i η y * A y i j *
      spatialPartial k q y * spatialSecond q j k y)
    + η y ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
        spatialSecond q j k y)
    - η y ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
        spatialPartial k q y)
  let E : PDE.Vec d → ℝ := fun y =>
    η y ^ 2 * (∑ k, ∑ i, spatialSecond q k i y ^ 2)
  let G : PDE.Vec d → ℝ := fun y => ∑ k, spatialPartial k q y ^ 2
  have hEint : IntegrableOn E O :=
    integrableOn_weighted_spatialSecond_sq hO q η hq hη hηcompact hηsupport
  have hGint : IntegrableOn G (tsupport η) :=
    integrableOn_spatialPartial_sq_tsupport hO q η hq hηcompact hηsupport
  have hGindicator : IntegrableOn ((tsupport η).indicator G) O := by
    exact (hGint.integrable_indicator (isClosed_tsupport η).measurableSet).integrableOn
  have hrightInt : IntegrableOn (fun y => lam / 2 * E y -
      principalCoercivityConstant d lam Lam M K * (tsupport η).indicator G y) O :=
    (hEint.const_mul _).sub (hGindicator.const_mul _)
  have hpoint : ∀ᵐ y ∂(volume.restrict O),
      lam / 2 * E y - principalCoercivityConstant d lam Lam M K *
          (tsupport η).indicator G y ≤ L y := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with y hy
    dsimp [L, E, G]
    simpa only [mul_assoc] using
      (principal_remainder_lower_pointwise_on_support lam Lam M K O A q η
        hlam hlamLam hAlower hAupper hAderiv hηnonneg hηle hηderiv hy)
  have hindicatorIntegral :
      (∫ y in O, (tsupport η).indicator G y ∂volume) = ∫ y in tsupport η, G y ∂volume := by
    rw [MeasureTheory.setIntegral_indicator (isClosed_tsupport η).measurableSet]
    rw [inter_eq_right.mpr hηsupport]
  have hrightIntegral :
      (∫ y in O, lam / 2 * E y - principalCoercivityConstant d lam Lam M K *
          (tsupport η).indicator G y ∂volume) =
        lam / 2 * (∫ y in O, E y ∂volume) -
          principalCoercivityConstant d lam Lam M K *
            (∫ y in tsupport η, G y ∂volume) := by
    rw [integral_sub (hEint.const_mul _) (hGindicator.const_mul _),
      integral_const_mul, integral_const_mul, hindicatorIntegral]
  have hη0 : ContDiffOn ℝ 0 η O := hη.contDiffOn.of_le (by simp)
  have hηp (i : Fin d) : ContDiffOn ℝ 0 (spatialPartial i η) O :=
    contDiffOn_spatialPartial (n := 0) hO i (hη.contDiffOn.of_le (by simp))
  have hqp (k : Fin d) : ContDiffOn ℝ 0 (spatialPartial k q) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hq.of_le (by norm_num))
  have hqsecond (j k : Fin d) : ContDiffOn ℝ 0 (spatialSecond q j k) O :=
    contDiffOn_spatialPartial (n := 0) hO k
      (contDiffOn_spatialPartial (n := 1) hO j (hq.of_le (by norm_num)))
  have hA0 (i j : Fin d) : ContDiffOn ℝ 0 (fun y => A y i j) O :=
    (hA i j).of_le (by norm_num)
  have hAp (i j k : Fin d) : ContDiffOn ℝ 0
      (spatialPartial k (fun x => A x i j)) O :=
    contDiffOn_spatialPartial (n := 0) hO k (hA i j)
  have htriple {f : Fin d → Fin d → Fin d → PDE.Vec d → ℝ}
      (hf : ∀ i j k, ContDiffOn ℝ 0 (f i j k) O) :
      ContDiffOn ℝ 0 (fun y => ∑ i, ∑ j, ∑ k, f i j k y) O := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (ContDiffOn.sum (s := Finset.univ) fun i _ =>
        ContDiffOn.sum (s := Finset.univ) fun j _ =>
          ContDiffOn.sum (s := Finset.univ) fun k _ => hf i j k)
  have hcompact2 : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηcompact.mul_left
  have hsupport2 : tsupport (fun y => η y ^ 2) ⊆ O :=
    (by simpa [pow_two] using tsupport_mul_subset_left.trans hηsupport)
  let P : PDE.Vec d → ℝ := fun y => η y ^ 2 * (∑ i, ∑ j, ∑ k,
    A y i j * spatialSecond q k i y * spatialSecond q k j y)
  let C : PDE.Vec d → ℝ := fun y => η y * (∑ i, ∑ j, ∑ k,
    spatialPartial i η y * A y i j * spatialPartial k q y * spatialSecond q j k y)
  let I : PDE.Vec d → ℝ := fun y => η y ^ 2 * (∑ i, ∑ j, ∑ k,
    spatialPartial i (fun x => A x i j) y * spatialPartial k q y *
      spatialSecond q j k y)
  let J : PDE.Vec d → ℝ := fun y => η y ^ 2 * (∑ i, ∑ j, ∑ k,
      spatialPartial k (fun x => A x i j) y * spatialSecond q j i y *
        spatialPartial k q y)
  have hP : IntegrableOn P O := by
    apply integrableOn_of_local_compactSupport hO P
    · exact (hη0.pow 2).mul (htriple fun i j k =>
        ((hA0 i j).mul (hqsecond k i)).mul (hqsecond k j))
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  have hC : IntegrableOn C O := by
    apply integrableOn_of_local_compactSupport hO C
    · exact hη0.mul (htriple fun i j k =>
        (((hηp i).mul (hA0 i j)).mul (hqp k)).mul (hqsecond j k))
    · exact hηcompact.mul_right
    · exact tsupport_mul_subset_left.trans hηsupport
  have hI : IntegrableOn I O := by
    apply integrableOn_of_local_compactSupport hO I
    · exact (hη0.pow 2).mul (htriple fun i j k =>
        ((hAp i j i).mul (hqp k)).mul (hqsecond j k))
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  have hJ : IntegrableOn J O := by
    apply integrableOn_of_local_compactSupport hO J
    · exact (hη0.pow 2).mul (htriple fun i j k =>
        ((hAp i j k).mul (hqsecond j i)).mul (hqp k))
    · exact hcompact2.mul_right
    · exact tsupport_mul_subset_left.trans hsupport2
  let C₂ := fun x => 2 * C x
  have hC₂ : IntegrableOn C₂ O := hC.const_mul 2
  have hLC : L = P + C₂ + I - J := by
    funext y
    dsimp only [L, P, C, C₂, I, J, Pi.add_apply, Pi.sub_apply]
    ring
  have hLint : IntegrableOn L O := hLC.symm ▸ ((hP.add hC₂).add hI).sub hJ
  have hmono := integral_mono_ae hrightInt hLint hpoint
  have hLintSplit : (∫ y in O, L y ∂volume) =
      (∫ y in O, P y ∂volume) + 2 * (∫ y in O, C y ∂volume) +
        (∫ y in O, I y ∂volume) - (∫ y in O, J y ∂volume) := by
    rw [hLC, integral_sub' ((hP.add hC₂).add hI) hJ,
      integral_add' (hP.add hC₂) hI, integral_add' hP hC₂]
    simp only [C₂, integral_const_mul]
  have hibp := smoothPrincipalIntegrationByParts O hO A q η hA hq hη hηcompact hηsupport
  have hnegIdentity :
      -(∫ y in O,
        (∑ i, ∑ j, A y i j * spatialSecond q j i y) *
          (-∑ k, (2 * η y * spatialPartial k η y * spatialPartial k q y +
            η y ^ 2 * spatialSecond q k k y)) ∂volume) = ∫ y in O, L y ∂volume := by
    rw [hLintSplit]
    dsimp [P, C, I, J]
    linarith
  rw [hnegIdentity, ← hrightIntegral]
  exact hmono
