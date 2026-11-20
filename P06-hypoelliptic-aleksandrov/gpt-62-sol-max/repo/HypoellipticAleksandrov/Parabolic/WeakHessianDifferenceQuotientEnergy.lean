module

public import HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
public import HypoellipticAleksandrov.Parabolic.WeakPrincipalCoercivity
public import Mathlib.Algebra.Order.Chebyshev

import HypoellipticAleksandrov.Analysis.L2Convergence
import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp

/-!
# Weak Hessian difference-quotient energy foundations

This module records the integrability foundations for the fixed-cylinder weak
Hessian energy argument.  In particular, it keeps the ordered convention
`QH z j i` and the literal residual orientation
`QW + principal + drift + scalar = R`.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology
open scoped ENNReal BigOperators MatrixOrder

namespace HypoellipticAleksandrov.Parabolic

private theorem lowerOrderSource_memLp
    {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (B : TimeVelocity d → PDE.Vec d) (C0 q R : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (M : ℝ) (hM : 0 ≤ M)
    (hBmeas : AEStronglyMeasurable B
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hCmeas : AEStronglyMeasurable C0
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hB : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d, |B z j| ≤ M)
    (hC : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, |C0 z| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z ↦ QG z j))
    (hR : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R) :
    ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z ↦
      R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) := by
  have hmem := ae_restrict_mem ((measurableSet_Ioo (a := s₀) (b := s₁)).prod hO.measurableSet)
    (μ := (volume : Measure (TimeVelocity d)))
  have hdrift := memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) fun j _ =>
    (Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hM
      ((continuous_apply j).comp_aestronglyMeasurable hBmeas) (hQG j)
      (hmem.mono fun z hz => hB z hz j)).1
  exact (hR.sub hdrift).sub
    (Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hM hCmeas hq (hmem.mono hC)).1

section
variable {d : ℕ} {S : Set (TimeVelocity d)} (A : TimeVelocity d → PDE.Mat d)

/-- The raw residual equation has the orientation needed by the time-energy
and principal-coercivity pairings.  This lemma is deliberately pointwise and
retains the ordered entry `QH z j i`. -/
private theorem residualEquation_reoriented
    (B QG : TimeVelocity d → PDE.Vec d)
    (C0 q QW R : TimeVelocity d → ℝ)
    (QH : TimeVelocity d → PDE.Mat d)
    (heq : ∀ᵐ z ∂timeVelocityVolumeOn S,
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) +
          (∑ j : Fin d, B z j * QG z j) + C0 z * q z = R z) :
    ∀ᵐ z ∂timeVelocityVolumeOn S,
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) =
        R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z := by
  filter_upwards [heq] with z hz
  linarith

/-- Pairing the reoriented residual equation with the localized divergence
gives the exact integrated decomposition.  The two summands are supplied
separately so that `integral_add` never relies on implicit integrability. -/
private theorem integrated_residual_pairing
    (QW F : TimeVelocity d → ℝ)
    (QH : TimeVelocity d → PDE.Mat d)
    (D : TimeVelocity d → ℝ)
    (heq : ∀ᵐ z ∂timeVelocityVolumeOn S,
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) = F z)
    (hIw : IntegrableOn (fun z => QW z * D z) S volume)
    (hIp : IntegrableOn (fun z =>
      (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) * D z) S volume)
    :
    (∫ z in S, QW z * D z ∂volume) +
        (∫ z in S, (∑ i : Fin d, ∑ j : Fin d,
          A z i j * QH z j i) * D z ∂volume) =
      ∫ z in S, F z * D z ∂volume := by
  rw [← integral_add hIw hIp]
  apply integral_congr_ae
  filter_upwards [heq] with z hz
  rw [← add_mul, hz]

end

/-- The scalar sign calculation at the heart of the pre-Young estimate.  It
keeps the time identity, residual splitting, and principal lower bound as
separate named inputs, matching the three analytic lemmas that produce them. -/
private theorem preYoung_of_time_residual_principal
    (lam Cpr E G If It Iw Ip : ℝ)
    (htime : 2 * Iw = -It)
    (hresidual : Iw + Ip = If)
    (hprincipal : -Ip ≥ lam / 2 * E - Cpr * G) :
    lam / 2 * E ≤ Cpr * G + |If| + |It| / 2 := by
  linarith only [htime, hresidual, hprincipal, neg_le_abs If, neg_le_abs It]

/-- Scalar Young inequality with the coefficient used to absorb one diagonal
Hessian entry.  Its proof uses only positivity of `lam`, not a dimension
factor. -/
private theorem abs_mul_le_quarter_young (lam x y : ℝ) (hlam : 0 < lam) :
    |x| * |y| ≤ lam / 4 * y ^ 2 + 1 / lam * x ^ 2 := by
  have h := two_mul_le_add_mul_sq (a := |y|) (b := |x|) (ε := lam / 2) (by positivity)
  rw [sq_abs, sq_abs, inv_div] at h
  linarith only [h, show (2 / lam) * x ^ 2 = 2 * (1 / lam * x ^ 2) by ring]

private theorem weight_le_one {z w : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hw : 0 ≤ w) (hw' : w ≤ 1) : z * w ^ 2 ≤ 1 :=
  mul_le_one₀ hz' (sq_nonneg _) (pow_le_one₀ hw hw')

/-- The pointwise coordinate estimate for the two terms in the localized
gradient divergence.  The cutoff weights are retained on the absorbed
Hessian square and discarded only from the lower-order squares. -/
private theorem localizedGradientDivergence_coordinate_young
    (lam Keta ζ η F G H Dη : ℝ)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hζnonneg : 0 ≤ ζ) (hζle : ζ ≤ 1)
    (hηnonneg : 0 ≤ η) (hηle : η ≤ 1) (hDη : |Dη| ≤ Keta) :
    |ζ * F * (2 * η * Dη * G + η ^ 2 * H)| ≤
      lam / 4 * (ζ * η ^ 2 * H ^ 2) + Keta * G ^ 2 +
        (Keta + 1 / lam) * F ^ 2 := by
  have hgrad := two_mul_le_add_sq |F| |G|
  rw [sq_abs, sq_abs] at hgrad
  have hgrad' : |ζ * F * (2 * η * Dη * G)| ≤ Keta * (F ^ 2 + G ^ 2) := by
    simp only [abs_mul, abs_of_nonneg hζnonneg, abs_of_nonneg hηnonneg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 1 * |F| * (2 * 1 * Keta * |G|) := by gcongr
      _ = Keta * (2 * |F| * |G|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrad hKeta
  have hweight := weight_le_one hζnonneg hζle hηnonneg hηle
  have hy := mul_le_mul_of_nonneg_left (abs_mul_le_quarter_young lam F H hlam)
    (mul_nonneg hζnonneg (sq_nonneg η))
  have hdrop := mul_le_of_le_one_left (show 0 ≤ 1 / lam * F ^ 2 by positivity) hweight
  have hs := abs_add_le (ζ * F * (2 * η * Dη * G)) (ζ * F * (η ^ 2 * H))
  rw [← mul_add] at hs
  rw [show |ζ * F * (η ^ 2 * H)| = (ζ * η ^ 2) * (|F| * |H|) by
    simp only [abs_mul, abs_of_nonneg hζnonneg, abs_of_nonneg (sq_nonneg η)]; ring] at hs
  linarith only [hs, hgrad', hy, hdrop]

private theorem integral_sum_three {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {e g f : α → ℝ} (he : Integrable e μ) (hg : Integrable g μ) (hf : Integrable f μ)
    (a b c : ℝ) :
    (∫ x, a * e x + b * g x + c * f x ∂μ) =
      a * (∫ x, e x ∂μ) + b * (∫ x, g x ∂μ) + c * ∫ x, f x ∂μ := by
  change (∫ x, (((fun x => a * e x) + fun x => b * g x) + fun x => c * f x) x ∂μ) = _
  rw [integral_add' ((he.const_mul a).add (hg.const_mul b)) (hf.const_mul c),
    integral_add' (he.const_mul a) (hg.const_mul b)]
  simp only [integral_const_mul]

/-- The lower-order pairing with an arbitrary restricted `L²` source.  The
diagonal Hessian expenditure is dominated by the full ordered Hessian energy;
no division by the dimension occurs, so the statement includes `d = 0`. -/
private theorem lowerOrder_localizedGradientDivergence_abs_le
    {d : ℕ} (lam Keta s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (F : TimeVelocity d → ℝ) (hF : ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 F)
    (QG : TimeVelocity d → PDE.Vec d)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QG z j))
    (QH : TimeVelocity d → PDE.Mat d)
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QH z j i))
    (η : PDE.Vec d → ℝ) (hη : Continuous η)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ Keta)
    (ζ : ℝ → ℝ) (hζ : Continuous ζ)
    (hζnonneg : ∀ r, 0 ≤ ζ r) (hζle : ∀ r, ζ r ≤ 1)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta) :
    |∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * F z *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume| ≤
      lam / 4 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * η z.2 ^ 2 * ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2 ∂volume) +
      Keta * ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2
        (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ^ 2 +
      (d : ℝ) * (Keta + 1 / lam) *
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O, F z ^ 2 ∂volume) := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let μ := timeVelocityVolumeOn S
  have hmem : ∀ᵐ z ∂μ, z ∈ S :=
    ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)
  have hQGsq : Integrable (fun z => ∑ j : Fin d, QG z j ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hQG j).integrable_sq
  have hQHsq : Integrable (fun z => ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) μ :=
    integrable_finset_sum Finset.univ fun j _ =>
      integrable_finset_sum Finset.univ fun i _ => (hQH j i).integrable_sq
  have hweightMeas : AEStronglyMeasurable (fun z : TimeVelocity d =>
      ζ z.1 * η z.2 ^ 2) μ :=
    (hζ.comp continuous_fst).aestronglyMeasurable.mul
      ((hη.comp continuous_snd).aestronglyMeasurable.pow 2)
  have hweightedH : Integrable (fun z => ζ z.1 * η z.2 ^ 2 *
      ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) μ := by
    apply hQHsq.bdd_mul hweightMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hζnonneg _) (sq_nonneg _))]
    exact weight_le_one (hζnonneg _) (hζle _) (hηnonneg _) (hηle _)
  let Rhs : TimeVelocity d → ℝ := fun z =>
    lam / 4 * (ζ z.1 * η z.2 ^ 2 * ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2) +
      Keta * ∑ j : Fin d, QG z j ^ 2 +
      (d : ℝ) * (Keta + 1 / lam) * F z ^ 2
  have hRhs : Integrable Rhs μ :=
    ((hweightedH.const_mul (lam / 4)).add (hQGsq.const_mul Keta)).add
      (hF.integrable_sq.const_mul ((d : ℝ) * (Keta + 1 / lam)))
  have hpoint : ∀ᵐ z ∂μ,
      |ζ z.1 * F z * WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z| ≤
        Rhs z := by
    filter_upwards [hmem] with z hz
    simp only [WeakGradientTimeEnergy.localizedGradientDivergence]
    rw [mul_neg, abs_neg]
    calc
      |ζ z.1 * F z * ∑ i : Fin d,
          (2 * η z.2 * spatialPartial i η z.2 * QG z i + η z.2 ^ 2 * QH z i i)| ≤
          ∑ i : Fin d, |ζ z.1 * F z *
            (2 * η z.2 * spatialPartial i η z.2 * QG z i + η z.2 ^ 2 * QH z i i)| := by
        rw [Finset.mul_sum]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (lam / 4 * (ζ z.1 * η z.2 ^ 2 * QH z i i ^ 2) +
          Keta * QG z i ^ 2 + (Keta + 1 / lam) * F z ^ 2) :=
        Finset.sum_le_sum fun i _ => localizedGradientDivergence_coordinate_young
          lam Keta (ζ z.1) (η z.2) (F z) (QG z i) (QH z i i)
          (spatialPartial i η z.2) hlam hKeta (hζnonneg _) (hζle _)
          (hηnonneg _) (hηle _) (hηderiv z.2 hz.2 i)
      _ ≤ Rhs z := by
        dsimp [Rhs]
        have hdiag : (∑ i : Fin d, QH z i i ^ 2) ≤
            ∑ j : Fin d, ∑ i : Fin d, QH z j i ^ 2 := by
          exact Finset.sum_le_sum fun j _ => Finset.single_le_sum
            (fun i _ => sq_nonneg (QH z j i)) (Finset.mem_univ j)
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h := mul_le_mul_of_nonneg_left hdiag
          (show 0 ≤ lam / 4 * (ζ z.1 * η z.2 ^ 2) from
            mul_nonneg (by positivity) (mul_nonneg (hζnonneg _) (sq_nonneg _)))
        linarith only [h]
  have h := norm_integral_le_of_norm_le hRhs
    (f := fun z => ζ z.1 * F z * WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z)
    (by simpa only [Real.norm_eq_abs] using hpoint)
  rw [Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  dsimp only [Rhs]
  rw [integral_sum_three hweightedH hQGsq hF.integrable_sq,
    Analysis.integral_sum_sq_eq_eLpNorm_sq hQG]

/-- The elementary three-term square estimate, in the subtraction orientation
used by the lower-order source. -/
private theorem sub_sub_sq_le_three (x y z : ℝ) :
    (x - y - z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y - z)]

section
variable {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d))

/-- The squared lower-order source is controlled by the prescribed restricted
`L²` bounds, without a finite-measure assumption on the cylinder. -/
private theorem lowerOrderSource_integral_sq_le (hO : IsOpen O)
    (B : TimeVelocity d → PDE.Vec d) (C0 q R : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (M : ℝ)
    (hM : 0 ≤ M)
    (hB : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d, |B z j| ≤ M)
    (hC : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, |C0 z| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hR : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R) :
    let S := Set.Ioo s₀ s₁ ×ˢ O
    let μ := timeVelocityVolumeOn S
    (∫ z in S, (R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) ^ 2 ∂volume) ≤
      3 * ((eLpNorm R 2 μ).toReal ^ 2 + M ^ 2 * (eLpNorm q 2 μ).toReal ^ 2 +
        (d : ℝ) * M ^ 2 * ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2 μ).toReal ^ 2) := by
  let S := Set.Ioo s₀ s₁ ×ˢ O
  let μ := timeVelocityVolumeOn S
  let F := fun z => R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z
  let G := fun z => ∑ j : Fin d, QG z j ^ 2
  have hGs : Integrable G μ := integrable_finset_sum _ (fun j _ => (hQG j).integrable_sq)
  have hpoint : ∀ᵐ z ∂μ, F z ^ 2 ≤ 3 * (R z ^ 2 + M ^ 2 * q z ^ 2 + (d : ℝ) * M ^ 2 * G z) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)] with z hz
    have hsq (x : ℝ) (h : |x| ≤ M) : x ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).2 h
    have hb : (∑ j, B z j ^ 2) ≤ (d : ℝ) * M ^ 2 := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hsq (B z j) (hB z hz j))
    have hg : 0 ≤ G z := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hBq := (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (B z) (QG z)).trans
      (mul_le_mul_of_nonneg_right hb hg)
    have hCq : (C0 z * q z) ^ 2 ≤ M ^ 2 * q z ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hsq (C0 z) (hC z hz)) (sq_nonneg _)
    dsimp only [F]
    linarith only [hBq, hCq, sub_sub_sq_le_three (R z) (∑ j, B z j * QG z j) (C0 z * q z)]
  have hRhs : Integrable (fun z => 3 * (R z ^ 2 + M ^ 2 * q z ^ 2 + (d : ℝ) * M ^ 2 * G z)) μ :=
    (((hR.integrable_sq.add (hq.integrable_sq.const_mul (M ^ 2))).add
      (hGs.const_mul ((d : ℝ) * M ^ 2))).const_mul 3)
  have h := integral_mono_of_nonneg (ae_of_all μ (fun z => sq_nonneg (F z))) hRhs hpoint
  rw [integral_const_mul] at h
  rw [show (∫ z, R z ^ 2 + M ^ 2 * q z ^ 2 + (d : ℝ) * M ^ 2 * G z ∂μ) = _ from by
    simpa only [one_mul] using integral_sum_three hR.integrable_sq hq.integrable_sq hGs 1 (M ^ 2) ((d : ℝ) * M ^ 2),
    Analysis.integral_real_sq_eq_eLpNorm_sq hq, Analysis.integral_real_sq_eq_eLpNorm_sq hR,
    Analysis.integral_sum_sq_eq_eLpNorm_sq hQG] at h
  exact h


/-- The literal support-indicator gradient term is bounded by the sum of the
coordinatewise restricted `L²` energies. -/
private theorem principalSupportIndicatorGradientIntegral_le_eLpNorm_sq_sum
    (QG : TimeVelocity d → PDE.Vec d) (η : PDE.Vec d → ℝ)
    (ζ : ℝ → ℝ)
    (hζnonneg : ∀ r, 0 ≤ ζ r) (hζle : ∀ r, ζ r ≤ 1)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QG z j)) :
    (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
        (fun y => ∑ j : Fin d, QG (z.1, y) j ^ 2) z.2 ∂volume) ≤
      ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2
        (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ^ 2 := by
  classical
  let μ := timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)
  let G := fun z : TimeVelocity d => ∑ j, QG z j ^ 2
  let q := fun z : TimeVelocity d => ζ z.1 * (tsupport η).indicator
    (fun y => G (z.1, y)) z.2
  have hq (z : TimeVelocity d) : 0 ≤ q z ∧ q z ≤ G z := by
    have hG : 0 ≤ G z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    by_cases hz : z.2 ∈ tsupport η
    · simpa only [q, Set.indicator_of_mem hz] using
        And.intro (mul_nonneg (hζnonneg z.1) hG) (mul_le_of_le_one_left hG (hζle z.1))
    · simpa only [q, Set.indicator_of_notMem hz, mul_zero] using And.intro le_rfl hG
  exact (integral_mono_of_nonneg (μ := μ) (ae_of_all _ (fun z => (hq z).1))
    (integrable_finset_sum _ (fun j _ => (hQG j).integrable_sq))
    (ae_of_all _ (fun z => (hq z).2))).trans_eq (Analysis.integral_sum_sq_eq_eLpNorm_sq hQG)

/-- A derivative bound needed only on the time interval controls the absolute
time-cutoff error, without a global derivative premise. -/
private theorem timeCutoffGradientIntegral_abs_div_two_le (hO : MeasurableSet O)
    (QG : TimeVelocity d → PDE.Vec d) (η : PDE.Vec d → ℝ)
    (ζ : ℝ → ℝ) (Kζ : ℝ)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hζderiv : ∀ r ∈ Set.Ioo s₀ s₁, |_root_.deriv ζ r| ≤ Kζ)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2
      (fun z => QG z j)) :
    |∫ z in Set.Ioo s₀ s₁ ×ˢ O, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ j : Fin d, QG z j ^ 2 ∂volume| / 2 ≤
      Kζ / 2 * ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2
        (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O))).toReal ^ 2 := by
  let μ := timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)
  let G := fun z : TimeVelocity d => ∑ j, QG z j ^ 2
  have hG : Integrable G μ := integrable_finset_sum _ (fun j _ => (hQG j).integrable_sq)
  have h := norm_integral_le_of_norm_le (hG.const_mul Kζ)
    (f := fun z => _root_.deriv ζ z.1 * η z.2 ^ 2 * G z) (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hO)] with z hz
      have hGz : 0 ≤ G z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hηsq : η z.2 ^ 2 ≤ 1 := by nlinarith [hηnonneg z.2, hηle z.2]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (η z.2)), abs_of_nonneg hGz]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_of_le_one_right (abs_nonneg _) hηsq).trans (hζderiv z.1 hz.1)) hGz)
  rw [Real.norm_eq_abs, integral_const_mul, Analysis.integral_sum_sq_eq_eLpNorm_sq hQG] at h
  dsimp only [G] at h
  linarith only [h]

end

/-- The weak time identity and weak principal coercivity estimate combine,
through the literal residual equation, into the pre-Young Hessian estimate. -/
private theorem weakHessian_preYoung
    {d : ℕ} (lam Lam M K : ℝ) (s₀ s₁ : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d)
    (B : TimeVelocity d → PDE.Vec d) (C0 q QW R : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, A z ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ i j k : Fin d,
      |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (hq : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQW : ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 QW)
    (hQG : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (hq_time : HasWeakTimeDerivOn (Set.Ioo s₀ s₁ ×ˢ O) q QW)
    (hq_velocity : ∀ j : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j))
    (hQG_velocity : ∀ j i : Fin d, HasWeakVelocityPartialDerivOn
      (Set.Ioo s₀ s₁ ×ˢ O) i (fun z => QG z j) (fun z => QH z j i))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η) (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y) (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d, |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ) (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁)
    (hζnonneg : ∀ r, 0 ≤ ζ r)
    (heq : ∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
      QW z + (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) +
        (∑ j : Fin d, B z j * QG z j) + C0 z * q z = R z) :
    lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
      ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2 ∂volume) ≤
      principalCoercivityConstant d lam Lam M K *
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2 ∂volume) +
      |∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
        (R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z) *
        WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z ∂volume| +
      |∫ z in Set.Ioo s₀ s₁ ×ˢ O, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, QG z i ^ 2 ∂volume| / 2 := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let F : TimeVelocity d → ℝ := fun z =>
    R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z
  let D : TimeVelocity d → ℝ := fun z => ζ z.1 *
    WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z
  have htime := WeakGradientTimeEnergy.weakGradient_timeEnergy s₀ s₁ O hO
    q QW QG QH hq hQW hQG (fun i => hQH i i) hq_time hq_velocity
    (fun i => hQG_velocity i i) η hη hηcompact hηsupport
    ζ hζ hζcompact hζsupport
  have hprincipal := weakPrincipalIntegrationByParts_coercive lam Lam M K s₀ s₁ O hO
    A q QG QH hAmeas hlam hlamLam hA hAlower hAupper hAderiv hq hQG hQH
    hq_velocity hQG_velocity η hη hηcompact hηsupport hηnonneg hηle hηderiv
    ζ hζ hζcompact hζsupport hζnonneg
  have hreoriented := residualEquation_reoriented A B QG C0 q QW R QH heq
  have assoc (f : TimeVelocity d → ℝ) :
      (fun z => ζ z.1 * f z * WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z) =
        fun z => f z * D z := by
    funext z
    simp only [D]
    ring
  have htInt := htime.1
  have ht := htime.2.2
  have hpInt := hprincipal.1
  have hp := hprincipal.2.2.2
  rw [assoc] at htInt hpInt
  simp only [assoc] at ht hp
  have hres := integrated_residual_pairing A QW F QH D hreoriented htInt hpInt
  have h := preYoung_of_time_residual_principal lam
    (principalCoercivityConstant d lam Lam M K) _ _ _ _ _ _ ht hres hp
  simpa only [← assoc F, F, S] using h

/-- The fixed-cylinder weak Hessian energy estimate obtained from the literal
residual equation. -/
theorem exists_weakHessian_energy_le_of_residual
    (d : ℕ)
    (lam Lam M Keta Kzeta : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hM : 0 ≤ M) (hKeta : 0 ≤ Keta) (hKzeta : 0 ≤ Kzeta) :
    ∃ Cenergy : ℝ, 0 ≤ Cenergy ∧
      ∀ (s₀ s₁ : ℝ)
        (O : Set (PDE.Vec d)) (_hO : IsOpen O)
        (A : TimeVelocity d → PDE.Mat d)
        (B : TimeVelocity d → PDE.Vec d)
        (C0 : TimeVelocity d → ℝ)
        (q QW R : TimeVelocity d → ℝ)
        (QG : TimeVelocity d → PDE.Vec d)
        (QH : TimeVelocity d → PDE.Mat d),
        AEStronglyMeasurable A
            (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) →
        AEStronglyMeasurable B
            (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) →
        AEStronglyMeasurable C0
            (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)) →
        (∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
          ContDiffOn ℝ 1 (fun y => A (r, y) i j) O) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
          lam • (1 : PDE.Mat d) ≤ A z) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
          A z ≤ Lam • (1 : PDE.Mat d)) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ i j k : Fin d,
          |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O, ∀ j : Fin d,
          |B z j| ≤ M) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
          |C0 z| ≤ M) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 q →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 QW →
        (∀ j : Fin d, ParabolicMemLpOn
          (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j)) →
        (∀ j i : Fin d, ParabolicMemLpOn
          (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i)) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) 2 R →
        HasWeakTimeDerivOn (Set.Ioo s₀ s₁ ×ˢ O) q QW →
        (∀ j : Fin d, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j)) →
        (∀ j i : Fin d, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O) i
            (fun z => QG z j) (fun z => QH z j i)) →
        (∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O),
          QW z +
                (∑ i : Fin d, ∑ j : Fin d,
                  A z i j * QH z j i) +
              (∑ j : Fin d, B z j * QG z j) +
            C0 z * q z = R z) →
        ∀ (η : PDE.Vec d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) η →
          HasCompactSupport η →
          tsupport η ⊆ O →
          (∀ y, 0 ≤ η y) →
          (∀ y, η y ≤ 1) →
          (∀ y ∈ O, ∀ i : Fin d,
            |spatialPartial i η y| ≤ Keta) →
        ∀ (ζ : ℝ → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ζ →
          HasCompactSupport ζ →
          tsupport ζ ⊆ Set.Ioo s₀ s₁ →
          (∀ r, 0 ≤ ζ r) →
          (∀ r, ζ r ≤ 1) →
          (∀ r ∈ Set.Ioo s₀ s₁,
            |_root_.deriv ζ r| ≤ Kzeta) →
        (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
            ζ z.1 * η z.2 ^ 2 *
              ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
            ∂volume) ≤
          Cenergy *
            ((ENNReal.toReal (eLpNorm q 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))) ^ 2 +
              (∑ j : Fin d, (ENNReal.toReal
                (eLpNorm (fun z => QG z j) 2
                  (timeVelocityVolumeOn
                    (Set.Ioo s₀ s₁ ×ˢ O)))) ^ 2) +
              (ENNReal.toReal (eLpNorm R 2
                (timeVelocityVolumeOn
                  (Set.Ioo s₀ s₁ ×ˢ O)))) ^ 2) := by
  set Cbase := principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2 +
    3 * (d : ℝ) * (Keta + 1 / lam) * (1 + M ^ 2 + (d : ℝ) * M ^ 2) with hCbase
  refine ⟨4 / lam * Cbase, ?_, ?_⟩
  · have hCpr : 0 ≤ principalCoercivityConstant d lam Lam M Keta := by
      unfold principalCoercivityConstant
      positivity
    have hbase : 0 ≤ Cbase := by
      rw [hCbase]
      positivity
    positivity
  · intro s₀ s₁ O hO A B C0 q QW R QG QH hAmeas hBmeas hCmeas hA
      hAlower hAupper hAderiv hB hC hq hQW hQG hQH hR hq_time hq_velocity
      hQG_velocity heq η hη hηcompact hηsupport hηnonneg hηle hηderiv ζ hζ
      hζcompact hζsupport hζnonneg hζle hζderiv
    let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
    let μ := timeVelocityVolumeOn S
    set E := ∫ z in S, ζ z.1 * η z.2 ^ 2 *
      ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2 ∂volume with hE
    set G := ∑ j : Fin d, (eLpNorm (fun z => QG z j) 2 μ).toReal ^ 2 with hGdef
    set Nq := (eLpNorm q 2 μ).toReal ^ 2 with hNqdef
    set NR := (eLpNorm R 2 μ).toReal ^ 2 with hNRdef
    let F : TimeVelocity d → ℝ := fun z =>
      R z - (∑ j : Fin d, B z j * QG z j) - C0 z * q z
    have hpre := weakHessian_preYoung lam Lam M Keta s₀ s₁ O hO A B C0 q QW R
      QG QH hAmeas hlam hlamLam hA hAlower hAupper hAderiv
      hq hQW hQG hQH hq_time hq_velocity hQG_velocity η hη hηcompact
      hηsupport hηnonneg hηle hηderiv ζ hζ hζcompact hζsupport hζnonneg heq
    have hprincipal := principalSupportIndicatorGradientIntegral_le_eLpNorm_sq_sum
      s₀ s₁ O QG η ζ hζnonneg hζle hQG
    have htime := timeCutoffGradientIntegral_abs_div_two_le s₀ s₁ O
      hO.measurableSet QG η ζ Kzeta hηnonneg hηle hζderiv hQG
    have hFlow := lowerOrderSource_memLp s₀ s₁ O hO B C0 q R QG M hM hBmeas hCmeas hB hC hq hQG hR
    have hsource := lowerOrder_localizedGradientDivergence_abs_le lam Keta s₀ s₁
      O hO F hFlow QG hQG QH hQH η hη.continuous hηnonneg hηle hηderiv
      ζ hζ.continuous hζnonneg hζle hlam hKeta
    have hFsq := lowerOrderSource_integral_sq_le s₀ s₁ O hO B C0 q R QG M hM hB hC hq hQG hR
    dsimp only at hFsq
    rw [← hE] at hpre hsource
    rw [← hGdef] at hprincipal htime hsource
    rw [← hNRdef, ← hNqdef, ← hGdef] at hFsq
    have hG : 0 ≤ G := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hNq : 0 ≤ Nq := sq_nonneg _
    have hNR : 0 ≤ NR := sq_nonneg _
    have hCpr : 0 ≤ principalCoercivityConstant d lam Lam M Keta := by
      unfold principalCoercivityConstant
      positivity
    have hcoef : 0 ≤ (d : ℝ) * (Keta + 1 / lam) := by positivity
    have hquarter : lam / 4 * E ≤
        (principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2) * G +
          3 * (d : ℝ) * (Keta + 1 / lam) *
            (NR + M ^ 2 * Nq + (d : ℝ) * M ^ 2 * G) := by
      have hpweighted := mul_le_mul_of_nonneg_left hprincipal hCpr
      have hFweighted := mul_le_mul_of_nonneg_left hFsq hcoef
      dsimp [F, μ, S] at hpre hprincipal htime hsource hFsq ⊢
      linarith
    let N := Nq + G + NR
    have hrest : NR + M ^ 2 * Nq + (d : ℝ) * M ^ 2 * G ≤
        (1 + M ^ 2 + (d : ℝ) * M ^ 2) * N := by
      rw [add_mul, add_mul, one_mul]
      dsimp only [N]
      gcongr <;> linarith
    have hdom := add_le_add
      (mul_le_mul_of_nonneg_left (show G ≤ N by dsimp [N]; linarith)
        (show 0 ≤ principalCoercivityConstant d lam Lam M Keta + Keta + Kzeta / 2 by positivity))
      (mul_le_mul_of_nonneg_left hrest (show 0 ≤ 3 * (d : ℝ) * (Keta + 1 / lam) by positivity))
    have hbound : lam / 4 * E ≤ Cbase * N := by
      rw [hCbase]
      linarith only [hquarter, hdom]
    have hdiv : E ≤ Cbase * N / (lam / 4) := (le_div_iff₀ (show 0 < lam / 4 by positivity)).2
      (by simpa only [mul_comm E] using hbound)
    convert hdiv using 1
    dsimp only [N]
    field_simp
    <;> ring

end HypoellipticAleksandrov.Parabolic
