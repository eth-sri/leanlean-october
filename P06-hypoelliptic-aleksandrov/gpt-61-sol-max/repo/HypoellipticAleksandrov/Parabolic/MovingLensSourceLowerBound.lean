module

public import HypoellipticAleksandrov.Parabolic.MovingLensSourceABP
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Parabolic.ABP

open private HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal from HypoellipticAleksandrov.Parabolic.ABP


/-!
# Supplied-source lower bound on a physical moving lens

This module closes the physical-coordinate contact/area argument with the
finite restricted parabolic norm of the supplied source.  It uses no
transformed operator or measure surface.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

variable (d : Nat)

private def movingLensSourceConstant  (lam kappa : Real) : Real :=
  (4 / ((d : Real) + 1)) *
    ((movingLensVelocityFootprint d kappa ^ d) /
      ((volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal * lam ^ d)) ^
        (1 / ((d : Real) + 1) : Real)




variable {d : Nat} {kappa eps tau : Real} {y : PDE.Vec d}

private theorem source_memLp_movingLensClosed

    (hkappa : 0 < kappa) (heps : 0 < eps) (htau : 0 < tau)
    (F : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hF : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y)) :
    MemLp F (parabolicExponent d)
      (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y)) := by
  let L := movingLensClosed (movingLensSignXi kappa) eps tau y

  have hLcompact : IsCompact L :=
    isCompact_movingLensClosed (by
        unfold movingLensSignXi
        positivity) heps htau.le
  have hLmeas  := hLcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict L) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hLcompact.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hLcompact.exists_bound_of_continuousOn hF
  refine MemLp.of_bound (hF.aestronglyMeasurable hLmeas) C ?_
  filter_upwards [ae_restrict_mem hLmeas] with z hz
  exact hC z hz

private theorem parabolicLpNormOn_movingLensClosed_eq_integral_abs_pow

    {F : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hFmem : MemLp F (parabolicExponent d)
      (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y))) :
    parabolicLpNormOn d F
      (movingLensClosed (movingLensSignXi kappa) eps tau y) =
      (∫ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        |F z| ^ (d + 1)) ^ (1 / ((d : Real) + 1) : Real) := by
  let sharedTerm_b2eda2aa44 := ((1 / ((d : Real) + 1) : Real))


  rw [parabolicLpNormOn, parabolicELpNormOn, _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal]
  calc
    (eLpNorm F (ENNReal.ofReal ((d : Real) + 1))
        (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y))).toReal =
      (∫ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        ‖F z‖ ^ ((d : Real) + 1)) ^ sharedTerm_b2eda2aa44 :=
      PDE.toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv (by positivity) (by
          rw [<- _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal]
          exact hFmem)
    _ = (∫ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        |F z| ^ (d + 1)) ^ sharedTerm_b2eda2aa44 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      rw [Real.norm_eq_abs,
        show ((d : Real) + 1) = ((d + 1 : Nat) : Real) by norm_num,
        Real.rpow_natCast]

private theorem movingLensSourceConstant_pos
    (d : Nat) {lam kappa : Real} (hlam : 0 < lam) (hkappa : 0 < kappa) :
    0 < movingLensSourceConstant d lam kappa := by




  unfold movingLensSourceConstant
  exact mul_pos (div_pos (by norm_num) (by positivity))
    (Real.rpow_pos_of_pos (div_pos (pow_pos (by
        unfold movingLensVelocityFootprint
        exact add_pos_of_pos_of_nonneg hkappa
          (mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (le_of_lt hkappa) _))) d) (mul_pos (PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)) (pow_pos hlam d))) _)

variable {d : Nat}

private theorem measurable_movingLensSourceSignSet_of_localC2
     {xi eps tau : Real} {y : PDE.Vec d}
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hlocal : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt Real 2 u z) :
    MeasurableSet (movingLensSourceSignSet xi eps tau y u) := by
  let sharedTerm_2953688a29 := ({z | (-velocityHessian u z).PosSemidef})
  let O  := {z | 0 < z.1 /\ z.1 < tau /\
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1}
  have hO : IsOpen O := by
    rw [show O = {z | 0 < z.1 /\
        PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} ∩
          {z | z.1 < tau} by exact (ext fun z =>
  id
    { mp := fun a => And.casesOn a fun ht0 right => And.casesOn right fun httau hspatial => ⟨⟨ht0, hspatial⟩, httau⟩,
      mpr := fun a => And.casesOn a fun left httau => And.casesOn left fun ht0 hspatial => ⟨ht0, ⟨httau, hspatial⟩⟩ })]
    exact (isOpen_movingLensPositiveSpatialStrict xi eps y).inter
      (isOpen_Iio.preimage continuous_fst)

  have huO : ContDiffOn Real 2 u O := fun z hz =>
    (hlocal z ((show O ⊆ movingLensActive xi eps tau y by
        rintro z ⟨hzpos, hzlt, hzspatial⟩
        exact ⟨hzpos, hzlt.le, hzspatial⟩) hz)).contDiffWithinAt
  have hDu : ContDiffOn Real 1 (fderiv Real u) O :=
    huO.fderiv_of_isOpen hO (by norm_num)
  have hD2u : ContDiffOn Real 0 (fderiv Real (fderiv Real u)) O :=
    hDu.fderiv_of_isOpen hO (by norm_num)

  have htime : ContinuousOn (timeDerivative u) O := by
    unfold timeDerivative
    simpa using hDu.continuousOn.clm_apply continuousOn_const
  have hhess : ContinuousOn (velocityHessian u) O := by
    change ContinuousOn ((velocityHessian u)) O
    unfold velocityHessian
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa using hD2u.continuousOn.clm_apply continuousOn_const |>.clm_apply continuousOn_const



  have hpsd : MeasurableSet (O ∩ sharedTerm_2953688a29) := by
    rw [show O ∩ sharedTerm_2953688a29 = O \ (O ∩
        (fun z => -velocityHessian u z) ⁻¹' {H : PDE.Mat d | H.PosSemidef}ᶜ) by
      ext z
      simp [sharedTerm_2953688a29]]
    exact hO.measurableSet.diff
      ((hhess.neg).isOpen_inter_preimage hO (show IsClosed {H : PDE.Mat d | H.PosSemidef} by

          have hset :
              {H : PDE.Mat d | H.PosSemidef} =
                {H : PDE.Mat d | H.IsHermitian} ∩
                  ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H.mulVec q)} := by
            ext H
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
            simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
          rw [hset]
          refine (show IsClosed {H : PDE.Mat d | H.IsHermitian} by
              have hset :
                  {H : PDE.Mat d | H.IsHermitian} =
                    ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
                ext H
                simp only [Set.mem_setOf_eq, Set.mem_iInter]
                constructor
                · intro h i j
                  exact h.apply i j
                · intro h
                  apply Matrix.IsHermitian.ext
                  intro i j
                  exact h i j
              rw [hset]
              refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
              exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)).inter (isClosed_iInter fun q => ?_)

          exact isClosed_le continuous_const (show Continuous (fun H : PDE.Mat d => dotProduct q (H.mulVec q)) from continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))).isOpen_compl).measurableSet
  rw [show movingLensSourceSignSet xi eps tau y u =
      (O ∩ {z | 0 < u z}) ∩ (O ∩ {z | 0 ≤ timeDerivative u z}) ∩
        (O ∩ sharedTerm_2953688a29) by
    ext z
    change (0 < z.1 /\ z.1 < tau /\
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 /\
      0 < u z /\ 0 ≤ timeDerivative u z /\ (-velocityHessian u z).PosSemidef) ↔
      ((z ∈ O /\ 0 < u z) /\ (z ∈ O /\ 0 ≤ timeDerivative u z)) /\
        (z ∈ O /\ (-velocityHessian u z).PosSemidef)
    constructor
    · rintro ⟨ht0, httau, hspatial, hpositivez, htimez, hpsdz⟩
      exact ⟨⟨⟨⟨ht0, httau, hspatial⟩, hpositivez⟩,
        ⟨⟨ht0, httau, hspatial⟩, htimez⟩⟩,
        ⟨⟨ht0, httau, hspatial⟩, hpsdz⟩⟩
    · rintro ⟨⟨⟨hOpositive, hpositivez⟩, ⟨hOtime, htimez⟩⟩, ⟨hOpsd, hpsdz⟩⟩
      exact ⟨hOpositive.1, hOpositive.2.1, hOpositive.2.2,
        hpositivez, htimez, hpsdz⟩]
  exact ((show MeasurableSet (O ∩ {z | 0 < u z}) from (huO.continuousOn.isOpen_inter_preimage hO isOpen_Ioi).measurableSet).inter (show MeasurableSet (O ∩ {z | 0 ≤ timeDerivative u z}) by
      rw [show O ∩ {z | 0 ≤ timeDerivative u z} =
          O \ (O ∩ (timeDerivative u) ⁻¹' Set.Iio 0) by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
          Set.mem_Iio]
        constructor
        · rintro ⟨hz, htimez⟩
          exact ⟨hz, fun hnegative => not_lt_of_ge htimez hnegative.2⟩
        · rintro ⟨hz, hnotnegative⟩
          exact ⟨hz, le_of_not_gt fun hnegative => hnotnegative ⟨hz, hnegative⟩⟩]
      exact hO.measurableSet.diff
        (htime.isOpen_inter_preimage hO isOpen_Iio).measurableSet)).inter hpsd

private theorem movingLens_wedge_le_source_lintegral
     {lam kappa eps tau : Real} {y : PDE.Vec d}
    {A : CoefficientField d} {F u : HypoellipticAleksandrov.Parabolic.ScalarField d} {M : Real}
    (hlam : 0 < lam)
    (hFcont : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z)
    (hlower : HasLowerEllipticityOn lam A
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hsub : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      parabolicOperator A u z <= F z)
    (hcoverage : movingLensSlopeInterceptWedge d
      (movingLensVelocityFootprint d kappa) M ⊆
        parabolicNormalMap u 0 ''
          movingLensSourceSignSet (movingLensSignXi kappa) eps tau y u) :
    volume (movingLensSlopeInterceptWedge d
      (movingLensVelocityFootprint d kappa) M) <=
      ∫⁻ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        ENNReal.ofReal (|F z| ^ (d + 1) /
          ((((d : Real) + 1) ^ (d + 1)) * lam ^ d)) := by
  let xi := movingLensSignXi kappa
  let L := movingLensClosed xi eps tau y
  let S := movingLensSourceSignSet xi eps tau y u
  let q : Real := ((d : Real) + 1) ^ (d + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity

  have hdenpos : 0 < q * lam ^ d := mul_pos hqpos (pow_pos hlam d)
  have harea := movingLensSlopeInterceptWedge_volume_le_lintegral_abs_det_fderiv
    hulocal hcoverage
  have hSL : S ⊆ L := by
    intro z hz
    exact movingLensActive_subset_movingLensClosed xi eps tau y
      ⟨hz.1, hz.2.1.le, hz.2.2.1⟩


  calc
    volume (movingLensSlopeInterceptWedge d
        (movingLensVelocityFootprint d kappa) M) <=
        ∫⁻ z in S,
          ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)| := harea
    _ <= ∫⁻ z in S, ENNReal.ofReal (|F z| ^ (d + 1) /
        (q * lam ^ d)) := (by
            apply MeasureTheory.setLIntegral_mono_ae
            · apply AEMeasurable.ennreal_ofReal
              exact ((hFcont.mono hSL).aemeasurable (measurable_movingLensSourceSignSet_of_localC2 hulocal)).norm.pow_const
                  (d + 1) |>.div_const _
            · exact ae_of_all _ (by
                intro z hz
                have hzActive : z ∈ movingLensActive xi eps tau y :=
                  ⟨hz.1, hz.2.1.le, hz.2.2.1⟩
                have hlo := hlower.le hzActive


                have hJ := abs_det_fderiv_parabolicNormalMap_le_source_of_signs (y₀ := 0)
                  (hulocal z hzActive) hz.2.2.2.2.1 hz.2.2.2.2.2 (posDef_of_loewner_lower hlam hlo) (hsub z hzActive)


                apply ENNReal.ofReal_le_ofReal
                calc
                  |((fderiv Real (parabolicNormalMap u 0) z).det)| <=
                      (max (F z) 0) ^ (d + 1) / (q * lam ^ d) := (by
                          calc
                            |((fderiv Real (parabolicNormalMap u 0) z).det)| <=
                                (max (F z) 0) ^ (d + 1) / (q * (coefficientAt A z).det) := hJ
                            _ <= (max (F z) 0) ^ (d + 1) / (q * lam ^ d) :=
                              div_le_div_of_nonneg_left (pow_nonneg (le_max_right _ _) _) hdenpos (mul_le_mul_of_nonneg_left (det_lower_of_loewner hlam hlo) hqpos.le))
                  _ <= |F z| ^ (d + 1) / (q * lam ^ d) :=
                    div_le_div_of_nonneg_right
                      (pow_le_pow_left₀ (le_max_right _ _)
                        (max_le (le_abs_self _) (abs_nonneg _)) _) hdenpos.le))
    _ <= ∫⁻ z in L, ENNReal.ofReal (|F z| ^ (d + 1) /
        (q * lam ^ d)) := MeasureTheory.lintegral_mono_set hSL
    _ = _ := rfl

private theorem movingLensSourceConstant_mul_rpow_pow
     {lam kappa I : Real}
    (hlam : 0 < lam) (hkappa : 0 < kappa) (hI : 0 <= I) :
    (movingLensSourceConstant d lam kappa *
      I ^ (1 / ((d : Real) + 1) : Real)) ^ (d + 1) =
      4 ^ (d + 1) * movingLensVelocityFootprint d kappa ^ d * I /
        ((((d : Real) + 1) ^ (d + 1)) *
          (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal * lam ^ d) := by
  have hp : 0 < (d : Real) + 1 := by positivity
  have homega : 0 < (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal :=
    PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)
  have hlamPow : 0 < lam ^ d := pow_pos hlam d
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    exact add_pos_of_pos_of_nonneg hkappa
      (mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (le_of_lt hkappa) _))


  have hpcast : (d : Real) + 1 = ((d + 1 : Nat) : Real) := by norm_num
  unfold movingLensSourceConstant
  rw [hpcast, mul_pow, mul_pow, one_div,
    Real.rpow_inv_natCast_pow (div_nonneg (pow_nonneg hR.le _) (mul_nonneg homega.le hlamPow.le)) (Nat.succ_ne_zero d),
    Real.rpow_inv_natCast_pow hI (Nat.succ_ne_zero d)]
  rw [div_pow]
  field_simp [hp.ne', homega.ne', hlamPow.ne', hR.ne']

private theorem movingLens_source_height_le_constant_mul_norm
     {lam kappa tau eps : Real} {y : PDE.Vec d}
    {A : CoefficientField d} {F u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hd : 0 < d) (hlam : 0 < lam) (hkappa : 0 < kappa)
    (hkappa_one : kappa <= 1) (htau : 0 < tau) (htau_kappa : tau <= kappa⁻¹)
    (heps : 0 < eps) (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y <= (d : Real) * kappa ^ (-4 : Int))
    (hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hFcont : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z)
    (hlower : HasLowerEllipticityOn lam A
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hsub : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      parabolicOperator A u z <= F z)
    (hboundary : ∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
      movingLensActive (movingLensSignXi kappa) eps tau y, u z <= 0) :
    u (tau, tau • y) <= movingLensSourceConstant d lam kappa *
      parabolicLpNormOn d F
        (movingLensClosed (movingLensSignXi kappa) eps tau y) := by
  let sharedTerm_852aa9c100 := ((1 / ((d : Real) + 1) : Real))
  let L := movingLensClosed (movingLensSignXi kappa) eps tau y
  let R := movingLensVelocityFootprint d kappa
  let omega := (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal
  let q : Real := ((d : Real) + 1) ^ (d + 1)
  let I : Real := ∫ z in L, |F z| ^ (d + 1)

  have hLcompact : IsCompact L := isCompact_movingLensClosed (show 0 <= movingLensSignXi kappa by
      unfold movingLensSignXi
      positivity) heps htau.le
  have hLmeas  := hLcompact.measurableSet
  have hFmem := source_memLp_movingLensClosed hkappa heps htau F hFcont

  have hnorm : parabolicLpNormOn d F L = I ^ sharedTerm_852aa9c100 := by
    dsimp [I, L]
    exact parabolicLpNormOn_movingLensClosed_eq_integral_abs_pow hFmem
  have hR : 0 < R := by
    dsimp [R, movingLensVelocityFootprint]
    exact add_pos_of_pos_of_nonneg hkappa
      (mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (le_of_lt hkappa) _))
  have homega : 0 < omega := by
    dsimp [omega]
    exact PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)
  have hlamPow : 0 < lam ^ d := pow_pos hlam d
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hI : 0 <= I := by
    dsimp [I]
    exact integral_nonneg fun z => pow_nonneg (abs_nonneg _) _
  by_cases hMnonpos : u (tau, tau • y) <= 0
  · calc
      u (tau, tau • y) <= 0 := hMnonpos
      _ <= movingLensSourceConstant d lam kappa * parabolicLpNormOn d F L :=
        mul_nonneg (movingLensSourceConstant_pos d hlam hkappa).le
          ((id ENNReal.toReal_nonneg))
  let M := u (tau, tau • y)
  have hM : 0 < M := lt_of_not_ge hMnonpos
  have hcoverage := movingLensSlopeInterceptWedge_subset_image_signSet_local
    d hd kappa tau eps y hkappa hkappa_one htau htau_kappa heps heps_small hy
    u hucont hulocal hboundary M hM (rfl)
  have hwedge := movingLens_wedge_le_source_lintegral hlam hFcont hulocal hlower hsub hcoverage
  let g  := fun z => |F z| ^ (d + 1) / (q * lam ^ d)

  have hgint : IntegrableOn g L  := (show ContinuousOn g L by
      apply (hFcont.norm.pow _).div continuousOn_const
      intro z hz
      exact (mul_pos hq hlamPow).ne').integrableOn_compact hLcompact

  have hreal := ENNReal.toReal_mono (show (∫⁻ z in L, ENNReal.ofReal (g z)) ≠ ∞ by
      have hfinite := (MeasureTheory.hasFiniteIntegral_iff_norm _).mp
        hgint.integrable.hasFiniteIntegral
      apply ne_of_lt
      refine (lintegral_congr_ae ?_).symm ▸ hfinite
      filter_upwards [ae_restrict_mem hLmeas] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (pow_nonneg (abs_nonneg _) _) (mul_nonneg hq.le hlamPow.le)) hwedge
  have hg_real : (∫⁻ z in L, ENNReal.ofReal (g z)).toReal =
      ∫ z in L, g z := by
    symm
    refine integral_eq_lintegral_of_nonneg_ae ?_ hgint.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hLmeas] with z hz
    exact div_nonneg (pow_nonneg (abs_nonneg _) _) (mul_nonneg hq.le hlamPow.le)
  have hpower : omega * M ^ (d + 1) /
      (4 ^ (d + 1) * R ^ d) <= I / (q * lam ^ d) := by
    rw [volume_movingLensSlopeInterceptWedge hR hM,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hM.le (by norm_num)),
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hM.le
        (mul_nonneg (by norm_num) hR.le)) _)] at hreal
    rw [hg_real] at hreal
    have hleft : (M / 4) * ((M / (4 * R)) ^ d * omega) =
        omega * M ^ (d + 1) / (4 ^ (d + 1) * R ^ d) := by
      rw [div_pow]
      field_simp [hR.ne']
      ring
    rw [hleft, integral_div] at hreal
    exact hreal



  have hrootnonneg : 0 <= movingLensSourceConstant d lam kappa *
      I ^ sharedTerm_852aa9c100 :=
    mul_nonneg (movingLensSourceConstant_pos d hlam hkappa).le
      (Real.rpow_nonneg hI _)

  calc
    u (tau, tau • y) = M := rfl
    _ <= movingLensSourceConstant d lam kappa * I ^ sharedTerm_852aa9c100 := (le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d) hrootnonneg (by
        rw [(movingLensSourceConstant_mul_rpow_pow (d := d) hlam hkappa hI)]
        exact (by
            calc
              M ^ (d + 1) =
                  (omega * M ^ (d + 1) / (4 ^ (d + 1) * R ^ d)) *
              (4 ^ (d + 1) * R ^ d / omega) := by
                field_simp [homega.ne', hR.ne']
              _ <= (I / (q * lam ^ d)) * (4 ^ (d + 1) * R ^ d / omega) :=
                mul_le_mul_of_nonneg_right hpower (div_nonneg
                  (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hR.le _)) homega.le)
              _ = 4 ^ (d + 1) * R ^ d * I / (q * omega * lam ^ d) := by
                field_simp [homega.ne', hq.ne', hlamPow.ne'])))
    _ = movingLensSourceConstant d lam kappa * parabolicLpNormOn d F L := by rw [hnorm]

/-- A nonnegative supplied source bounds the lower terminal height on a
physical moving lens by its finite restricted parabolic `L^(d + 1)` norm. -/
theorem exists_movingLens_source_lower_bound
    (d : Nat) (hd : 0 < d) (lam Lam kappa : Real)
    (hlam : 0 < lam) (hlamLam : lam <= Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa <= 1) :
    ∃ C : Real, 0 < C ∧
      ∀ (A : CoefficientField d) (U : HypoellipticAleksandrov.Parabolic.Region d)
        (F w : HypoellipticAleksandrov.Parabolic.ScalarField d) (tau eps : Real) (y : PDE.Vec d),
        0 < tau -> tau <= kappa⁻¹ -> 0 < eps ->
        2 * eps ^ 2 < kappa ^ 2 ->
        PDE.vecNormSq y <= (d : Real) * kappa ^ (-4 : Int) ->
        IsOpen U ->
        movingLensClosed (movingLensSignXi kappa) eps tau y ⊆ U ->
        IsContinuousCoefficientOn A U ->
        ContinuousOn F U ->
        ContinuousOn w (movingLensClosed (movingLensSignXi kappa) eps tau y) ->
        (∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
          ContDiffAt Real 2 w z) ->
        HasLowerEllipticityOn lam A
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        HasUpperEllipticityOn Lam A
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        IsNonnegativeOn F (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        IsParabolicSupersolutionOn A (fun z => -F z) w
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        (∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
          movingLensActive (movingLensSignXi kappa) eps tau y, 0 <= w z) ->
        -C * parabolicLpNormOn d F
          (movingLensClosed (movingLensSignXi kappa) eps tau y) <=
          w (tau, tau • y) := by
  refine ⟨movingLensSourceConstant d lam kappa,
    movingLensSourceConstant_pos d hlam hkappa, ?_⟩
  intro A U F w tau eps y htau htau_kappa heps heps_small hy hU hLU hAcont hF hwcont
    hwlocal hlower hupper hFnonneg hsuper hboundary
  let u  := fun z => -w z
  have hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y) := hwcont.neg
  have hFcont  := hF.mono hLU
  have hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z := by
    intro z hz
    exact (hwlocal z hz).neg

  have huboundary : ∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
      movingLensActive (movingLensSignXi kappa) eps tau y, u z <= 0 := by
    intro z hz
    change -w z <= 0
    linarith [hboundary z hz]
  have hheight := movingLens_source_height_le_constant_mul_norm
    hd hlam hkappa hkappa_one htau htau_kappa heps heps_small hy hucont hFcont hulocal
    hlower (show ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      parabolicOperator A u z <= F z by
        intro z hz
        have h := hsuper z hz
        change parabolicOperator A (fun q => -w q) z <= F z
        rw [parabolicOperator_neg]
        change -F z <= parabolicOperator A w z at h
        linarith) huboundary
  linarith
