module

public import HypoellipticAleksandrov.Parabolic.LocalizedGradientDivergence
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedDirection
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.productCutoff_hasCompactSupport from HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedDirection
open private HypoellipticAleksandrov.Parabolic.productCutoff_contDiff from HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedDirection


/-!
# Smooth gradient time-energy identity

This file develops the compact-support directional integration-by-parts
infrastructure for the smooth gradient time-energy identity.
-/

 public section



open MeasureTheory Set
open scoped BigOperators

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

variable {d : ℕ}

private theorem integral_mul_fderiv_apply_eq_neg_of_right_compact
     (q : TimeVelocity d)
    (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f)
    (hg : ContDiff ℝ PDE.smoothOrder g)
    (hgCompact : HasCompactSupport g) :
    (∫ z, f z * fderiv ℝ g z q
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      -∫ z, fderiv ℝ f z q * g z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  have hfCont  := hf.continuous
  have hgCont  := hg.continuous






  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hgCont).integrable_of_hasCompactSupport hgCompact.mul_left) ((hfCont.mul ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hgCompact.fderiv_apply ℝ q).mul_left) ((hfCont.mul hgCont).integrable_of_hasCompactSupport hgCompact.mul_left) (fun x _ => hf.differentiable (by simp) x)
      (fun x _ => hg.differentiable (by simp) x)

private theorem integral_restrict_eq_integral_of_eq_zero_off
     (S : HypoellipticAleksandrov.Parabolic.Region d) (hS : MeasurableSet S)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hoff : ∀ z ∉ S, f z = 0) :
    (∫ z in S, f z) = ∫ z, f z := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp_all






variable (r : HypoellipticAleksandrov.Parabolic.ScalarField d)

section
variable (hr : ContDiff ℝ PDE.smoothOrder r)

include hr in
private theorem fderiv_fderiv_apply_comm


    (z p q : TimeVelocity d) :
    fderiv ℝ (fun x => fderiv ℝ r x p) z q =
      fderiv ℝ (fun x => fderiv ℝ r x q) z p := by
  have hgrad : ContDiff ℝ PDE.smoothOrder (fderiv ℝ r) :=
    (contDiff_infty_iff_fderiv.mp hr).2
  have heval (a b : TimeVelocity d) :
      fderiv ℝ (fun x => fderiv ℝ r x a) z b =
        fderiv ℝ (fderiv ℝ r) z b a := by
    rw [fderiv_clm_apply
      (hgrad.differentiable (by simp) z)
      (differentiableAt_const (c := a))]
    rw [fderiv_const_apply]
    simp
  rw [heval p q, heval q p]
  have hrz : ContDiffAt ℝ PDE.smoothOrder r z := hr.contDiffAt

  exact ((hrz.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).isSymmSndFDerivAt (by norm_num)).eq q p

section
variable (i : Fin d)

include hr
private theorem velocity_time_mixed_comm


     (z : TimeVelocity d) :
    fderiv ℝ (timeDerivative r) z (0, Pi.single i 1) =
      fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) := by
  solve_by_elim (maxDepth := 4) [timeDerivative, velocityGradient, fderiv_fderiv_apply_comm]

private theorem velocityGradient_component_contDiff

      :
    ContDiff ℝ PDE.smoothOrder (fun z => velocityGradient r z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hr).2.clm_apply contDiff_const
end


include hr in
private theorem weightedVelocityGradient_contDiff


    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (i : Fin d) :
    ContDiff ℝ PDE.smoothOrder
      (fun z : TimeVelocity d =>
        ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) := (_root_.HypoellipticAleksandrov.Parabolic.productCutoff_contDiff ζ η hζ hη).mul
    (velocityGradient_component_contDiff r hr i)
end


private theorem weightedVelocityGradient_hasCompactSupport

    (η : PDE.ScalarField d) (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζCompact : HasCompactSupport ζ)
    (i : Fin d) :
    HasCompactSupport
      (fun z : TimeVelocity d =>
        ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) := (_root_.HypoellipticAleksandrov.Parabolic.productCutoff_hasCompactSupport ζ η hζCompact hηCompact).mul_right

private theorem fderiv_timeVelocityCutoff_spatial
     (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) z
        (0, Pi.single i 1) =
      ζ z.1 * (2 * η z.2 * spatialPartial i η z.2) := by
  let sharedTerm_7871300b36 := ((fun x : TimeVelocity d => ζ x.1))
  have hζDiff : DifferentiableAt ℝ sharedTerm_7871300b36 z :=
    (hζ.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hηDiff : DifferentiableAt ℝ (fun x : TimeVelocity d => η x.2) z :=
    (hη.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) =
      (fun x => ζ x.1) * (fun x => η x.2) ^ 2 by rfl]
  rw [fderiv_mul hζDiff (hηDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change ζ z.1 * fderiv ℝ (fun x : TimeVelocity d => η x.2 ^ 2) z
      (0, Pi.single i 1) + η z.2 ^ 2 *
      fderiv ℝ sharedTerm_7871300b36 z (0, Pi.single i 1) = _
  rw [fderiv_fun_pow 2 hηDiff]
  have hζzero : fderiv ℝ sharedTerm_7871300b36 z
      (0, Pi.single i 1) = 0 := by
    change fderiv ℝ (ζ ∘ Prod.fst) z (0, Pi.single i 1) = 0
    rw [fderiv_comp z (hζ.differentiable (by simp) z.1)
      (differentiableAt_fst )]
    rw [fderiv_fst]
    simp
  have hηeval : fderiv ℝ (fun x : TimeVelocity d => η x.2) z
      (0, Pi.single i 1) = spatialPartial i η z.2 := by
    change fderiv ℝ (η ∘ Prod.snd) z (0, Pi.single i 1) = _
    rw [fderiv_comp z (hη.differentiable (by simp) z.2)
      (differentiableAt_snd )]
    rw [fderiv_snd]
    rfl
  simp_all

section
variable (r : HypoellipticAleksandrov.Parabolic.ScalarField d) (hr : ContDiff ℝ PDE.smoothOrder r)

include hr
private theorem fderiv_velocityGradient_component_spatial

    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x => velocityGradient r x i) z (0, Pi.single i 1) =
      velocityHessian r z i i := by
  unfold velocityGradient velocityHessian

  rw [fderiv_clm_apply
    (((contDiff_infty_iff_fderiv.mp hr).2).differentiable (by simp) z)
    (differentiableAt_const (c := ((0, Pi.single i 1) : TimeVelocity d)))]
  rw [fderiv_const_apply]
  simp

private theorem fderiv_weightedVelocityGradient_spatial

    (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d =>
      ζ x.1 * η x.2 ^ 2 * velocityGradient r x i) z
        (0, Pi.single i 1) =
      ζ z.1 *
        (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
          η z.2 ^ 2 * velocityHessian r z i i) := by
  let c : HypoellipticAleksandrov.Parabolic.ScalarField d := fun x => ζ x.1 * η x.2 ^ 2
  let v  := fun x => velocityGradient r x i


  change fderiv ℝ (c * v) z (0, Pi.single i 1) = _
  rw [fderiv_mul ((_root_.HypoellipticAleksandrov.Parabolic.productCutoff_contDiff ζ η hζ hη).differentiable (by simp) z) ((velocityGradient_component_contDiff r hr i).differentiable (by simp) z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, c, v]
  rw [fderiv_timeVelocityCutoff_spatial η hη ζ hζ i z,
    fderiv_velocityGradient_component_spatial r hr i z]
  ring
end


private theorem fderiv_timeVelocityCutoff_time
     (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) z (1, 0) =
      _root_.deriv ζ z.1 * η z.2 ^ 2 := by
  let sharedTerm_06e721ea1b := ((fun x : TimeVelocity d => ζ x.1))
  have hζDiff : DifferentiableAt ℝ sharedTerm_06e721ea1b z :=
    (hζ.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hηDiff : DifferentiableAt ℝ (fun x : TimeVelocity d => η x.2) z :=
    (hη.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) =
      (fun x => ζ x.1) * (fun x => η x.2) ^ 2 by rfl]
  rw [fderiv_mul hζDiff (hηDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change ζ z.1 * fderiv ℝ (fun x : TimeVelocity d => η x.2 ^ 2) z (1, 0) +
      η z.2 ^ 2 * fderiv ℝ sharedTerm_06e721ea1b z (1, 0) = _
  rw [fderiv_fun_pow 2 hηDiff]
  have hηzero : fderiv ℝ (fun x : TimeVelocity d => η x.2) z (1, 0) = 0 := by
    change fderiv ℝ (η ∘ Prod.snd) z (1, 0) = 0
    rw [fderiv_comp z (hη.differentiable (by simp) z.2)
      (differentiableAt_snd ), fderiv_snd]
    simp
  have hζeval : fderiv ℝ sharedTerm_06e721ea1b z (1, 0) =
      _root_.deriv ζ z.1 := by
    change fderiv ℝ (ζ ∘ Prod.fst) z (1, 0) = _
    rw [fderiv_comp z (hζ.differentiable (by simp) z.1)
      (differentiableAt_fst ), fderiv_fst]
    rfl
  rw [hζeval]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, hηzero, mul_zero, smul_zero, zero_add]
  ring

section
variable (r : HypoellipticAleksandrov.Parabolic.ScalarField d) (hr : ContDiff ℝ PDE.smoothOrder r)

include hr in
private theorem timeDerivative_contDiff
      :
    ContDiff ℝ PDE.smoothOrder (timeDerivative r) := by
  unfold timeDerivative
  exact (contDiff_infty_iff_fderiv.mp hr).2.clm_apply contDiff_const

variable (η : PDE.ScalarField d) (hη : ContDiff ℝ PDE.smoothOrder η) (hηCompact : HasCompactSupport η) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ PDE.smoothOrder ζ) (hζCompact : HasCompactSupport ζ)

include hr hη hηCompact hζ hζCompact
private theorem global_coordinate_timeEnergy


    (i : Fin d) :
    2 * (∫ z : TimeVelocity d,
      timeDerivative r z *
        (-(ζ z.1 *
          (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
            η z.2 ^ 2 * velocityHessian r z i i)))) =
      -(∫ z : TimeVelocity d,
        _root_.deriv ζ z.1 * η z.2 ^ 2 * velocityGradient r z i ^ 2) := by
  let sharedTerm_6417f74c76 := (∫ z : TimeVelocity d,
    ζ z.1 * η z.2 ^ 2 * fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) * velocityGradient r z i ∂volume)
  let sharedTerm_14abcbf946 := (∫ z : TimeVelocity d, velocityGradient r z i ^ 2 * (_root_.deriv ζ z.1 * η z.2 ^ 2) ∂volume)
  let sharedTerm_1f66282431 := (∫ z : TimeVelocity d,
    timeDerivative r z *
      (ζ z.1 *
        (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i + η z.2 ^ 2 * velocityHessian r z i i)) ∂volume)
  let sharedTerm_be38e9fe51 := (∫ z : TimeVelocity d,
    fderiv ℝ (timeDerivative r) z (0, Pi.single i 1) * (ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) ∂volume)
  let sharedTerm_bb6f47c620 := ((fun x => velocityGradient r x i))
  let w : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * η z.2 ^ 2
  let v  := fun z => velocityGradient r z i
  let g  := fun z => w z * v z


  have hspatial := integral_mul_fderiv_apply_eq_neg_of_right_compact
    ((0, Pi.single i 1) ) _ g
    (timeDerivative_contDiff r hr) (weightedVelocityGradient_contDiff r hr η hη ζ hζ i) (weightedVelocityGradient_hasCompactSupport r η hηCompact ζ hζCompact i)


  have hvSmooth  :=
    velocityGradient_component_contDiff r hr i
  have htime := integral_mul_fderiv_apply_eq_neg_of_right_compact
    ((1, 0) : TimeVelocity d) (fun z => v z ^ 2) w
    (hvSmooth.pow 2) (_root_.HypoellipticAleksandrov.Parabolic.productCutoff_contDiff ζ η hζ hη) (_root_.HypoellipticAleksandrov.Parabolic.productCutoff_hasCompactSupport ζ η hζCompact hηCompact)
  have hspatial' :
      (sharedTerm_1f66282431) =
        -(sharedTerm_be38e9fe51) := by
    simpa only [g, w, v, fderiv_weightedVelocityGradient_spatial r hr η hη ζ hζ i]
      using hspatial
  have htime' :
      (sharedTerm_14abcbf946) =
        -(∫ z : TimeVelocity d,
          (2 * ζ z.1 * η z.2 ^ 2 *
            fderiv ℝ sharedTerm_bb6f47c620 z (1, 0) *
              velocityGradient r z i)) := by
    calc
      (sharedTerm_14abcbf946) =
          ∫ z, (fun x => v x ^ 2) z * fderiv ℝ w z (1, 0) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          dsimp [w, v]
          rw [fderiv_timeVelocityCutoff_time η hη ζ hζ z]
      _ = -(∫ z, fderiv ℝ (fun x => v x ^ 2) z (1, 0) * w z) := htime
      _ = -(∫ z, 2 * ζ z.1 * η z.2 ^ 2 *
          fderiv ℝ sharedTerm_bb6f47c620 z (1, 0) *
            velocityGradient r z i) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          dsimp [w, v]
          rw [fderiv_fun_pow 2 (hvSmooth.differentiable (by simp) z)]
          simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
            nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
          ring
  have hleftNeg :
      (∫ z : TimeVelocity d,
        timeDerivative r z *
          -(ζ z.1 *
            (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
              η z.2 ^ 2 * velocityHessian r z i i))) =
        -(sharedTerm_1f66282431) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by ring
  rw [hleftNeg, hspatial', neg_neg]
  have hmixed (z : TimeVelocity d)  :=
    velocity_time_mixed_comm r hr i z
  have hpair :
      (sharedTerm_be38e9fe51) =
        sharedTerm_6417f74c76 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [hmixed z]
      ring
  rw [hpair]
  have htimeNorm :
      (sharedTerm_14abcbf946) =
        -(2 * sharedTerm_6417f74c76) := by
    calc
      _ = -(∫ z : TimeVelocity d, 2 *
          (ζ z.1 * η z.2 ^ 2 *
            fderiv ℝ sharedTerm_bb6f47c620 z (1, 0) *
              velocityGradient r z i)) := by
        rw [htime']
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by ring
      _ = _ := by rw [integral_const_mul]
  calc
    2 * sharedTerm_6417f74c76 =
        -(sharedTerm_14abcbf946) := by linarith
    _ = -(∫ z, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        velocityGradient r z i ^ 2) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

private theorem global_timeEnergy

     :
    2 * (∫ z : TimeVelocity d,
      ζ z.1 * timeDerivative r z *
        localizedGradientDivergence η
          ((velocityGradient r))
          ((velocityHessian r)) z) =
      -(∫ z : TimeVelocity d,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d, velocityGradient r z i ^ 2) := by
  let L  := fun i z =>
    timeDerivative r z *
      -(ζ z.1 *
        (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
          η z.2 ^ 2 * velocityHessian r z i i))
  let R  := fun i z =>
    _root_.deriv ζ z.1 * η z.2 ^ 2 * velocityGradient r z i ^ 2
  have hLInt (i : Fin d) : Integrable (L i) := by
    let g  := fun z =>
      ζ z.1 * η z.2 ^ 2 * velocityGradient r z i



    have hbase : Integrable (fun z  =>
        timeDerivative r z * fderiv ℝ g z (0, Pi.single i 1)) :=
      ((timeDerivative_contDiff r hr).continuous.mul
        (((weightedVelocityGradient_contDiff r hr η hη ζ hζ i).continuous_fderiv (by simp)).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
          ((weightedVelocityGradient_hasCompactSupport r η hηCompact ζ hζCompact i).fderiv_apply ℝ (0, Pi.single i 1)).mul_left
    refine hbase.neg.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp [L, g]
    rw [fderiv_weightedVelocityGradient_spatial r hr η hη ζ hζ i]
    ring
  have hRInt (i : Fin d) : Integrable (R i) := by
    let w : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * η z.2 ^ 2
    let v  := fun z => velocityGradient r z i




    have hbase : Integrable (fun z : TimeVelocity d =>
        v z ^ 2 * fderiv ℝ w z (1, 0)) :=
      (((velocityGradient_component_contDiff r hr i).pow 2).continuous.mul
        (((_root_.HypoellipticAleksandrov.Parabolic.productCutoff_contDiff ζ η hζ hη).continuous_fderiv (by simp)).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
          ((_root_.HypoellipticAleksandrov.Parabolic.productCutoff_hasCompactSupport ζ η hζCompact hηCompact).fderiv_apply ℝ (1, 0)).mul_left
    refine hbase.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp [R, w, v]
    rw [fderiv_timeVelocityCutoff_time η hη ζ hζ z]
    ring
  calc
    2 * (∫ z : TimeVelocity d,
        ζ z.1 * timeDerivative r z *
          localizedGradientDivergence η
            ((velocityGradient r))
            ((velocityHessian r)) z) =
        2 * ∫ z : TimeVelocity d, ∑ i : Fin d, L i z := by
      apply congrArg (fun x : ℝ => 2 * x)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [localizedGradientDivergence, L]
        rw [← Finset.sum_neg_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = ∑ i : Fin d, 2 * ∫ z : TimeVelocity d, L i z := by
      rw [integral_finset_sum Finset.univ (fun i _ => hLInt i), Finset.mul_sum]
    _ = ∑ i : Fin d, -(∫ z : TimeVelocity d, R i z) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact global_coordinate_timeEnergy r hr η hη hηCompact ζ hζ hζCompact i
    _ = -(∑ i : Fin d, ∫ z : TimeVelocity d, R i z) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ z : TimeVelocity d, ∑ i : Fin d, R i z) := by
      rw [integral_finset_sum Finset.univ (fun i _ => hRInt i)]
    _ = -(∫ z : TimeVelocity d,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d, velocityGradient r z i ^ 2) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [R, Finset.mul_sum]
end


/-- Smooth compactly supported gradient time-energy identity on a literal
product cylinder. -/
theorem smoothGradient_timeEnergy
     (s₀ s₁ : ℝ)
    (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (r : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hr : ContDiff ℝ PDE.smoothOrder r)
    (η : PDE.ScalarField d)
    (hη : ContDiff ℝ PDE.smoothOrder η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ PDE.smoothOrder ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * timeDerivative r z *
          localizedGradientDivergence η
            ((velocityGradient r))
            ((velocityHessian r)) z) =
      -(∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d, velocityGradient r z i ^ 2) := by
  let S  := Set.Ioo s₀ s₁ ×ˢ O
  have hS : MeasurableSet S := measurableSet_Ioo.prod hO.measurableSet
  let F  := fun z =>
    ζ z.1 * timeDerivative r z *
      localizedGradientDivergence η
        ((velocityGradient r))
        ((velocityHessian r)) z
  let G  := fun z =>
    _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, velocityGradient r z i ^ 2


  have hFrestrict  :=
    integral_restrict_eq_integral_of_eq_zero_off S hS F (by
        intro z hz
        by_cases ht : z.1 ∈ Set.Ioo s₀ s₁
        · have hv : z.2 ∉ O := by
            intro hv
            exact hz ⟨ht, hv⟩
          have hnot  := fun hmem => hv (hηsupport hmem)
          have hzero  := image_eq_zero_of_notMem_tsupport hnot
          simp [F, localizedGradientDivergence, hzero]
        · have hnot  := fun hmem => ht (hζsupport hmem)
          have hzero  := image_eq_zero_of_notMem_tsupport hnot
          simp [F, hzero])
  have hGrestrict  :=
    integral_restrict_eq_integral_of_eq_zero_off S hS G (by
        intro z hz
        by_cases ht : z.1 ∈ Set.Ioo s₀ s₁
        · have hv : z.2 ∉ O := by
            intro hv
            exact hz ⟨ht, hv⟩

          have hzero  := image_eq_zero_of_notMem_tsupport (fun hmem => hv (hηsupport hmem))
          simp [G, hzero]
        ·
          have hzero : _root_.deriv ζ z.1 = 0 := by
            rw [← fderiv_apply_one_eq_deriv, fderiv_of_notMem_tsupport ℝ (fun hmem => ht (hζsupport hmem))]
            rfl
          simp [G, hzero])
  change 2 * (∫ z in S, F z) = -(∫ z in S, G z)
  rw [hFrestrict, hGrestrict]
  exact global_timeEnergy r hr η hη hηcompact ζ hζ hζcompact

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
