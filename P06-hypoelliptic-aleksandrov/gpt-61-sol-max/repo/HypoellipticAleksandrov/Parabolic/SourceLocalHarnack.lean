module

public import HypoellipticAleksandrov.Parabolic.SourceLevelGrowth
public import HypoellipticAleksandrov.Parabolic.SourceForwardPropagation
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry
public import HypoellipticAleksandrov.Parabolic.PeakSelection
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Measure.InkSpotsSelection
import all HypoellipticAleksandrov.Parabolic.SourceDensityPositivePropagation
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.parabolicLpNormOn_mono_of_continuousOn from HypoellipticAleksandrov.Parabolic.SourceDensityPositivePropagation
open private HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed from HypoellipticAleksandrov.Measure.InkSpotsSelection


/-!
# Carrier-local source-aware parabolic Harnack estimate

This module combines the source density, level-growth, peak-selection,
and forward-propagation interfaces on one compact carrier.
-/

 public section

open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

section

variable {d : ℕ}




private theorem low_density_of_not_high_density  {R eps t0 beta : ℝ}
    {v0 : PDE.Vec d} (_hR : 0 < R) (U : HypoellipticAleksandrov.Parabolic.Region d)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (_hU : IsOpen U)
    (hQU : parabolicBox 1 R t0 v0 ⊆ U) (hq : ContDiffOn ℝ 2 q U)
    (hnot : ¬ beta * ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
        (parabolicBox 1 R t0 v0 ∩ {z | eps ≤ q z})).toReal) :
    (1 - beta) * ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
        (parabolicBox 1 R t0 v0 ∩ {z | q z ≤ eps})).toReal := by
  let Q := parabolicBox 1 R t0 v0
  let L  := Q ∩ {z | q z < eps}
  let H  := Q ∩ {z | eps ≤ q z}
  have hL : MeasurableSet L := by
    have hcont  := hq.continuousOn.mono hQU
    change MeasurableSet (Q ∩ q ⁻¹' Iio eps)
    exact (hcont.isOpen_inter_preimage (isOpen_parabolicBox 1 R t0 v0)
      isOpen_Iio).measurableSet
  have hQfinite : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) Q ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono _root_.HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed)
  have hLsubset : L ⊆ Q := fun _ hz ↦ hz.1
  have hinter  := inter_eq_right.mpr hLsubset
  have hdiff : Q \ L = H := by
    ext z
    simp only [L, H, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · simp_all
    · simp_all
  have hdecomp : (volume L).toReal + (volume H).toReal = (volume Q).toReal := by
    simpa only [Measure.real, hinter, hdiff] using
      (measureReal_inter_add_diff   hL hQfinite)

  have hlow : (1 - beta) * (volume Q).toReal < (volume L).toReal := by
    nlinarith
  have hsubset : L ⊆ Q ∩ {z | q z ≤ eps} := by
    intro z hz
    exact ⟨hz.1, (show q z < eps from hz.2).le⟩
  have htargetFinite : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      (Q ∩ {z | q z ≤ eps}) ≠ ⊤ :=
    ne_top_of_le_ne_top hQfinite (measure_mono fun _ hz ↦ hz.1)
  exact hlow.le.trans (ENNReal.toReal_mono htargetFinite (measure_mono hsubset))

private theorem parabolicLpNormOn_abs  (F : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (S : HypoellipticAleksandrov.Parabolic.Region d) (hF : AEStronglyMeasurable F (volume.restrict S)) :
    parabolicLpNormOn d (fun z ↦ |F z|) S = parabolicLpNormOn d F S := (id
  (id
    (congrArg ENNReal.toReal
      (eLpNorm_congr_enorm_ae (AEStronglyMeasurable.norm hF) hF (Filter.univ_mem' (id fun z => Real.enorm_abs (F z)))))))




variable {B : CoefficientField d} {F q : HypoellipticAleksandrov.Parabolic.ScalarField d} {V : HypoellipticAleksandrov.Parabolic.Region d}

private theorem supersolution_of_equation_abs
    (heq : ∀ z ∈ V, parabolicOperator B q z = F z) :
    IsParabolicSupersolutionOn B (fun z ↦ -|F z|) q V := by
  intro z hz
  rw [heq z hz]
  exact neg_abs_le (F z)

private theorem equation_add_const   {e : ℝ}
    (heq : ∀ z ∈ V, parabolicOperator B q z = F z) :
    ∀ z ∈ V, parabolicOperator B (fun y ↦ q y + e) z = F z := by
  intro z hz
  rw [parabolicOperator_add_const, heq z hz]

/-- A source-aware positive local parabolic Harnack estimate on one compact carrier. -/
theorem exists_source_local_parabolic_harnack_positive
    (d : Nat) (hd : 1 ≤ d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) :
    ∃ hBox C : Real, 0 < hBox ∧ hBox ≤ 1 ∧ 0 < C ∧
      ∀ (K U : HypoellipticAleksandrov.Parabolic.Region d) (B : CoefficientField d)
        (q F : HypoellipticAleksandrov.Parabolic.ScalarField d),
        IsCompact K → K ⊆ U → IsOpen U →
        parabolicClosedBox 2 2 0 0 ⊆ K →
        IsContinuousCoefficientOn B U → ContDiffOn Real 2 q U →
        ContinuousOn F U → IsNonnegativeOn q K →
        HasLowerEllipticityOn lam B K → HasUpperEllipticityOn Lam B K →
        (∀ x ∈ K, parabolicOperator B q x = F x) →
        0 < q (4, (0 )) →
        ∀ (j : Nat) (v : PDE.Vec d),
          v ∈ velocityCube (0 : PDE.Vec d) 1 →
          hBox * q (4, (0 )) ≤
            q (localHarnackTerminalApprox j, v) +
              C * parabolicLpNormOn d F K := by
  let sharedTerm_fa4e417182 := ((parabolicBox 2 2 (0 ) (0 : PDE.Vec d)))
  let sharedTerm_bcece2f0cb := (((d : ℝ) / ((d : ℝ) + 1)))
  have hd' : 0 < d := by omega
  obtain ⟨delta, hdelta, m, hm, CP, hCP, hprop⟩ :=
    exists_forward_propagation_source_constants d hd' lam Lam (1 / 2)
      hlam hlamLam (by norm_num) (by norm_num)
  let gStar : ℝ := 1 - 1 / (4 * (2 : ℝ) ^ m)
  have hpow0 : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hpow1 : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hden0 : 0 < 4 * (2 : ℝ) ^ m := mul_pos (by norm_num) hpow0
  have hden1 : 1 < 4 * (2 : ℝ) ^ m := by nlinarith
  have hfrac_lt_one  :=
    (div_lt_one₀ hden0).mpr hden1
  have hgStar0 : 0 < gStar := by
    dsimp [gStar]
    exact sub_pos.mpr hfrac_lt_one
  have hgStar1 : gStar < 1 := by
    dsimp [gStar]
    exact sub_lt_self 1 (div_pos (by norm_num) hden0)
  have hratio_id :
      (2 - gStar) / (2 * (1 - gStar)) = 2 * (2 : ℝ) ^ m + 1 / 2 := by
    dsimp [gStar]
    field_simp [hden0.ne']
    ring
  obtain ⟨rho, hrho0, hrho1, CStar, hCStar, hdtpStar⟩ :=
    exists_sourceDensityToPoint_near_one d hd' lam hlam Lam hlamLam
      gStar hgStar0 hgStar1
  let beta : ℝ := 1 - rho
  have hbeta0  := sub_pos.mpr hrho1
  have hbeta1  := sub_lt_self 1 hrho0
  have honeSubBeta : 1 - beta = rho := by
    dsimp [beta]
    ring
  let kappaLG : ℝ := CStar / (1 - gStar)
  have hkappaLG0  := div_pos hCStar (sub_pos.mpr hgStar1)
  let aPeak : ℝ := (2 : ℝ) ^ m + 1 / 2
  have haPeak : 0 < aPeak := by positivity
  let H : ℝ := 1 + 2 * kappaLG / aPeak
  have hH : 0 < H := by positivity
  obtain ⟨gBeta, Cbeta, hgBeta0, _hgBeta1, hCbeta, hdtpBeta⟩ :=
    exists_sourceDensityToPoint_positive d hd' lam hlam Lam hlamLam beta hbeta0 hbeta1
  let p : ℝ := sharedTerm_bcece2f0cb
  have hp : 0 ≤ p := by
    dsimp [p]
    positivity
  let c : ℝ := delta * (1 / 8 : ℝ) ^ m * (gBeta / 2)
  let hBox : ℝ := min 1 c
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hhBox0 : 0 < hBox := lt_min (by norm_num) hc
  have hhBox1 : hBox ≤ 1 := min_le_left _ _
  let C : ℝ := H + Cbeta + CP * (2 : ℝ) ^ p
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F hKcompact hKU hU hworkClosed hB hq hF hqnonneg hlowerK hupperK
    heqK hsourcePos j v hv
  let A : ℝ := parabolicLpNormOn d F K
  let G  := fun z ↦ |F z|
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hG  := hF.abs
  have hworkOpen : IsOpen sharedTerm_fa4e417182 :=
    isOpen_parabolicBox 2 2 0 0
  have hworkOpenK : sharedTerm_fa4e417182 ⊆ K :=
    _root_.HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed.trans hworkClosed

  have hcontPeak  :=
    hq.continuousOn.mono
      (backwardParabolicClosedBox_one_four_subset_normalizedOpenBox.trans hworkOpenK |>.trans hKU)
  obtain ⟨t1, v1, r0, hpeakPoint, hr0eq, _hpeakMax, hr0lt, hweight, hu1,
    hpeakNested⟩ := exists_weighted_backward_peak m hm q hcontPeak hsourcePos
  let s : ℝ := (1 - r0) / 2
  let u1 : ℝ := q (t1, v1)
  let M : ℝ := (2 : ℝ) ^ m * u1
  let tBase : ℝ := t1 - s ^ 2
  have hr0nonneg : 0 ≤ r0 := by
    rw [hr0eq, backwardParabolicRadius]
    exact le_max_of_le_left (by
      rw [show velocitySupNorm (v1 - 0) = ‖v1‖ by
        simp only [velocitySupNorm_eq_norm, sub_zero]]
      exact norm_nonneg _)
  have hs : 0 < s := by
    dsimp [s]
    exact selected_backward_radius_pos hr0lt
  have hsOne : s ≤ 1 := by
    dsimp [s]
    linarith
  have hspow  := Real.rpow_le_one hs.le hsOne hp
  have hu1' : 0 < u1 := by exact hu1
  have hbasePow : (1 - r0) ^ m ≤ 1 := by
    apply pow_le_one₀
    · linarith
    · linarith
  have hweightToU1 : q (4, (0 )) ≤ u1 := by
    calc
      q (4, (0 )) ≤ (1 - r0) ^ m * u1 := hweight
      _ ≤ 1 * u1 := mul_le_mul_of_nonneg_right hbasePow hu1'.le
      _ = u1 := one_mul _
  have hclosedSmall : parabolicClosedBox 1 s tBase v1 ⊆ K := by
    intro z hz
    apply hworkOpenK
    rw [← backwardParabolicClosedBox_eq_parabolicClosedBox s t1 v1] at hz
    exact selected_backwardParabolicClosedBox_subset_normalizedOpenBox hpeakPoint hr0eq hr0lt hz
  have hopenSmall  :=
    _root_.HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed.trans hclosedSmall
  have hclosedSmallU  := hclosedSmall.trans hKU
  have hopenSmallU  := hopenSmall.trans hKU
  have hM : ∀ z ∈ parabolicClosedBox 1 s tBase v1, q z ≤ M := by
    intro z hz
    change q z ≤ (2 : ℝ) ^ m * q (t1, v1)
    rw [← backwardParabolicClosedBox_eq_parabolicClosedBox s t1 v1] at hz
    exact hpeakNested z hz
  have htop : u1 ≤ q (tBase + s ^ 2, v1) := by
    dsimp [u1, tBase]
    apply le_of_eq
    congr 1
    ring_nf
  have hnormSmall : parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ A := by
    calc
      parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ parabolicLpNormOn d G K :=
        _root_.HypoellipticAleksandrov.Parabolic.parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl hopenSmall
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  suffices hhighCase : H * A < q (4, (0 )) →
      hBox * q (4, (0 )) ≤
        q (localHarnackTerminalApprox j, v) + C * parabolicLpNormOn d F K by
    let sharedTerm_718c6a67da := (q (4, (0 )))
    by_cases hhigh : H * A < sharedTerm_718c6a67da
    · exact hhighCase hhigh
    · have htargetK  :=
        hworkOpenK (localHarnackTerminalApprox_mem_normalizedOpenBox j hv)
      have htargetNonneg  := hqnonneg _ htargetK
      have hsourceBound  := le_of_not_gt hhigh
      have hHC : H ≤ C := by
        have hCPpow : 0 ≤ CP * (2 : ℝ) ^ p :=
          mul_nonneg hCP.le (Real.rpow_nonneg (by norm_num) _)
        dsimp [C]
        exact (le_add_of_nonneg_right hCbeta).trans (le_add_of_nonneg_right hCPpow)
      have hCA  := mul_le_mul_of_nonneg_right hHC hA
      calc
        hBox * sharedTerm_718c6a67da ≤ hBox * (H * A) :=
          mul_le_mul_of_nonneg_left hsourceBound hhBox0.le
        _ ≤ H * A := by nlinarith [hH, hA]
        _ ≤ C * A := hCA
        _ ≤ q (localHarnackTerminalApprox j, v) + C * A :=
          le_add_of_nonneg_left htargetNonneg
  intro hhigh
  have hhighDensity : beta * ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      (parabolicBox 1 s tBase v1)).toReal ≤
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
        (parabolicBox 1 s tBase v1 ∩ {z | u1 / 2 ≤ q z})).toReal := by
    by_contra hnot
    have hLow := low_density_of_not_high_density hs U q hU hopenSmallU hq hnot
    rw [honeSubBeta] at hLow
    have hgrowth := source_level_growth_of_low_set_density hdtpStar hs hu1' hgStar1
      U B F q hU hclosedSmallU hB hq hF
      (hlowerK.mono hopenSmall) (hupperK.mono hopenSmall)
      (fun z hz ↦ heqK z (hopenSmall hz)) hM htop hLow
    have hgrowth' : aPeak * u1 ≤ kappaLG * s ^ p *
        parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := by
      rw [hratio_id] at hgrowth
      have hgrowth'' : (2 * (2 : ℝ) ^ m + 1 / 2) * u1 ≤
          (2 : ℝ) ^ m * u1 + kappaLG * s ^ p *
            parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := by
        simpa only [M, kappaLG, p, mul_comm] using hgrowth
      calc
        aPeak * u1 = (2 * (2 : ℝ) ^ m + 1 / 2) * u1 - (2 : ℝ) ^ m * u1 := by
          ring
        _ ≤ kappaLG * s ^ p * parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := by
          linarith only [hgrowth'']
    have hnormSmallF : parabolicLpNormOn d F (parabolicBox 1 s tBase v1) ≤ A := by
      rw [← parabolicLpNormOn_abs F _
        ((hF.mono hopenSmallU).aestronglyMeasurable
          (isOpen_parabolicBox 1 s tBase v1).measurableSet)]
      exact hnormSmall
    have hmain : aPeak * u1 ≤ kappaLG * A := by
      calc
        aPeak * u1 ≤ kappaLG * s ^ p *
            parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := hgrowth'
        _ ≤ kappaLG * A := by
          let sharedTerm_2d51dedd39 := (parabolicLpNormOn d F (parabolicBox 1 s tBase v1))
          have hterm : s ^ p * sharedTerm_2d51dedd39 ≤ A := by
            calc
              s ^ p * sharedTerm_2d51dedd39 ≤
                  1 * sharedTerm_2d51dedd39 := mul_le_mul_of_nonneg_right hspow ENNReal.toReal_nonneg
              _ ≤ A := by simpa
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm hkappaLG0.le
    by_cases hAzero : A = 0
    · have hzero : aPeak * u1 ≤ 0 := by
        calc
          aPeak * u1 ≤ kappaLG * A := hmain
          _ = 0 := by rw [hAzero, mul_zero]
      exact (not_le_of_gt (mul_pos haPeak hu1')) hzero
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      have hstrict : kappaLG * A < aPeak * H * A := by
        have hAH : aPeak * H = aPeak + 2 * kappaLG := by
          dsimp [H]
          field_simp [haPeak.ne']
        have hAHlt : kappaLG < aPeak * H := by
          rw [hAH]
          linarith only [haPeak, hkappaLG0]
        exact mul_lt_mul_of_pos_right hAHlt hApos
      have hcontra : aPeak * H * A < aPeak * u1 := by
        have hsource  := hhigh.trans_le hweightToU1
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hsource haPeak
      exact (not_lt_of_ge hmain) (hstrict.trans hcontra)
  have hseed := hdtpBeta.scaled hs (by linarith : 0 < u1 / 2)
    U B G q hU hclosedSmallU hB hq hG
    (hqnonneg.mono hopenSmall) (fun z _ ↦ abs_nonneg (F z))
    (hlowerK.mono hopenSmall) (hupperK.mono hopenSmall)
    (supersolution_of_equation_abs fun z hz ↦ heqK z (hopenSmall hz)) hhighDensity
  let ell : ℝ := (u1 / 2) * gBeta
  let eD : ℝ := Cbeta * A
  have hell : 0 < ell := by
    dsimp [ell]
    positivity
  have heD : 0 ≤ eD := by
    dsimp [eD]
    positivity
  have hseedAdd : ∀ w ∈ velocityClosedCube v1 (s / 2),
      ell ≤ q (t1, w) + eD := by
    intro w hw
    have hpoint := hseed w hw
    have htime : tBase + s ^ 2 = t1 := by
      dsimp [tBase]
      ring
    rw [htime] at hpoint
    have hterm : Cbeta * s ^ p * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ eD := by
      dsimp [eD]
      have hinner : s ^ p * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ A := by
        calc
          s ^ p * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤
              1 * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) :=
            mul_le_mul_of_nonneg_right hspow ENNReal.toReal_nonneg
          _ ≤ A := by simpa using hnormSmall
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hCbeta
    dsimp [ell]
    have hterm' : Cbeta * s ^ sharedTerm_bcece2f0cb *
        parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ eD := by
      exact hterm
    exact hpoint.trans (by simpa only [add_comm] using add_le_add_left hterm' (q (t1, w)))
  obtain ⟨htauLower, htauUpper, hwidth, hbase, htarget, hcorridor⟩ :=
    selected_localHarnack_corridor hpeakPoint hr0eq hr0lt hv
  let tau : ℝ := selectedLocalHarnackForwardTime t1 j
  let lower  := localHarnackCorridorLower v1 v
  let upper  := localHarnackCorridorUpper v1 v
  let UHat : HypoellipticAleksandrov.Parabolic.Region d := localHarnackCorridorNeighborhood t1
  let BHat  := pullbackCoefficient B t1 (0 ) 1
  let qHat  := pullbackScalar (fun z ↦ q z + eD) t1 (0 ) 1
  let GHat  := pullbackScalar G t1 (0 ) 1
  have hUHat : IsOpen UHat := by
    dsimp [UHat, localHarnackCorridorNeighborhood]
    exact hworkOpen.preimage (contDiff_parabolicAffine t1 0 1).continuous
  have hmapHat : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1) UHat
      (parabolicBox 2 2 0 0) := fun _ hz ↦ hz
  have hmapHatU : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1) UHat U :=
    fun z hz ↦ hKU (hworkOpenK (hmapHat hz))
  have hcorridor' : parabolicClosedRectangle tau lower upper ⊆ UHat := by
    exact hcorridor
  have hrect : parabolicRectangle tau lower upper ⊆ UHat := by
    intro z hz
    apply hcorridor'
    rcases hz with ⟨ht, hw⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, fun i ↦ ⟨(hw i).1.le, (hw i).2.le⟩⟩
  have hrectWork : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1)
      (parabolicRectangle tau lower upper) (parabolicBox 2 2 0 0) :=
    fun _ hz ↦ hmapHat (hrect hz)
  have hrectK : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1)
      (parabolicRectangle tau lower upper) K := fun _ hz ↦ hworkOpenK (hrectWork hz)
  have hBHat  := hB.pullback hmapHatU
  have hqHat : ContDiffOn ℝ 2 qHat UHat := by
    dsimp [qHat]
    exact ContDiffOn.pullbackScalar (hq.add contDiffOn_const) hmapHatU
  have hGHat : ContinuousOn GHat UHat := by
    dsimp [GHat]
    exact hG.comp (contDiff_parabolicAffine t1 0 1).continuous.continuousOn hmapHatU
  have hnonnegHat : IsNonnegativeOn qHat (parabolicRectangle tau lower upper) := by
    intro z hz
    dsimp [qHat, pullbackScalar_apply]
    exact add_nonneg (hqnonneg _ (hrectK hz)) heD
  have hlowerHat  :=
    hlowerK.pullback hrectK
  have hupperHat  :=
    hupperK.pullback hrectK
  have hGHatNonneg : IsNonnegativeOn GHat (parabolicRectangle tau lower upper) := by
    intro z _
    dsimp [GHat, pullbackScalar_apply, G]
    exact abs_nonneg _
  have hsuperWork : IsParabolicSupersolutionOn B (fun z ↦ -G z)
      (fun z ↦ q z + eD) (parabolicBox 2 2 0 0) :=
    supersolution_of_equation_abs (equation_add_const fun z hz ↦ heqK z (hworkOpenK hz))
  have hsuperHat : IsParabolicSupersolutionOn BHat (fun z ↦ -GHat z) qHat
      (parabolicRectangle tau lower upper) := by
    dsimp [BHat, qHat, GHat]
    simpa only [one_pow, one_mul] using IsParabolicSupersolutionOn.pullback
      hworkOpen ((hq.add contDiffOn_const).mono (hworkOpenK.trans hKU))
      hsuperWork hrectWork
  have heps : 0 < (1 - r0) / 8 := by linarith
  have hepsOne : (1 - r0) / 8 ≤ 1 := by linarith
  have hpropSeed : ∀ w ∈ velocityClosedRectangle lower upper,
      w ∈ velocityCube v1 (((1 - r0) / 8) * 2) → ell ≤ qHat (0, w) := by
    intro w _hwRect hwCube
    have hwSeed : w ∈ velocityClosedCube v1 (s / 2) := by
      change w ∈ velocityClosedCube v1 (((1 - r0) / 2) / 2)
      intro i
      have hwi := hwCube i
      have hradius : ((1 - r0) / 8) * 2 = ((1 - r0) / 2) / 2 := by ring
      rw [← hradius]
      exact hwi.le
    have hpoint := hseedAdd w hwSeed
    dsimp [qHat, pullbackScalar_apply, parabolicAffine]
    simpa using hpoint
  have hpropOut := hprop 2 BHat v1 lower upper tau UHat GHat qHat
    ((1 - r0) / 8) ell tau v (by norm_num) (by norm_num)
    (by norm_num; exact htauLower) (by norm_num; exact htauUpper)
    (by
      intro i
      rcases hwidth i with ⟨hleft, hright⟩
      constructor
      · norm_num
        exact hleft
      · norm_num
        linarith)
    (by
      intro i
      rcases hbase i with ⟨hleft, hright⟩
      constructor
      · norm_num
        exact hleft
      · norm_num
        exact hright)
    hUHat hcorridor' hBHat hqHat hGHat hnonnegHat hlowerHat hupperHat hGHatNonneg
    hsuperHat heps hepsOne hell hpropSeed (by norm_num; exact htauLower) le_rfl
    (by norm_num; exact htarget)
  have htargetEval : qHat (tau, v) = q (localHarnackTerminalApprox j, v) + eD := by
    dsimp [qHat, pullbackScalar_apply, tau, parabolicAffine]
    have htime : t1 + selectedLocalHarnackForwardTime t1 j =
        localHarnackTerminalApprox j := selectedLocalHarnackForwardTime_eq j
    simpa using congrArg (fun t ↦ q (t, v) + eD) htime
  rw [htargetEval] at hpropOut
  have himageK : parabolicAffine t1 (0 : PDE.Vec d) 1 ''
      parabolicRectangle tau lower upper ⊆ K := by
    rintro z ⟨w, hw, rfl⟩
    exact hrectK hw
  have hnormHat : parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) ≤ A := by
    calc
      parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) =
          (1 : ℝ) ^ p * parabolicLpNormOn d G
            (parabolicAffine t1 (0 ) 1 '' parabolicRectangle tau lower upper) := by
        simpa [GHat, pullbackScalar, Function.comp_def] using
          (parabolicLpNormOn_pullback t1 (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1)
            G (parabolicRectangle tau lower upper))
      _ = parabolicLpNormOn d G
            (parabolicAffine t1 (0 ) 1 '' parabolicRectangle tau lower upper) := by simp
      _ ≤ parabolicLpNormOn d G K :=
        _root_.HypoellipticAleksandrov.Parabolic.parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl himageK
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  have hweight' : q (4, (0 )) ≤ (1 - r0) ^ m * u1 := by
    exact hweight
  have hfactor : hBox * q (4, (0 )) ≤
      delta * ((1 - r0) / 8) ^ m * ell := by
    have hh : hBox ≤ c := min_le_right _ _
    have hscale : ((1 - r0) / 8) * 8 = 1 - r0 := by ring
    have hpowEq : (1 - r0) ^ m = (8 : ℝ) ^ m * ((1 - r0) / 8) ^ m := by
      rw [← hscale, mul_pow]
      ring
    have hpowCancel : (1 / 8 : ℝ) ^ m * 8 ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      hBox * q (4, (0 )) ≤ hBox * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_left hweight' hhBox0.le
      _ ≤ c * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg (by linarith) _) hu1'.le)
      _ = delta * ((1 - r0) / 8) ^ m * ell := by
        let sharedTerm_c8b5c2b732 := (((1 - r0) / 8) ^ m)
        dsimp [c, ell]
        rw [hpowEq]
        calc
          delta * (1 / 8 : ℝ) ^ m * (gBeta / 2) *
              (8 ^ m * sharedTerm_c8b5c2b732 * u1) =
              delta * (gBeta / 2) * ((1 / 8 : ℝ) ^ m * 8 ^ m) *
                sharedTerm_c8b5c2b732 * u1 := by ring
          _ = delta * sharedTerm_c8b5c2b732 * ((u1 / 2) * gBeta) := by
            rw [hpowCancel]
            ring
  have hpropBound : delta * ((1 - r0) / 8) ^ m * ell ≤
        q (localHarnackTerminalApprox j, v) + (Cbeta + CP * (2 : ℝ) ^ p) * A := by
      have herror : CP * (2 : ℝ) ^ p * parabolicLpNormOn d GHat
          (parabolicRectangle tau lower upper) ≤ CP * (2 : ℝ) ^ p * A := by
        gcongr
      calc
        delta * ((1 - r0) / 8) ^ m * ell ≤
            q (localHarnackTerminalApprox j, v) + eD + CP * (2 : ℝ) ^ p *
              parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) := hpropOut.le
        _ ≤ q (localHarnackTerminalApprox j, v) + eD + CP * (2 : ℝ) ^ p * A :=
          by simpa only [add_assoc, add_comm, add_left_comm] using
            add_le_add_left herror (q (localHarnackTerminalApprox j, v) + eD)
        _ = q (localHarnackTerminalApprox j, v) + (Cbeta + CP * (2 : ℝ) ^ p) * A := by
          ring
  calc
    hBox * q (4, (0 )) ≤ delta * ((1 - r0) / 8) ^ m * ell := hfactor
    _ ≤ q (localHarnackTerminalApprox j, v) + (Cbeta + CP * (2 : ℝ) ^ p) * A := hpropBound
    _ ≤ q (localHarnackTerminalApprox j, v) + C * A := by
      let sharedTerm_36087e4849 := ((Cbeta + CP * (2 : ℝ) ^ p))
      have hsmallC : sharedTerm_36087e4849 ≤ C := by
        dsimp [C]
        calc
          sharedTerm_36087e4849 = 0 + (sharedTerm_36087e4849) := by ring
          _ ≤ H + (sharedTerm_36087e4849) := by
            simpa only [add_comm] using add_le_add_right hH.le sharedTerm_36087e4849
          _ = H + Cbeta + CP * (2 : ℝ) ^ p := by ring
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hsmallC hA)
          (q (localHarnackTerminalApprox j, v))

end

end HypoellipticAleksandrov.Parabolic
