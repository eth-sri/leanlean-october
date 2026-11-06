module

public import HypoellipticAleksandrov.Parabolic.SourceLevelGrowth
public import HypoellipticAleksandrov.Parabolic.SourceForwardPropagation
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry
public import HypoellipticAleksandrov.Parabolic.PeakSelection
public import HypoellipticAleksandrov.Parabolic.SourceDensityPositivePropagation

/-!
# Carrier-local source-aware parabolic Harnack estimate

This module combines the source density, level-growth, peak-selection,
and forward-propagation interfaces on one compact carrier.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

variable {d : ℕ} {B : CoefficientField d} {F q : TimeVelocity d → ℝ} {V : Set (TimeVelocity d)}


private theorem low_density_of_not_high_density  {R eps t0 beta : ℝ}
    {v0 : PDE.Vec d} (_hR : 0 < R) (U : Set (TimeVelocity d))
    (q : TimeVelocity d → ℝ) (_hU : IsOpen U)
    (hQU : parabolicBox 1 R t0 v0 ⊆ U) (hq : ContDiffOn ℝ 2 q U)
    (hnot : ¬ beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 R t0 v0 ∩ {z | eps ≤ q z})).toReal) :
    (1 - beta) * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 R t0 v0 ∩ {z | q z ≤ eps})).toReal := by
  let Q := parabolicBox 1 R t0 v0
  let L  := Q ∩ {z | q z < eps}
  let H  := Q ∩ {z | eps ≤ q z}
  have hL : MeasurableSet L := by
    have hcont  := hq.continuousOn.mono hQU
    exact (hcont.isOpen_inter_preimage (isOpen_parabolicBox 1 R t0 v0)
      isOpen_Iio).measurableSet
  have hQfinite : volume Q ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono parabolicBox_subset_closedBox)
  have hLsubset : L ⊆ Q := fun _ hz ↦ hz.1
  have hinter  := inter_eq_right.mpr hLsubset
  have hdiff : Q \ L = H := by
    aesop
  have hdecomp  := by
    simpa only [Measure.real, hinter, hdiff] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hL hQfinite)
  have hlow : (1 - beta) * (volume Q).toReal < (volume L).toReal := by
    nlinarith
  have hsubset : L ⊆ Q ∩ {z | q z ≤ eps} := by
    grind
  have htargetFinite : volume
      (Q ∩ {z | q z ≤ eps}) ≠ ⊤ :=
    ne_top_of_le_ne_top hQfinite (measure_mono fun _ hz ↦ hz.1)
  exact hlow.le.trans (ENNReal.toReal_mono htargetFinite (measure_mono hsubset))

private theorem parabolicLpNormOn_abs  (F : TimeVelocity d → ℝ)
    (S : Set (TimeVelocity d)) (hF : AEStronglyMeasurable F (volume.restrict S)) :
    parabolicLpNormOn d (fun z ↦ |F z|) S = parabolicLpNormOn d F S := by
  apply congrArg ENNReal.toReal
  have habs : AEStronglyMeasurable (fun z ↦ |F z|) (volume.restrict S) := by
    fun_prop
  apply eLpNorm_congr_enorm_ae habs hF
  simp


private theorem supersolution_of_equation_abs 
    (heq : ∀ z ∈ V, parabolicOperator B q z = F z) :
    IsParabolicSupersolutionOn B (fun z ↦ -|F z|) q V := by
  intro z hz
  grind

private theorem equation_add_const  {e : ℝ}
    (heq : ∀ z ∈ V, parabolicOperator B q z = F z) :
    ∀ z ∈ V, parabolicOperator B (fun y ↦ q y + e) z = F z := by
  intro z hz
  rw [parabolicOperator_add_const, heq z hz]

/-- A source-aware positive local parabolic Harnack estimate on one compact carrier. -/
theorem exists_source_local_parabolic_harnack_positive
    (d : Nat) (hd : 1 ≤ d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) :
    ∃ hBox C : Real, 0 < hBox ∧ hBox ≤ 1 ∧ 0 < C ∧
      ∀ (K U : Set (TimeVelocity d)) (B : CoefficientField d)
        (q F : TimeVelocity d → Real),
        IsCompact K → K ⊆ U → IsOpen U →
        parabolicClosedBox 2 2 0 0 ⊆ K →
        IsContinuousCoefficientOn B U → ContDiffOn Real 2 q U →
        ContinuousOn F U → IsNonnegativeOn q K →
        HasLowerEllipticityOn lam B K → HasUpperEllipticityOn Lam B K →
        (∀ x ∈ K, parabolicOperator B q x = F x) →
        0 < q (4, (0 : PDE.Vec d)) →
        ∀ (j : Nat) (v : PDE.Vec d),
          v ∈ velocityCube (0 : PDE.Vec d) 1 →
          hBox * q (4, (0 : PDE.Vec d)) ≤
            q (localHarnackTerminalApprox j, v) +
              C * parabolicLpNormOn d F K := by
  have hd' : 0 < d := by omega
  obtain ⟨delta, hdelta, m, hm, CP, hCP, hprop⟩ :=
    exists_forward_propagation_source_constants d hd' lam Lam (1 / 2)
      hlam hlamLam (by norm_num) (by norm_num)
  let gStar : ℝ := 1 - 1 / (4 * (2) ^ m)
  have hpow0 : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hpow1 : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hden0 : 0 < 4 * (2 : ℝ) ^ m := mul_pos (by norm_num) hpow0
  have hden1 : 1 < 4 * (2 : ℝ) ^ m := by nlinarith
  have hfrac_lt_one : 1 / (4 * (2 : ℝ) ^ m) < 1 :=
    (div_lt_one₀ hden0).mpr hden1
  have hgStar0 : 0 < gStar := sub_pos.mpr hfrac_lt_one
  have hgStar1 : gStar < 1 := sub_lt_self 1 (div_pos (by norm_num) hden0)
  have hratio_id :
      (2 - gStar) / (2 * (1 - gStar)) = 2 * (2) ^ m + 1 / 2 := by
    dsimp [gStar]
    field_simp [hden0.ne']
    ring
  obtain ⟨rho, hrho0, hrho1, CStar, hCStar, hdtpStar⟩ :=
    exists_sourceDensityToPoint_near_one d hd' lam hlam Lam hlamLam
      gStar hgStar0 hgStar1
  let beta : ℝ := 1 - rho
  have hbeta0 : 0 < beta := sub_pos.mpr hrho1
  have hbeta1 : beta < 1 := sub_lt_self 1 hrho0
  have honeSubBeta : 1 - beta = rho := by
    ring
  let kappaLG : ℝ := CStar / (1 - gStar)
  have hkappaLG0 : 0 < kappaLG := div_pos hCStar (sub_pos.mpr hgStar1)
  let aPeak : ℝ := (2) ^ m + 1 / 2
  have haPeak : 0 < aPeak := by positivity
  let H : ℝ := 1 + 2 * kappaLG / aPeak
  have hH : 0 < H := by positivity
  obtain ⟨gBeta, Cbeta, hgBeta0, _hgBeta1, hCbeta, hdtpBeta⟩ :=
    exists_sourceDensityToPoint_positive d hd' lam hlam Lam hlamLam beta hbeta0 hbeta1
  let p : ℝ := d / (d + 1)
  have hp : 0 ≤ p := by
    positivity
  let c : ℝ := delta * (1 / 8) ^ m * (gBeta / 2)
  let hBox : ℝ := min 1 c
  have hc : 0 < c := by
    positivity
  have hhBox0 : 0 < hBox := lt_min (by norm_num) hc
  have hhBox1 : hBox ≤ 1 := min_le_left _ _
  let C : ℝ := H + Cbeta + CP * (2) ^ p
  have hC : 0 < C := by
    positivity
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F hKcompact hKU hU hworkClosed hB hq hF hqnonneg hlowerK hupperK
    heqK hsourcePos j v hv
  let A : ℝ := parabolicLpNormOn d F K
  let G : TimeVelocity d → ℝ := fun z ↦ |F z|
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hG : ContinuousOn G U := hF.abs
  have hworkOpen : IsOpen (parabolicBox 2 2 (0) (0 : PDE.Vec d)) :=
    isOpen_parabolicBox 2 2 0 0
  have hworkOpenK : parabolicBox 2 2 (0) (0) ⊆ K :=
    parabolicBox_subset_closedBox.trans hworkClosed
  have hcontPeak : ContinuousOn q (backwardParabolicClosedBox 1 4 (0)) :=
    hq.continuousOn.mono
      (backwardParabolicClosedBox_one_four_subset_normalizedOpenBox.trans hworkOpenK |>.trans hKU)
  obtain ⟨t1, v1, r0, hpeakPoint, hr0eq, _hpeakMax, hr0lt, hweight, hu1,
    hpeakNested⟩ := exists_weighted_backward_peak m hm q hcontPeak hsourcePos
  let s : ℝ := (1 - r0) / 2
  let u1 : ℝ := q (t1, v1)
  let M : ℝ := (2) ^ m * u1
  let tBase : ℝ := t1 - s ^ 2
  have hr0nonneg : 0 ≤ r0 := by
    rw [hr0eq]
    exact le_max_of_le_left (by
      rw [show velocitySupNorm (v1 - 0) = ‖v1‖ by
        simp only [velocitySupNorm_eq_norm, sub_zero]]
      exact norm_nonneg _)
  have hs : 0 < s := selected_backward_radius_pos hr0lt
  have hsOne : s ≤ 1 := by
    dsimp [s]
    linarith
  have hspow : s ^ p ≤ 1 := Real.rpow_le_one hs.le hsOne hp
  have hu1' : 0 < u1 := by simpa only [u1] using hu1
  have hbasePow : (1 - r0) ^ m ≤ 1 := by
    apply pow_le_one₀
    · linarith
    · linarith
  have hweightToU1 : q (4, (0)) ≤ u1 := by
    calc
      q (4, (0)) ≤ (1 - r0) ^ m * u1 := hweight
      _ ≤ 1 * u1 := mul_le_mul_of_nonneg_right hbasePow hu1'.le
      _ = u1 := one_mul _
  have hclosedSmall : parabolicClosedBox 1 s tBase v1 ⊆ K := by
    intro z hz
    apply hworkOpenK
    rw [← backwardParabolicClosedBox_eq_parabolicClosedBox s t1 v1] at hz
    exact selected_backwardParabolicClosedBox_subset_normalizedOpenBox hpeakPoint hr0eq hr0lt hz
  have hopenSmall : parabolicBox 1 s tBase v1 ⊆ K :=
    parabolicBox_subset_closedBox.trans hclosedSmall
  have hclosedSmallU : parabolicClosedBox 1 s tBase v1 ⊆ U := hclosedSmall.trans hKU
  have hopenSmallU : parabolicBox 1 s tBase v1 ⊆ U := hopenSmall.trans hKU
  have hM : ∀ z ∈ parabolicClosedBox 1 s tBase v1, q z ≤ M := by
    intro z hz
    rw [← backwardParabolicClosedBox_eq_parabolicClosedBox s t1 v1] at hz
    exact hpeakNested z hz
  have htop : u1 ≤ q (tBase + s ^ 2, v1) := by
    dsimp [u1, tBase]
    apply le_of_eq
    ring_nf
  have hnormSmall : parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ A := by
    calc
      parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ parabolicLpNormOn d G K :=
        parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl hopenSmall
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  suffices hhighCase : H * A < q (4, (0 : PDE.Vec d)) →
      hBox * q (4, (0 : PDE.Vec d)) ≤
        q (localHarnackTerminalApprox j, v) + C * parabolicLpNormOn d F K by
    by_cases hhigh : H * A < q (4, (0 : PDE.Vec d))
    · exact hhighCase hhigh
    · have htargetK : (localHarnackTerminalApprox j, v) ∈ K :=
        hworkOpenK (localHarnackTerminalApprox_mem_normalizedOpenBox j hv)
      have htargetNonneg : 0 ≤ q (localHarnackTerminalApprox j, v) := hqnonneg _ htargetK
      have hsourceBound : q (4, (0 : PDE.Vec d)) ≤ H * A := le_of_not_gt hhigh
      have hHC : H ≤ C := by
        have hCPpow : 0 ≤ CP * (2) ^ p :=
          mul_nonneg hCP.le (Real.rpow_nonneg (by norm_num) _)
        exact (le_add_of_nonneg_right hCbeta).trans (le_add_of_nonneg_right hCPpow)
      have hCA : H * A ≤ C * A := mul_le_mul_of_nonneg_right hHC hA
      calc
        hBox * q (4, (0)) ≤ hBox * (H * A) :=
          mul_le_mul_of_nonneg_left hsourceBound hhBox0.le
        _ ≤ H * A := by nlinarith [hH, hA]
        _ ≤ C * A := hCA
        _ ≤ q (localHarnackTerminalApprox j, v) + C * A :=
          le_add_of_nonneg_left htargetNonneg
  intro hhigh
  have hhighDensity : beta * (volume
      (parabolicBox 1 s tBase v1)).toReal ≤
      (volume
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
      grind
    have hnormSmallF : parabolicLpNormOn d F (parabolicBox 1 s tBase v1) ≤ A := by
      rw [← parabolicLpNormOn_abs F (parabolicBox 1 s tBase v1)
        ((hF.mono hopenSmallU).aestronglyMeasurable
          (isOpen_parabolicBox 1 s tBase v1).measurableSet)]
      exact hnormSmall
    have hmain : aPeak * u1 ≤ kappaLG * A := by
      calc
        aPeak * u1 ≤ kappaLG * s ^ p *
            parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := hgrowth'
        _ ≤ kappaLG * A := by
          have hterm : s ^ p * parabolicLpNormOn d F (parabolicBox 1 s tBase v1) ≤ A := by
            calc
              s ^ p * parabolicLpNormOn d F (parabolicBox 1 s tBase v1) ≤
                  1 * parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := mul_le_mul_of_nonneg_right hspow ENNReal.toReal_nonneg
              _ ≤ A := by simpa using hnormSmallF
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
        simpa only [mul_assoc] using mul_lt_mul_of_pos_right hAHlt hApos
      have hcontra : aPeak * H * A < aPeak * u1 := by
        have hsource : H * A < u1 := hhigh.trans_le hweightToU1
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hsource haPeak
      linarith
  have hseed := hdtpBeta.scaled hs (by linarith)
    U B G q hU hclosedSmallU hB hq hG
    (hqnonneg.mono hopenSmall) (fun z _ ↦ abs_nonneg (F z))
    (hlowerK.mono hopenSmall) (hupperK.mono hopenSmall)
    (supersolution_of_equation_abs fun z hz ↦ heqK z (hopenSmall hz)) hhighDensity
  let ell : ℝ := (u1 / 2) * gBeta
  let eD : ℝ := Cbeta * A
  have hell : 0 < ell := by
    positivity
  have heD : 0 ≤ eD := by
    positivity
  have hseedAdd : ∀ w ∈ velocityClosedCube v1 (s / 2),
      ell ≤ q (t1, w) + eD := by
    have hterm : Cbeta * s ^ p * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ eD := by
      have hinner : s ^ p * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ A := by
        calc
          s ^ p * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤
              1 * parabolicLpNormOn d G (parabolicBox 1 s tBase v1) :=
            mul_le_mul_of_nonneg_right hspow ENNReal.toReal_nonneg
          _ ≤ A := by simpa using hnormSmall
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hCbeta
    grind
  obtain ⟨htauLower, htauUpper, hwidth, hbase, htarget, hcorridor⟩ :=
    selected_localHarnack_corridor hpeakPoint hr0eq hr0lt hv
  let tau : ℝ := selectedLocalHarnackForwardTime t1 j
  let lower : PDE.Vec d := localHarnackCorridorLower v1 v
  let upper : PDE.Vec d := localHarnackCorridorUpper v1 v
  let UHat : Set (TimeVelocity d) := localHarnackCorridorNeighborhood t1
  let BHat : CoefficientField d := pullbackCoefficient B t1 (0 : PDE.Vec d) 1
  let qHat : TimeVelocity d → ℝ := pullbackScalar (fun z ↦ q z + eD) t1 (0 : PDE.Vec d) 1
  let GHat : TimeVelocity d → ℝ := pullbackScalar G t1 (0 : PDE.Vec d) 1
  have hUHat : IsOpen UHat := hworkOpen.preimage (contDiff_parabolicAffine t1 0 1).continuous
  have hmapHat : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1) UHat
      (parabolicBox 2 2 0 0) := fun _ hz ↦ hz
  have hmapHatU : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1) UHat U :=
    fun z hz ↦ hKU (hworkOpenK (hmapHat hz))
  have hcorridor' : parabolicClosedRectangle tau lower upper ⊆ UHat := by
    simpa only [tau, lower, upper] using hcorridor
  have hrect : parabolicRectangle tau lower upper ⊆ UHat := by
    intro z hz
    apply hcorridor'
    rcases hz with ⟨ht, hw⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, fun i ↦ ⟨(hw i).1.le, (hw i).2.le⟩⟩
  have hrectWork : MapsTo (parabolicAffine t1 (0) 1)
      (parabolicRectangle tau lower upper) (parabolicBox 2 2 0 0) :=
    fun _ hz ↦ hmapHat (hrect hz)
  have hrectK : MapsTo (parabolicAffine t1 (0) 1)
      (parabolicRectangle tau lower upper) K := fun _ hz ↦ hworkOpenK (hrectWork hz)
  have hBHat : IsContinuousCoefficientOn BHat UHat := hB.pullback hmapHatU
  have hqHat : ContDiffOn ℝ 2 qHat UHat := ContDiffOn.pullbackScalar (hq.add contDiffOn_const) hmapHatU
  have hGHat : ContinuousOn GHat UHat := hG.comp (contDiff_parabolicAffine t1 0 1).continuous.continuousOn hmapHatU
  have hnonnegHat : IsNonnegativeOn qHat (parabolicRectangle tau lower upper) := by
    intro z hz
    exact add_nonneg (hqnonneg _ (hrectK hz)) heD
  have hlowerHat : HasLowerEllipticityOn lam BHat (parabolicRectangle tau lower upper) :=
    hlowerK.pullback hrectK
  have hupperHat : HasUpperEllipticityOn Lam BHat (parabolicRectangle tau lower upper) :=
    hupperK.pullback hrectK
  have hGHatNonneg : IsNonnegativeOn GHat (parabolicRectangle tau lower upper) := by
    intro z _
    exact abs_nonneg _
  have hsuperWork : IsParabolicSupersolutionOn B (fun z ↦ -G z)
      (fun z ↦ q z + eD) (parabolicBox 2 2 0 0) :=
    supersolution_of_equation_abs (equation_add_const fun z hz ↦ heqK z (hworkOpenK hz))
  have hsuperHat : IsParabolicSupersolutionOn BHat (fun z ↦ -GHat z) qHat
      (parabolicRectangle tau lower upper) := by
    dsimp [GHat]
    simpa only [one_pow, one_mul] using IsParabolicSupersolutionOn.pullback
      hworkOpen ((hq.add contDiffOn_const).mono (hworkOpenK.trans hKU))
      hsuperWork hrectWork
  have heps : 0 < (1 - r0) / 8 := by linarith
  have hepsOne : (1 - r0) / 8 ≤ 1 := by linarith
  have hpropSeed : ∀ w ∈ velocityClosedRectangle lower upper,
      w ∈ velocityCube v1 (((1 - r0) / 8) * 2) → ell ≤ qHat (0, w) := by
    intro w _hwRect hwCube
    have hwSeed : w ∈ velocityClosedCube v1 (s / 2) := by
      intro i
      have hwi := hwCube i
      have hradius : ((1 - r0) / 8) * 2 = ((1 - r0) / 2) / 2 := by ring
      rw [← hradius]
      exact hwi.le
    have hpoint := hseedAdd w hwSeed
    dsimp [qHat, parabolicAffine]
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
      · linarith)
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
    dsimp [qHat, parabolicAffine]
    have htime : t1 + selectedLocalHarnackForwardTime t1 j =
        localHarnackTerminalApprox j := selectedLocalHarnackForwardTime_eq j
    simpa using congrArg (fun t ↦ q (t, v) + eD) htime
  have himageK : parabolicAffine t1 (0) 1 ''
      parabolicRectangle tau lower upper ⊆ K := by
    rintro z ⟨w, hw, rfl⟩
    exact hrectK hw
  have hnormHat : parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) ≤ A := by
    calc
      parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) =
          (1) ^ p * parabolicLpNormOn d G
            (parabolicAffine t1 (0) 1 '' parabolicRectangle tau lower upper) := by
        simpa [GHat, pullbackScalar, Function.comp_def] using
          (parabolicLpNormOn_pullback t1 (0) (by norm_num : (0 : ℝ) < 1)
            G (parabolicRectangle tau lower upper))
      _ = parabolicLpNormOn d G
            (parabolicAffine t1 (0) 1 '' parabolicRectangle tau lower upper) := by simp
      _ ≤ parabolicLpNormOn d G K :=
        parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl himageK
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  have hweight' : q (4, (0)) ≤ (1 - r0) ^ m * u1 := by
    simpa only [u1] using hweight
  have hfactor : hBox * q (4, (0)) ≤
      delta * ((1 - r0) / 8) ^ m * ell := by
    have hh : hBox ≤ c := min_le_right _ _
    have hscale : ((1 - r0) / 8) * 8 = 1 - r0 := by ring
    have hpowEq : (1 - r0) ^ m = (8) ^ m * ((1 - r0) / 8) ^ m := by
      rw [← hscale, mul_pow]
      ring
    have hpowCancel : (1 / 8 : ℝ) ^ m * 8 ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      hBox * q (4, (0)) ≤ hBox * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_left hweight' hhBox0.le
      _ ≤ c * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg (by linarith) _) hu1'.le)
      _ = delta * ((1 - r0) / 8) ^ m * ell := by
        rw [hpowEq]
        calc
          delta * (1 / 8) ^ m * (gBeta / 2) *
              (8 ^ m * ((1 - r0) / 8) ^ m * u1) =
              delta * (gBeta / 2) * ((1 / 8) ^ m * 8 ^ m) *
                ((1 - r0) / 8) ^ m * u1 := by ring
          _ = delta * ((1 - r0) / 8) ^ m * ((u1 / 2) * gBeta) := by
            rw [hpowCancel]
            ring
  have hpropBound : delta * ((1 - r0) / 8) ^ m * ell ≤
        q (localHarnackTerminalApprox j, v) + (Cbeta + CP * (2) ^ p) * A := by
      have herror : CP * (2) ^ p * parabolicLpNormOn d GHat
          (parabolicRectangle tau lower upper) ≤ CP * (2) ^ p * A := by
        gcongr
      linarith
  calc
    hBox * q (4, (0)) ≤ delta * ((1 - r0) / 8) ^ m * ell := hfactor
    _ ≤ q (localHarnackTerminalApprox j, v) + (Cbeta + CP * (2) ^ p) * A := hpropBound
    _ ≤ q (localHarnackTerminalApprox j, v) + C * A := by
      have hsmallC : Cbeta + CP * (2) ^ p ≤ C := by
        calc
          Cbeta + CP * (2) ^ p = 0 + (Cbeta + CP * (2) ^ p) := by ring
          _ ≤ H + (Cbeta + CP * (2) ^ p) := by
            simpa only [add_comm] using add_le_add_right hH.le (Cbeta + CP * (2) ^ p)
          _ = H + Cbeta + CP * (2) ^ p := by ring
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hsmallC hA)
          (q (localHarnackTerminalApprox j, v))

end

end HypoellipticAleksandrov.Parabolic
