module

public import HypoellipticAleksandrov.Parabolic.SourceLevelGrowth
public import HypoellipticAleksandrov.Parabolic.SourceForwardPropagation
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry
public import HypoellipticAleksandrov.Parabolic.PeakSelection

/-!
# Carrier-local source-aware parabolic Harnack estimate

This module combines the source density, level-growth, peak-selection,
and forward-propagation interfaces on one compact carrier.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

section
variable {d : ℕ} {B : CoefficientField d} {F q : TimeVelocity d → ℝ} {V : Set (TimeVelocity d)}
    {e : ℝ} (heq : ∀ z ∈ V, parabolicOperator B q z = F z)

private theorem parabolicBox_subset_closedBox {vartheta r t0 : ℝ}
    {v0 : PDE.Vec d} :
    parabolicBox vartheta r t0 v0 ⊆ parabolicClosedBox vartheta r t0 v0 := by
  intro z hz
  rcases hz with ⟨⟨hzleft, hzright⟩, hzv⟩
  exact ⟨⟨hzleft.le, hzright.le⟩, fun i ↦ (hzv i).le⟩

private theorem low_density_of_not_high_density {R eps t0 beta : ℝ}
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
  let L : Set (TimeVelocity d) := Q ∩ {z | q z < eps}
  let H := Q ∩ {z | eps ≤ q z}
  have hL : MeasurableSet L := by
    have hcont := hq.continuousOn.mono hQU
    exact (hcont.isOpen_inter_preimage (isOpen_parabolicBox 1 R t0 v0)
      isOpen_Iio).measurableSet
  have hQfinite : volume Q ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono parabolicBox_subset_closedBox)
  have hLsubset : L ⊆ Q := fun _ hz ↦ hz.1
  have hinter := inter_eq_right.mpr hLsubset
  have hdiff : Q \ L = H := by
    ext z
    simp only [L, H, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · grind
    · grind
  have hdecomp : (volume L).toReal + (volume H).toReal = (volume Q).toReal := by
    simpa only [Measure.real, hinter, hdiff] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hL hQfinite)
  have hlow : (1 - beta) * (volume Q).toReal < (volume L).toReal := by
    nlinarith
  have hsubset : L ⊆ Q ∩ {z | q z ≤ eps} := by
    grind
  exact hlow.le.trans (ENNReal.toReal_mono (ne_top_of_le_ne_top hQfinite (measure_mono fun _ hz ↦ hz.1)) (measure_mono hsubset))

private theorem parabolicLpNormOn_abs (F : TimeVelocity d → ℝ)
    (S : Set (TimeVelocity d)) (hF : AEStronglyMeasurable F (volume.restrict S)) :
    parabolicLpNormOn d (fun z ↦ |F z|) S = parabolicLpNormOn d F S := by
  unfold parabolicLpNormOn parabolicELpNormOn
  apply congrArg ENNReal.toReal
  have habs : AEStronglyMeasurable (fun z ↦ |F z|) (volume.restrict S) := by
    exact hF.norm
  apply eLpNorm_congr_enorm_ae habs hF
  filter_upwards [] with z
  apply Real.enorm_abs

private theorem parabolicLpNormOn_mono_of_continuousOn
    {F : TimeVelocity d → ℝ} {U S T K : Set (TimeVelocity d)}
    (hF : ContinuousOn F U) (hKU : K ⊆ U) (hKcompact : IsCompact K)
    (hTK : T ⊆ K) (hST : S ⊆ T) :
    parabolicLpNormOn d F S ≤ parabolicLpNormOn d F T := by
  have hFK := hF.mono hKU
  have hKmeas := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hFK
  have hKmem : MemLp F (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hFK.aestronglyMeasurable hKmeas) M ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hM z hz
  have hTmem :=
    hKmem.mono_measure (Measure.restrict_mono_set volume hTK)
  have hTtop : parabolicELpNormOn d F T ≠ ⊤ := by
    exact hTmem.eLpNorm_ne_top
  have hStop : parabolicELpNormOn d F S ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using (hTmem.mono_measure (Measure.restrict_mono_set volume hST)).eLpNorm_ne_top
  exact (ENNReal.toReal_le_toReal hStop hTtop).mpr
    (eLpNorm_mono_measure F (Measure.restrict_mono_set volume hST))

include heq in
private theorem supersolution_of_equation_abs :
    IsParabolicSupersolutionOn B (fun z ↦ -|F z|) q V := by
  intro z hz
  rw [heq z hz]
  apply neg_abs_le

include heq in
private theorem equation_add_const :
    ∀ z ∈ V, parabolicOperator B (fun y ↦ q y + e) z = F z := by
  intro z hz
  rw [parabolicOperator_add_const, heq z hz]

end

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
  let gStar : ℝ := 1 - 1 / (4 * 2 ^ m)
  have hpow0 : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hpow1 : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hden0 : 0 < 4 * (2 : ℝ) ^ m := mul_pos (by norm_num) hpow0
  have hden1 : 1 < 4 * (2 : ℝ) ^ m := by nlinarith
  have hfrac_lt_one : 1 / (4 * (2 : ℝ) ^ m) < 1 :=
    (div_lt_one₀ hden0).mpr hden1
  have hgStar0 : 0 < gStar := by
    positivity
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
  have hbeta0 := sub_pos.mpr hrho1
  have honeSubBeta : 1 - beta = rho := by
    ring
  let kappaLG := CStar / (1 - gStar)
  have hkappaLG0 : 0 < kappaLG := div_pos hCStar (sub_pos.mpr hgStar1)
  let aPeak : ℝ := (2 : ℝ) ^ m + 1 / 2
  have haPeak : 0 < aPeak := by positivity
  let H := 1 + 2 * kappaLG / aPeak
  have hH : 0 < H := by positivity
  obtain ⟨gBeta, Cbeta, hgBeta0, _hgBeta1, hCbeta, hdtpBeta⟩ :=
    exists_sourceDensityToPoint_positive d hd' lam hlam Lam hlamLam beta hbeta0 (sub_lt_self 1 hrho0)
  let p : ℝ := d / (d + 1)
  have hp : 0 ≤ p := by
    positivity
  let c := delta * (1 / 8) ^ m * (gBeta / 2)
  let hBox := min 1 c
  have hc : 0 < c := by
    positivity
  have hhBox0 : 0 < hBox := lt_min (by norm_num) hc
  have hhBox1 : hBox ≤ 1 := min_le_left _ _
  let C := H + Cbeta + CP * 2 ^ p
  have hC : 0 < C := by
    positivity
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F hKcompact hKU hU hworkClosed hB hq hF hqnonneg hlowerK hupperK
    heqK hsourcePos j v hv
  let A := parabolicLpNormOn d F K
  let G := fun z ↦ |F z|
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hG := hF.abs
  have hworkOpen : IsOpen (parabolicBox 2 2 (0 : ℝ) (0 : PDE.Vec d)) :=
    isOpen_parabolicBox 2 2 0 0
  have hworkOpenK :=
    parabolicBox_subset_closedBox.trans hworkClosed
  obtain ⟨t1, v1, r0, hpeakPoint, hr0eq, _hpeakMax, hr0lt, hweight, hu1,
    hpeakNested⟩ := exists_weighted_backward_peak m hm q (hq.continuousOn.mono (backwardParabolicClosedBox_one_four_subset_normalizedOpenBox.trans hworkOpenK |>.trans hKU)) hsourcePos
  let s := (1 - r0) / 2
  let u1 := q (t1, v1)
  let M := 2 ^ m * u1
  let tBase := t1 - s ^ 2
  have hr0nonneg : 0 ≤ r0 := by
    rw [hr0eq, backwardParabolicRadius]
    positivity
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsOne : s ≤ 1 := by
    dsimp [s]
    linarith
  have hspow : s ^ p ≤ 1 := Real.rpow_le_one hs.le hsOne hp
  have hu1' : 0 < u1 := by exact hu1
  have hbasePow : (1 - r0) ^ m ≤ 1 := by
    apply pow_le_one₀
    · linarith
    · linarith
  have hweightToU1 : q (4, 0) ≤ u1 := by
    calc
      q (4, 0) ≤ (1 - r0) ^ m * u1 := hweight
      _ ≤ 1 * u1 := mul_le_mul_of_nonneg_right hbasePow hu1'.le
      _ = u1 := one_mul _
  have hclosedSmall : parabolicClosedBox 1 s tBase v1 ⊆ K := by
    intro z hz
    apply hworkOpenK
    rw [← backwardParabolicClosedBox_eq_parabolicClosedBox s t1 v1] at hz
    exact selected_backwardParabolicClosedBox_subset_normalizedOpenBox hpeakPoint hr0eq hr0lt hz
  have hopenSmall :=
    parabolicBox_subset_closedBox.trans hclosedSmall
  have hclosedSmallU := hclosedSmall.trans hKU
  have hopenSmallU := hopenSmall.trans hKU
  have hM : ∀ z ∈ parabolicClosedBox 1 s tBase v1, q z ≤ M := by
    intro z hz
    rw [← backwardParabolicClosedBox_eq_parabolicClosedBox s t1 v1] at hz
    exact hpeakNested z hz
  have htop : u1 ≤ q (tBase + s ^ 2, v1) := by
    dsimp [u1, tBase]
    apply le_of_eq
    ring
  have hnormSmall : parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ A := by
    calc
      parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ parabolicLpNormOn d G K :=
        parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl hopenSmall
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  suffices hhighCase : H * A < q (4, 0) →
      hBox * q (4, 0) ≤
        q (localHarnackTerminalApprox j, v) + C * parabolicLpNormOn d F K by
    by_cases hhigh : H * A < q (4, 0)
    · exact hhighCase hhigh
    · have htargetK :=
        hworkOpenK (localHarnackTerminalApprox_mem_normalizedOpenBox j hv)
      have hsourceBound := le_of_not_gt hhigh
      have hHC : H ≤ C := by
        dsimp [C]
        exact (le_add_of_nonneg_right hCbeta).trans (le_add_of_nonneg_right (mul_nonneg hCP.le (Real.rpow_nonneg (by norm_num) _)))
      have hCA := mul_le_mul_of_nonneg_right hHC hA
      calc
        hBox * q (4, 0) ≤ hBox * (H * A) :=
          mul_le_mul_of_nonneg_left hsourceBound hhBox0.le
        _ ≤ H * A := by nlinarith [hH, hA]
        _ ≤ C * A := hCA
        _ ≤ q (localHarnackTerminalApprox j, v) + C * A :=
          le_add_of_nonneg_left (hqnonneg _ htargetK)
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
      have hgrowth'' : (2 * 2 ^ m + 1 / 2) * u1 ≤
          2 ^ m * u1 + kappaLG * s ^ p *
            parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := by
        simpa only [M, kappaLG, p, mul_comm] using hgrowth
      calc
        aPeak * u1 = (2 * 2 ^ m + 1 / 2) * u1 - 2 ^ m * u1 := by
          ring
        _ ≤ kappaLG * s ^ p * parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := by
          linarith only [hgrowth'']
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
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hterm hkappaLG0.le
    by_cases hAzero : A = 0
    · have hzero : aPeak * u1 ≤ 0 := by
        calc
          aPeak * u1 ≤ kappaLG * A := hmain
          _ = 0 := by rw [hAzero, mul_zero]
      exact (not_le_of_gt (mul_pos haPeak hu1')) hzero
    · have hstrict : kappaLG * A < aPeak * H * A := by
        have hAH : aPeak * H = aPeak + 2 * kappaLG := by
          dsimp [H]
          field_simp [haPeak.ne']
        have hAHlt : kappaLG < aPeak * H := by
          linarith
        simpa only [mul_assoc] using mul_lt_mul_of_pos_right hAHlt (lt_of_le_of_ne hA (Ne.symm hAzero))
      have hcontra : aPeak * H * A < aPeak * u1 := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left (hhigh.trans_le hweightToU1) haPeak
      exact (not_lt_of_ge hmain) (hstrict.trans hcontra)
  have hseed := hdtpBeta.scaled hs (by linarith)
    U B G q hU hclosedSmallU hB hq hG
    (hqnonneg.mono hopenSmall) (fun z _ ↦ abs_nonneg (F z))
    (hlowerK.mono hopenSmall) (hupperK.mono hopenSmall)
    (supersolution_of_equation_abs fun z hz ↦ heqK z (hopenSmall hz)) hhighDensity
  let ell := (u1 / 2) * gBeta
  let eD := Cbeta * A
  have hell : 0 < ell := by
    positivity
  have heD : 0 ≤ eD := by
    positivity
  have hseedAdd : ∀ w ∈ velocityClosedCube v1 (s / 2),
      ell ≤ q (t1, w) + eD := by
    intro w hw
    have hpoint := hseed w hw
    have htime : tBase + s ^ 2 = t1 := by
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
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinner hCbeta
    dsimp [ell]
    have hterm' : Cbeta * s ^ (d / ((d : ℝ) + 1)) *
        parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ eD := by
      exact hterm
    exact hpoint.trans (by simpa using add_le_add_left hterm' (q (t1, w)))
  obtain ⟨htauLower, htauUpper, hwidth, hbase, htarget, hcorridor⟩ :=
    selected_localHarnack_corridor hpeakPoint hr0eq hr0lt hv
  let tau := selectedLocalHarnackForwardTime t1 j
  let lower := localHarnackCorridorLower v1 v
  let upper := localHarnackCorridorUpper v1 v
  let UHat : Set (TimeVelocity d) := localHarnackCorridorNeighborhood t1
  let BHat := pullbackCoefficient B t1 0 1
  let qHat := pullbackScalar (fun z ↦ q z + eD) t1 0 1
  let GHat := pullbackScalar G t1 0 1
  have hUHat : IsOpen UHat := by
    exact hworkOpen.preimage (contDiff_parabolicAffine t1 0 1).continuous
  have hmapHat : MapsTo (parabolicAffine t1 0 1) UHat
      (parabolicBox 2 2 0 0) := fun _ hz ↦ hz
  have hmapHatU : MapsTo (parabolicAffine t1 0 1) UHat U :=
    fun z hz ↦ hKU (hworkOpenK (hmapHat hz))
  have hcorridor' : parabolicClosedRectangle tau lower upper ⊆ UHat := by
    exact hcorridor
  have hrect : parabolicRectangle tau lower upper ⊆ UHat := by
    intro z hz
    apply hcorridor'
    rcases hz with ⟨ht, hw⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, fun i ↦ ⟨(hw i).1.le, (hw i).2.le⟩⟩
  have hrectWork : MapsTo (parabolicAffine t1 0 1)
      (parabolicRectangle tau lower upper) (parabolicBox 2 2 0 0) :=
    fun _ hz ↦ hmapHat (hrect hz)
  have hrectK : MapsTo (parabolicAffine t1 0 1)
      (parabolicRectangle tau lower upper) K := fun _ hz ↦ hworkOpenK (hrectWork hz)
  have hqHat : ContDiffOn ℝ 2 qHat UHat := by
    exact ContDiffOn.pullbackScalar (hq.add contDiffOn_const) hmapHatU
  have hGHat : ContinuousOn GHat UHat := by
    exact hG.comp (contDiff_parabolicAffine t1 0 1).continuous.continuousOn hmapHatU
  have hnonnegHat : IsNonnegativeOn qHat (parabolicRectangle tau lower upper) := by
    intro z hz
    exact add_nonneg (hqnonneg _ (hrectK hz)) heD
  have hGHatNonneg : IsNonnegativeOn GHat (parabolicRectangle tau lower upper) := by
    intro z _
    apply abs_nonneg
  have hsuperHat : IsParabolicSupersolutionOn BHat (fun z ↦ -GHat z) qHat
      (parabolicRectangle tau lower upper) := by
    dsimp [BHat, qHat, GHat]
    simpa only [one_pow, one_mul] using IsParabolicSupersolutionOn.pullback
      hworkOpen ((hq.add contDiffOn_const).mono (hworkOpenK.trans hKU))
      (supersolution_of_equation_abs (equation_add_const fun z hz ↦ heqK z (hworkOpenK hz))) hrectWork
  have heps : 0 < (1 - r0) / 8 := by linarith
  have hepsOne : (1 - r0) / 8 ≤ 1 := by linarith
  have hpropSeed : ∀ w ∈ velocityClosedRectangle lower upper,
      w ∈ velocityCube v1 (((1 - r0) / 8) * 2) → ell ≤ qHat (0, w) := by
    intro w _hwRect hwCube
    have hwSeed : w ∈ velocityClosedCube v1 (s / 2) := by
      intro i
      have hradius : ((1 - r0) / 8) * 2 = ((1 - r0) / 2) / 2 := by ring
      rw [← hradius]
      exact (hwCube i).le
    dsimp [qHat, pullbackScalar_apply, parabolicAffine]
    simpa using (hseedAdd w hwSeed)
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
    hUHat hcorridor' (hB.pullback hmapHatU) hqHat hGHat hnonnegHat (hlowerK.pullback hrectK) (hupperK.pullback hrectK) hGHatNonneg
    hsuperHat heps hepsOne hell hpropSeed (by norm_num; exact htauLower) le_rfl
    (by norm_num; exact htarget)
  have htargetEval : qHat (tau, v) = q (localHarnackTerminalApprox j, v) + eD := by
    dsimp [qHat, pullbackScalar_apply, tau, parabolicAffine]
    simpa using congrArg (fun t ↦ q (t, v) + eD) (selectedLocalHarnackForwardTime_eq j)
  rw [htargetEval] at hpropOut
  have himageK : parabolicAffine t1 0 1 ''
      parabolicRectangle tau lower upper ⊆ K := by
    rintro z ⟨w, hw, rfl⟩
    exact hrectK hw
  have hnormHat : parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) ≤ A := by
    calc
      parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) =
          1 ^ p * parabolicLpNormOn d G
            (parabolicAffine t1 0 1 '' parabolicRectangle tau lower upper) := by
        simpa [GHat, pullbackScalar, Function.comp_def] using
          (parabolicLpNormOn_pullback t1 0 (by norm_num : (0 : ℝ) < 1)
            G (parabolicRectangle tau lower upper))
      _ = parabolicLpNormOn d G
            (parabolicAffine t1 0 1 '' parabolicRectangle tau lower upper) := by simp
      _ ≤ parabolicLpNormOn d G K :=
        parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl himageK
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  have hweight' : q (4, 0) ≤ (1 - r0) ^ m * u1 := by
    exact hweight
  have hfactor : hBox * q (4, 0) ≤
      delta * ((1 - r0) / 8) ^ m * ell := by
    have hscale : ((1 - r0) / 8) * 8 = 1 - r0 := by ring
    have hpowEq : (1 - r0) ^ m = 8 ^ m * ((1 - r0) / 8) ^ m := by
      rw [← hscale, mul_pow]
      ring
    have hpowCancel : (1 / 8 : ℝ) ^ m * 8 ^ m = 1 := by
      simp
    calc
      hBox * q (4, 0) ≤ hBox * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_left hweight' hhBox0.le
      _ ≤ c * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (mul_nonneg (pow_nonneg (by linarith) _) hu1'.le)
      _ = delta * ((1 - r0) / 8) ^ m * ell := by
        dsimp [c, ell]
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
        q (localHarnackTerminalApprox j, v) + (Cbeta + CP * 2 ^ p) * A := by
      have herror : CP * 2 ^ p * parabolicLpNormOn d GHat
          (parabolicRectangle tau lower upper) ≤ CP * 2 ^ p * A := by
        gcongr
      calc
        delta * ((1 - r0) / 8) ^ m * ell ≤
            q (localHarnackTerminalApprox j, v) + eD + CP * 2 ^ p *
              parabolicLpNormOn d GHat (parabolicRectangle tau lower upper) := hpropOut.le
        _ ≤ q (localHarnackTerminalApprox j, v) + eD + CP * 2 ^ p * A :=
          by simpa using
            add_le_add_left herror (q (localHarnackTerminalApprox j, v) + eD)
        _ = q (localHarnackTerminalApprox j, v) + (Cbeta + CP * 2 ^ p) * A := by
          ring
  calc
    hBox * q (4, 0) ≤ delta * ((1 - r0) / 8) ^ m * ell := hfactor
    _ ≤ q (localHarnackTerminalApprox j, v) + (Cbeta + CP * 2 ^ p) * A := hpropBound
    _ ≤ q (localHarnackTerminalApprox j, v) + C * A := by
      have hsmallC : Cbeta + CP * 2 ^ p ≤ C := by
        dsimp [C]
        calc
          Cbeta + CP * 2 ^ p = 0 + (Cbeta + CP * 2 ^ p) := by ring
          _ ≤ H + (Cbeta + CP * 2 ^ p) := by
            simpa using add_le_add_right hH.le (Cbeta + CP * (2 : ℝ) ^ p)
          _ = H + Cbeta + CP * 2 ^ p := by ring
      simpa using
        add_le_add_left (mul_le_mul_of_nonneg_right hsmallC hA)
          (q (localHarnackTerminalApprox j, v))

end

end HypoellipticAleksandrov.Parabolic
