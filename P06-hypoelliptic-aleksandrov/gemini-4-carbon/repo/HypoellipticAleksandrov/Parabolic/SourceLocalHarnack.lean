module

public import HypoellipticAleksandrov.Parabolic.SourceDensityPositive
public import HypoellipticAleksandrov.Parabolic.SourceForwardPropagation
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry
public import HypoellipticAleksandrov.Parabolic.PeakSelection

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory Set Filter




private theorem terminalCenter_mem_parabolicClosedBox {d : ℕ} {R t₀ : ℝ}
    {v₀ : PDE.Vec d} (hR : 0 < R) :
    (t₀ + R ^ 2, v₀) ∈ parabolicClosedBox 1 R t₀ v₀ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith [sq_nonneg R]
  · apply le_of_eq
    ring
  · intro i
    simp
    exact hR.le



private theorem volume_toReal_mono_of_subset {d : ℕ} {s t : Set (TimeVelocity d)}
    (ht : (volume : Measure (TimeVelocity d)) t ≠ ⊤) (hst : s ⊆ t) :
    ((volume : Measure (TimeVelocity d)) s).toReal ≤
      ((volume : Measure (TimeVelocity d)) t).toReal :=
  ENNReal.toReal_mono ht (measure_mono hst)

private theorem memLp_of_continuousOn_compact_carrier
    {d : ℕ} {F : TimeVelocity d → ℝ} {U Q K : Set (TimeVelocity d)}
    (hF : ContinuousOn F U) (hKU : K ⊆ U) (hKcompact : IsCompact K)
    (hQK : Q ⊆ K) :
    MemLp F (parabolicExponent d) (volume.restrict Q) := by
  have hFK := hF.mono hKU
  have hKmeas := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨A, hA⟩ := hKcompact.exists_bound_of_continuousOn hFK
  have hKmem : MemLp F (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hFK.aestronglyMeasurable hKmeas) A ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hA z hz
  exact hKmem.mono_measure (Measure.restrict_mono_set volume hQK)


private theorem source_supersolution_const_sub_div
    {d : ℕ} {B : CoefficientField d} {M D : ℝ} {F u : TimeVelocity d → ℝ}
    {Q : Set (TimeVelocity d)} (hD : 0 < D)
    (heq : ∀ z ∈ Q, parabolicOperator B u z = F z) :
    IsParabolicSupersolutionOn B (fun z ↦ -(|F z| / D))
      (fun z ↦ (M - u z) / D) Q  := by
  intro z hz
  have parabolicOperator_const_sub {d : ℕ} (B : CoefficientField d) (c : ℝ) (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
      parabolicOperator B (fun y ↦ c - u y) z = -parabolicOperator B u z := by
    calc
      parabolicOperator B (fun y ↦ c - u y) z =
          parabolicOperator B (fun y ↦ -u y + c) z := by
        congr 1
        funext y
        ring
      _ = parabolicOperator B (fun y ↦ -u y) z :=
        parabolicOperator_add_const B (fun y ↦ -u y) c z
      _ = -parabolicOperator B u z := parabolicOperator_neg B u z
  have hoperator : parabolicOperator B (fun y ↦ (M - u y) / D) z =
      D⁻¹ * (-parabolicOperator B u z) := by
    calc
      parabolicOperator B (fun y ↦ (M - u y) / D) z =
          parabolicOperator B (D⁻¹ • fun y ↦ M - u y) z := by
        congr 1
        funext y
        simp
        ring
      _ = D⁻¹ * parabolicOperator B (fun y ↦ M - u y) z :=
        parabolicOperator_const_smul B D⁻¹ (fun y ↦ M - u y) z
      _ = D⁻¹ * (-parabolicOperator B u z) := by
        rw [parabolicOperator_const_sub]
  rw [hoperator, heq z hz]
  have hquotient :=
    (div_le_div_iff_of_pos_right hD).mpr (le_abs_self (F z))
  calc
    -(|F z| / D) ≤ -(F z / D) := neg_le_neg hquotient
    _ = D⁻¹ * (-F z) := by field_simp [hD.ne']

/-- A supplied `SourceDensityToPoint` relation yields raw-equation source-aware level growth
on a physical box. -/
theorem source_level_growth_of_low_set_density
    {d : Nat} {lam Lam beta g C : Real}
    (hdtp : SourceDensityToPoint d lam Lam beta g C)
    {R nu t0 M : Real} {v0 : PDE.Vec d}
    (hR : 0 < R) (hnu : 0 < nu) (hg : g < 1)
    (U : Set (TimeVelocity d)) (B : CoefficientField d)
    (F u : TimeVelocity d → Real) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 R t0 v0 ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn Real 2 u U)
    (hF : ContinuousOn F U)
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 R t0 v0))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 R t0 v0))
    (heq : ∀ z ∈ parabolicBox 1 R t0 v0,
      parabolicOperator B u z = F z)
    (hM : ∀ z ∈ parabolicClosedBox 1 R t0 v0, u z ≤ M)
    (htop : nu ≤ u (t0 + R ^ 2, v0))
    (hdensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 R t0 v0 ∩ {z | u z ≤ nu / 2})).toReal) :
    nu * ((2 - g) / (2 * (1 - g))) ≤
      M + (C / (1 - g)) * R ^ ((d : Real) / ((d : Real) + 1)) *
        parabolicLpNormOn d F (parabolicBox 1 R t0 v0)     := by
  have parabolicLpNormOn_abs_div {d : ℕ} {F : TimeVelocity d → ℝ} {Q : Set (TimeVelocity d)} {D : ℝ} (hD : 0 < D) (hFmem : MemLp F (parabolicExponent d) (volume.restrict Q)) :
      parabolicLpNormOn d (fun z ↦ |F z| / D) Q =
      D⁻¹ * parabolicLpNormOn d F Q := by
    have hFtop : parabolicELpNormOn d F Q ≠ ⊤ := by
      simpa only [parabolicELpNormOn] using hFmem.eLpNorm_ne_top
    have habsmem : MemLp (fun z ↦ |F z|) (parabolicExponent d) (volume.restrict Q) := by
      simpa using hFmem.norm
    have habstop : parabolicELpNormOn d (fun z ↦ |F z|) Q ≠ ⊤ := by
      simpa only [parabolicELpNormOn] using habsmem.eLpNorm_ne_top
    have hinv := inv_nonneg.mpr hD.le
    calc
      parabolicLpNormOn d (fun z ↦ |F z| / D) Q =
          parabolicLpNormOn d (D⁻¹ • fun z ↦ |F z|) Q := by
        congr 2
        funext z
        simp
        ring
      _ = D⁻¹ * parabolicLpNormOn d (fun z ↦ |F z|) Q := by
        unfold parabolicLpNormOn parabolicELpNormOn
        rw [eLpNorm_const_smul, ENNReal.toReal_mul]
        simp only [Real.enorm_of_nonneg hinv, ENNReal.toReal_ofReal hinv]
      _ = D⁻¹ * parabolicLpNormOn d F Q := by
        congr 1
        unfold parabolicLpNormOn parabolicELpNormOn
        apply congrArg ENNReal.toReal
        apply eLpNorm_congr_enorm_ae habsmem.aestronglyMeasurable hFmem.aestronglyMeasurable
        filter_upwards [] with z
        exact Real.enorm_abs (F z)
  have contDiffOn_const_sub_div {D : ℝ} : ContDiffOn ℝ 2 (fun z ↦ (M - u z) / D) U :=
    (contDiffOn_const.sub hu).div_const D
  have center_mem_velocityClosedCube {v₀ : PDE.Vec d} :
      v₀ ∈ velocityClosedCube v₀ (R / 2) := by
    intro i
    simp
    linarith
  have parabolicBox_subset_parabolicClosedBox {vartheta r t₀ : ℝ} {v₀ : PDE.Vec d} :
      parabolicBox vartheta r t₀ v₀ ⊆ parabolicClosedBox vartheta r t₀ v₀ := by
    intro z hz
    rcases hz with ⟨⟨hzleft, hzright⟩, hzv⟩
    exact ⟨⟨hzleft.le, hzright.le⟩, fun i ↦ (hzv i).le⟩
  let Q := parabolicBox 1 R t0 v0
  let Qclosed := parabolicClosedBox 1 R t0 v0
  let D := M - nu / 2
  let w : TimeVelocity d → Real := fun z ↦ (M - u z) / D
  let Fabs : TimeVelocity d → Real := fun z ↦ |F z| / D
  have hterminal : (t0 + R ^ 2, v0) ∈ Qclosed :=
    terminalCenter_mem_parabolicClosedBox hR
  have hnuM := htop.trans (hM _ hterminal)
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hQsubset : Q ⊆ Qclosed := parabolicBox_subset_parabolicClosedBox
  have hFmem :=
    memLp_of_continuousOn_compact_carrier hF hclosed
      (isCompact_parabolicClosedBox 1 R t0 v0) hQsubset
  have hFtop : parabolicELpNormOn d F Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFmem.eLpNorm_ne_top
  have hFabsmem : MemLp Fabs (parabolicExponent d) (volume.restrict Q) := by
    have habsmem : MemLp (fun z ↦ |F z|) (parabolicExponent d)
        (volume.restrict Q) := by
      simpa using hFmem.norm
    rw [show Fabs = D⁻¹ • fun z ↦ |F z| by
      funext z
      dsimp only [Fabs]
      simp [div_eq_mul_inv]
      ring]
    exact habsmem.const_smul D⁻¹
  have hFabstop : parabolicELpNormOn d Fabs Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFabsmem.eLpNorm_ne_top
  have hwnonneg : IsNonnegativeOn w Q := by
    intro z hz
    dsimp [w]
    exact div_nonneg (sub_nonneg.mpr (hM z (hQsubset hz))) hD.le
  have hFabsnonneg : IsNonnegativeOn Fabs Q := by
    intro z _hz
    dsimp [Fabs]
    exact div_nonneg (abs_nonneg (F z)) hD.le
  have hwregular : ContDiffOn Real 2 w U := by
    dsimp only [w]
    exact contDiffOn_const_sub_div
  have hFabscontinuous : ContinuousOn Fabs U := by
    dsimp only [Fabs]
    exact hF.abs.div_const D
  have hwsuper : IsParabolicSupersolutionOn B (fun z ↦ -Fabs z) w Q := by
    dsimp only [Fabs, w]
    exact source_supersolution_const_sub_div hD (by simpa only [Q] using heq)
  have hlow : Q ∩ {z | u z ≤ nu / 2} ⊆ Q ∩ {z | 1 ≤ w z} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change 1 ≤ (M - u z) / D
    apply (le_div_iff₀ hD).mpr
    dsimp [D]
    have huz : u z ≤ nu / 2 := hz.2
    linarith
  have hsuperclosed : Q ∩ {z | 1 ≤ w z} ⊆ Qclosed := fun _ hz ↦ hQsubset hz.1
  have hvolfin : (volume : Measure (TimeVelocity d)) (Q ∩ {z | 1 ≤ w z}) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono hsuperclosed)
  have hcenter : v0 ∈ velocityClosedCube v0 (R / 2) :=
    center_mem_velocityClosedCube
  have hpoint : g ≤ w (t0 + R ^ 2, v0) +
      C * R ^ ((d : Real) / ((d : Real) + 1)) * parabolicLpNormOn d Fabs Q := by
    simpa using hdtp.scaled hR one_pos U B Fabs w hU hclosed hB
      hwregular hFabscontinuous hwnonneg hFabsnonneg hlower hupper hwsuper (hdensity.trans (volume_toReal_mono_of_subset hvolfin hlow))
      v0 hcenter
  have hnorm : parabolicLpNormOn d Fabs Q = D⁻¹ * parabolicLpNormOn d F Q := by
    dsimp only [Fabs]
    exact parabolicLpNormOn_abs_div hD hFmem
  rw [hnorm] at hpoint
  have hterminalBound : w (t0 + R ^ 2, v0) ≤ (M - nu) / D := by
    dsimp only [w]
    apply (div_le_div_iff_of_pos_right hD).mpr
    linarith
  have hmul : g * D ≤ M - nu + C * R ^ ((d : Real) / ((d : Real) + 1)) *
      parabolicLpNormOn d F Q := by
    calc
      g * D ≤ ((M - nu) / D + C * R ^ ((d : Real) / ((d : Real) + 1)) *
          (D⁻¹ * parabolicLpNormOn d F Q)) * D :=
        mul_le_mul_of_nonneg_right (hpoint.trans (add_le_add_left hterminalBound _)) hD.le
      _ = M - nu + C * R ^ ((d : Real) / ((d : Real) + 1)) *
          parabolicLpNormOn d F Q := by
        field_simp [hD.ne']
  have hden : 0 < 2 * (1 - g) := by
    nlinarith
  have hden' := ne_of_gt (sub_pos.mpr hg)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  calc
    nu * (2 - g) ≤ 2 * M * (1 - g) +
        2 * C * R ^ ((d : Real) / ((d : Real) + 1)) * parabolicLpNormOn d F Q := by
      dsimp [D] at hmul
      nlinarith
    _ = (M + (C / (1 - g)) * R ^ ((d : Real) / ((d : Real) + 1)) *
        parabolicLpNormOn d F Q) * (2 * (1 - g)) := by
      field_simp [hden']




private theorem parabolicBox_subset_closedBox {d : ℕ} {vartheta r t0 : ℝ}
    {v0 : PDE.Vec d} :
    parabolicBox vartheta r t0 v0 ⊆ parabolicClosedBox vartheta r t0 v0 := by
  intro z hz
  rcases hz with ⟨⟨hzleft, hzright⟩, hzv⟩
  exact ⟨⟨hzleft.le, hzright.le⟩, fun i ↦ (hzv i).le⟩

private theorem low_density_of_not_high_density {d : ℕ} {R eps t0 beta : ℝ}
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
  let L := Q ∩ {z | q z < eps}
  let H := Q ∩ {z | eps ≤ q z}
  have hL : MeasurableSet L := by
    change MeasurableSet (Q ∩ q ⁻¹' Iio eps)
    exact ((hq.continuousOn.mono hQU).isOpen_inter_preimage (isOpen_parabolicBox 1 R t0 v0)
      isOpen_Iio).measurableSet
  have hQfinite : (volume : Measure (TimeVelocity d)) Q ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono parabolicBox_subset_closedBox)
  have hLsubset : L ⊆ Q := fun _ hz ↦ hz.1
  have hinter : Q ∩ L = L := inter_eq_right.mpr hLsubset
  have hdiff : Q \ L = H := by
    ext z
    simp only [L, H, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hzQ, hzL⟩
      exact ⟨hzQ, le_of_not_gt fun hlt ↦ hzL ⟨hzQ, hlt⟩⟩
    · rintro ⟨hzQ, hqz⟩
      refine ⟨hzQ, ?_⟩
      rintro ⟨_, hlt⟩
      exact (not_lt_of_ge hqz) hlt
  have hdecomp : (volume L).toReal + (volume H).toReal = (volume Q).toReal := by
    simpa only [Measure.real, hinter, hdiff] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hL hQfinite)
  have hhigh : (volume H).toReal < beta * (volume Q).toReal := lt_of_not_ge hnot
  have hlow : (1 - beta) * (volume Q).toReal < (volume L).toReal := by
    nlinarith
  have hsubset : L ⊆ Q ∩ {z | q z ≤ eps} := by
    intro z hz
    exact ⟨hz.1, (show q z < eps from hz.2).le⟩
  have htargetFinite : (volume : Measure (TimeVelocity d))
      (Q ∩ {z | q z ≤ eps}) ≠ ⊤ :=
    ne_top_of_le_ne_top hQfinite (measure_mono fun _ hz ↦ hz.1)
  exact hlow.le.trans (ENNReal.toReal_mono htargetFinite (measure_mono hsubset))


private theorem parabolicLpNormOn_mono_of_continuousOn {d : ℕ}
    {F : TimeVelocity d → ℝ} {U S T K : Set (TimeVelocity d)}
    (hF : ContinuousOn F U) (hKU : K ⊆ U) (hKcompact : IsCompact K)
    (hTK : T ⊆ K) (hST : S ⊆ T) :
    parabolicLpNormOn d F S ≤ parabolicLpNormOn d F T := by
  have hFK : ContinuousOn F K := hF.mono hKU
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn hFK
  have hKmem : MemLp F (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hFK.aestronglyMeasurable hKmeas) M ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hM z hz
  have hTmem : MemLp F (parabolicExponent d) (volume.restrict T) :=
    hKmem.mono_measure (Measure.restrict_mono_set volume hTK)
  have hSmem : MemLp F (parabolicExponent d) (volume.restrict S) :=
    hTmem.mono_measure (Measure.restrict_mono_set volume hST)
  have hTtop : parabolicELpNormOn d F T ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hTmem.eLpNorm_ne_top
  have hStop : parabolicELpNormOn d F S ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hSmem.eLpNorm_ne_top
  unfold parabolicLpNormOn
  exact (ENNReal.toReal_le_toReal hStop hTtop).mpr
    (eLpNorm_mono_measure F (Measure.restrict_mono_set volume hST))

private theorem supersolution_of_equation_abs {d : ℕ} {B : CoefficientField d}
    {F q : TimeVelocity d → ℝ} {V : Set (TimeVelocity d)}
    (heq : ∀ z ∈ V, parabolicOperator B q z = F z) :
    IsParabolicSupersolutionOn B (fun z ↦ -|F z|) q V := by
  intro z hz
  rw [heq z hz]
  exact neg_abs_le (F z)

private theorem equation_add_const {d : ℕ} {B : CoefficientField d}
    {F q : TimeVelocity d → ℝ} {V : Set (TimeVelocity d)} {e : ℝ}
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
              C * parabolicLpNormOn d F K  := by
  have parabolicLpNormOn_abs {d : ℕ} (F : TimeVelocity d → ℝ) (S : Set (TimeVelocity d)) (hF : AEStronglyMeasurable F (volume.restrict S)) :
      parabolicLpNormOn d (fun z ↦ |F z|) S = parabolicLpNormOn d F S := by
    unfold parabolicLpNormOn parabolicELpNormOn
    apply congrArg ENNReal.toReal
    have habs : AEStronglyMeasurable (fun z ↦ |F z|) (volume.restrict S) := by
      simpa using hF.norm
    apply eLpNorm_congr_enorm_ae habs hF
    filter_upwards [] with z
    exact Real.enorm_abs (F z)
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
    dsimp [gStar]
    exact sub_pos.mpr hfrac_lt_one
  have hgStar1 : gStar < 1 := by
    dsimp [gStar]
    exact sub_lt_self 1 (div_pos (by norm_num) hden0)
  have hratio_id :
      (2 - gStar) / (2 * (1 - gStar)) = 2 * 2 ^ m + 1 / 2 := by
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
    dsimp [beta]
    ring
  let kappaLG : ℝ := CStar / (1 - gStar)
  have hkappaLG0 : 0 < kappaLG := div_pos hCStar (sub_pos.mpr hgStar1)
  let aPeak : ℝ := 2 ^ m + 1 / 2
  have haPeak : 0 < aPeak := by positivity
  let H : ℝ := 1 + 2 * kappaLG / aPeak
  have hH : 0 < H := by positivity
  obtain ⟨gBeta, Cbeta, hgBeta0, _hgBeta1, hCbeta, hdtpBeta⟩ :=
    exists_sourceDensityToPoint_positive d hd' lam hlam Lam hlamLam beta hbeta0 hbeta1
  let p : ℝ := (d : ℝ) / ((d : ℝ) + 1)
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
  let C : ℝ := H + Cbeta + CP * 2 ^ p
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F hKcompact hKU hU hworkClosed hB hq hF hqnonneg hlowerK hupperK
    heqK hsourcePos j v hv
  let A : ℝ := parabolicLpNormOn d F K
  let G : TimeVelocity d → ℝ := fun z ↦ |F z|
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hG : ContinuousOn G U := hF.abs
  have hworkOpen : IsOpen (parabolicBox 2 2 0 (0 : PDE.Vec d)) :=
    isOpen_parabolicBox 2 2 0 0
  have hworkOpenK : parabolicBox 2 2 0 0 ⊆ K :=
    parabolicBox_subset_closedBox.trans hworkClosed
  have hsourceMem : (4, 0) ∈ parabolicBox 2 2 0 (0 : PDE.Vec d) := by
    rw [mem_parabolicBox_iff]
    norm_num
  have hcontPeak : ContinuousOn q (backwardParabolicClosedBox 1 4 (0 : PDE.Vec d)) :=
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
        simp [velocitySupNorm_eq_norm]]
      exact norm_nonneg _)
  have hs : 0 < s := by
    dsimp [s]
    exact selected_backward_radius_pos hr0lt
  have hsOne : s ≤ 1 := by
    dsimp [s]
    linarith
  have hspow : s ^ p ≤ 1 := Real.rpow_le_one hs.le hsOne hp
  have hu1' : 0 < u1 := by simpa only [u1] using hu1
  have hbasePow : (1 - r0) ^ m ≤ 1 := by
    apply pow_le_one₀
    · linarith
    · linarith
  have hweightToU1 : q (4, (0 : PDE.Vec d)) ≤ u1 := by
    calc
      q (4, (0 : PDE.Vec d)) ≤ (1 - r0) ^ m * u1 := hweight
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
        have hCPpow : 0 ≤ CP * (2 : ℝ) ^ p :=
          mul_nonneg hCP.le (Real.rpow_nonneg (by norm_num) _)
        dsimp [C]
        exact (le_add_of_nonneg_right hCbeta).trans (le_add_of_nonneg_right hCPpow)
      have hCA : H * A ≤ C * A := mul_le_mul_of_nonneg_right hHC hA
      calc
        hBox * q (4, (0 : PDE.Vec d)) ≤ hBox * (H * A) :=
          mul_le_mul_of_nonneg_left hsourceBound hhBox0.le
        _ ≤ H * A := by nlinarith [hH, hA]
        _ ≤ C * A := hCA
        _ ≤ q (localHarnackTerminalApprox j, v) + C * A :=
          le_add_of_nonneg_left htargetNonneg
  intro hhigh
  have hhighDensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 s tBase v1)).toReal ≤
      ((volume : Measure (TimeVelocity d))
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
          dsimp [aPeak]
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
                  1 * parabolicLpNormOn d F (parabolicBox 1 s tBase v1) := by
                exact mul_le_mul_of_nonneg_right hspow ENNReal.toReal_nonneg
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
      exact (not_lt_of_ge hmain) (hstrict.trans hcontra)
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
    have hpoint := (hdtpBeta.scaled hs (by linarith : 0 < u1 / 2) U B G q hU hclosedSmallU hB hq hG (hqnonneg.mono hopenSmall) (fun z _ ↦ abs_nonneg (F z)) (hlowerK.mono hopenSmall) (hupperK.mono hopenSmall) (supersolution_of_equation_abs fun z hz ↦ heqK z (hopenSmall hz)) hhighDensity) w hw
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
    have hterm' : Cbeta * s ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d G (parabolicBox 1 s tBase v1) ≤ eD := by
      simpa only [p] using hterm
    exact hpoint.trans (by simpa only [add_comm] using add_le_add_left hterm' (q (t1, w)))
  obtain ⟨htauLower, htauUpper, hwidth, hbase, htarget, hcorridor⟩ :=
    selected_localHarnack_corridor hpeakPoint hr0eq hr0lt hv
  let tau : ℝ := selectedLocalHarnackForwardTime t1 j
  let lower : PDE.Vec d := localHarnackCorridorLower v1 v
  let upper : PDE.Vec d := localHarnackCorridorUpper v1 v
  let UHat : Set (TimeVelocity d) := localHarnackCorridorNeighborhood t1
  let BHat : CoefficientField d := pullbackCoefficient B t1 (0 : PDE.Vec d) 1
  let qHat : TimeVelocity d → ℝ := pullbackScalar (fun z ↦ q z + eD) t1 (0 : PDE.Vec d) 1
  let GHat : TimeVelocity d → ℝ := pullbackScalar G t1 (0 : PDE.Vec d) 1
  have hUHat : IsOpen UHat := by
    dsimp [UHat, localHarnackCorridorNeighborhood]
    exact hworkOpen.preimage (contDiff_parabolicAffine t1 0 1).continuous
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
  have hrectWork : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1)
      (parabolicRectangle tau lower upper) (parabolicBox 2 2 0 0) :=
    fun _ hz ↦ hmapHat (hrect hz)
  have hrectK : MapsTo (parabolicAffine t1 (0 : PDE.Vec d) 1)
      (parabolicRectangle tau lower upper) K := fun _ hz ↦ hworkOpenK (hrectWork hz)
  have hBHat : IsContinuousCoefficientOn BHat UHat := hB.pullback hmapHatU
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
  have hlowerHat : HasLowerEllipticityOn lam BHat (parabolicRectangle tau lower upper) :=
    hlowerK.pullback hrectK
  have hupperHat : HasUpperEllipticityOn Lam BHat (parabolicRectangle tau lower upper) :=
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
    simpa [one_pow] using IsParabolicSupersolutionOn.pullback
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
            (parabolicAffine t1 (0 : PDE.Vec d) 1 '' parabolicRectangle tau lower upper) := by
        simpa [GHat, pullbackScalar, Function.comp_def] using
          (parabolicLpNormOn_pullback t1 (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1)
            G (parabolicRectangle tau lower upper))
      _ = parabolicLpNormOn d G
            (parabolicAffine t1 (0 : PDE.Vec d) 1 '' parabolicRectangle tau lower upper) := by simp
      _ ≤ parabolicLpNormOn d G K :=
        parabolicLpNormOn_mono_of_continuousOn hG hKU hKcompact Subset.rfl himageK
      _ = A := parabolicLpNormOn_abs F K
          ((hF.mono hKU).aestronglyMeasurable hKcompact.measurableSet)
  have hweight' : q (4, (0 : PDE.Vec d)) ≤ (1 - r0) ^ m * u1 := by
    simpa only [u1] using hweight
  have hfactor : hBox * q (4, (0 : PDE.Vec d)) ≤
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
      hBox * q (4, (0 : PDE.Vec d)) ≤ hBox * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_left hweight' hhBox0.le
      _ ≤ c * ((1 - r0) ^ m * u1) :=
        mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg (by linarith) _) hu1'.le)
      _ = delta * ((1 - r0) / 8) ^ m * ell := by
        dsimp [c, ell]
        rw [hpowEq]
        calc
          delta * (1 / 8 : ℝ) ^ m * (gBeta / 2) *
              (8 ^ m * ((1 - r0) / 8) ^ m * u1) =
              delta * (gBeta / 2) * ((1 / 8 : ℝ) ^ m * 8 ^ m) *
                ((1 - r0) / 8) ^ m * u1 := by ring
          _ = delta * ((1 - r0) / 8) ^ m * ((u1 / 2) * gBeta) := by
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
          dsimp [eD]
          ring
  calc
    hBox * q (4, (0 : PDE.Vec d)) ≤ delta * ((1 - r0) / 8) ^ m * ell := hfactor
    _ ≤ q (localHarnackTerminalApprox j, v) + (Cbeta + CP * (2 : ℝ) ^ p) * A := hpropBound
    _ ≤ q (localHarnackTerminalApprox j, v) + C * A := by
      have hsmallC : Cbeta + CP * (2 : ℝ) ^ p ≤ C := by
        dsimp [C]
        calc
          Cbeta + CP * (2 : ℝ) ^ p = 0 + (Cbeta + CP * (2 : ℝ) ^ p) := by ring
          _ ≤ H + (Cbeta + CP * (2 : ℝ) ^ p) := by
            simpa only [add_comm] using add_le_add_right hH.le (Cbeta + CP * (2 : ℝ) ^ p)
          _ = H + Cbeta + CP * (2 : ℝ) ^ p := by ring
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hsmallC hA)
          (q (localHarnackTerminalApprox j, v))


end HypoellipticAleksandrov.Parabolic

