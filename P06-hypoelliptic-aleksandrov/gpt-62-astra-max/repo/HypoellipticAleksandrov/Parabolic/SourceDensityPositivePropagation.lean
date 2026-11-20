module

public import HypoellipticAleksandrov.Parabolic.DensityPositiveGeometry
public import HypoellipticAleksandrov.Parabolic.SourceDensityToPoint
public import HypoellipticAleksandrov.Parabolic.SourceForwardPropagation
public import HypoellipticAleksandrov.Measure.InkSpotsSelection

/-!
# Source-aware uniform cap propagation for positive density

This module propagates a supplied source-aware near-one density estimate to
the terminal Q3 region.  The source error is compared internally with the
single unit-box norm appearing in the public conclusion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

section
variable {d : ℕ} {a : ℝ} {u : TimeVelocity d → ℝ} {q : InkSpotsBox d}

/-- A genuine source box contained in the unit box has radius at most one. -/
private theorem inkSpots_radius_le_one
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    q.radius ≤ 1 := by
  have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hR hq
  have htop : (q.baseTime + q.radius ^ 2, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    simp [hR.le]
  have htopUnit := hclosed htop
  rw [mem_parabolicClosedBox_iff] at htopUnit
  have hbottom : (q.baseTime, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    simp [hR.le]
  have hbottomUnit := hclosed hbottom
  rw [mem_parabolicClosedBox_iff] at hbottomUnit
  nlinarith

/-- A closed translated propagation rectangle inside the closed unit box has
its open rectangle inside the open unit box. -/
private theorem mapsTo_openRectangle_of_closedRectangle {tau t0 : ℝ} {v0 lower upper : PDE.Vec d}
    (htau : 0 < tau)
    (hclosed : parabolicAffine (d := d) t0 v0 1 ''
      parabolicClosedRectangle tau lower upper ⊆ parabolicClosedBox 1 1 0 0) :
    MapsTo (parabolicAffine t0 v0 1) (parabolicRectangle tau lower upper)
      (parabolicBox 1 1 0 0) := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_parabolicRectangle_iff] at hz
  rw [mem_parabolicBox_iff]
  have hbot :=
    hclosed ⟨(0, v), by
      rw [mem_parabolicClosedRectangle_iff]
      exact ⟨le_rfl, htau.le, fun i => ⟨(hz.2.2 i).1.le, (hz.2.2 i).2.le⟩⟩, rfl⟩
  have htop :=
    hclosed ⟨(tau, v), by
      rw [mem_parabolicClosedRectangle_iff]
      exact ⟨htau.le, le_rfl, fun i => ⟨(hz.2.2 i).1.le, (hz.2.2 i).2.le⟩⟩, rfl⟩
  rw [mem_parabolicClosedBox_iff] at hbot htop
  refine ⟨?_, ?_, ?_⟩
  · grind [parabolicAffine]
  · grind [parabolicAffine]
  · intro i
    have hlower :=
      hclosed ⟨(t, lower), by
        rw [mem_parabolicClosedRectangle_iff]
        exact ⟨hz.1.le, hz.2.1.le, fun j =>
          ⟨le_rfl, (hz.2.2 j).1.le.trans (hz.2.2 j).2.le⟩⟩, rfl⟩
    have hupper :=
      hclosed ⟨(t, upper), by
        rw [mem_parabolicClosedRectangle_iff]
        exact ⟨hz.1.le, hz.2.1.le, fun j =>
          ⟨(hz.2.2 j).1.le.trans (hz.2.2 j).2.le, le_rfl⟩⟩, rfl⟩
    rw [mem_parabolicClosedBox_iff] at hlower hupper
    have hlow : -1 ≤ v0 i + lower i := by
      simpa [parabolicAffine] using (abs_le.mp (hlower.2.2 i)).1
    have hupp : v0 i + upper i ≤ 1 := by
      simpa [parabolicAffine] using (abs_le.mp (hupper.2.2 i)).2
    have hvlower := (hz.2.2 i).1
    have hvupper := (hz.2.2 i).2
    dsimp [parabolicAffine]
    rw [abs_lt]
    constructor <;> linarith

/-- Strict density gives the squared density required by the source seed. -/
private theorem inkSpots_squared_density
    (ha0 : 0 < a) (ha1 : a < 1)
    (hq : inkSpotsStrictDense (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) a q) :
    a ^ 2 * (volume (parabolicBox 1 q.radius q.baseTime q.center)).toReal ≤
      (volume (parabolicBox 1 q.radius q.baseTime q.center ∩
        {z | 1 ≤ u z})).toReal := by
  have hrewrite : inkSpotsSourceBox q ∩
      (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) =
      inkSpotsSourceBox q ∩ {z | 1 ≤ u z} := by
    ext z
    simp only [mem_inter_iff]
    constructor
    · grind
    · rintro ⟨hz, hlevel⟩
      exact ⟨hz, hq.2.1 hz, hlevel⟩
  have hstrict := hq.2.2
  rw [hrewrite] at hstrict
  have hsq : a ^ 2 ≤ a := by
    nlinarith
  simpa only [inkSpotsSourceBox] using
    (le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsq ENNReal.toReal_nonneg) hstrict))

/-- An open parabolic box is contained in its closed counterpart. -/
private theorem parabolicBox_subset_closedBox
    {vartheta r t0 : ℝ} {v0 : PDE.Vec d} :
    parabolicBox vartheta r t0 v0 ⊆ parabolicClosedBox vartheta r t0 v0 := by
  intro z hz
  rcases hz with ⟨⟨hzleft, hzright⟩, hzv⟩
  exact ⟨⟨hzleft.le, hzright.le⟩, fun i => (hzv i).le⟩

/-- Continuous data on a compact collar makes restricted real `Lᵖ` norms
monotone for nested carriers. -/
private theorem parabolicLpNormOn_mono_of_continuousOn {F : TimeVelocity d → ℝ} {U S T K : Set (TimeVelocity d)}
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

end

/-- A source-aware near-one density seed gives a uniform cap on every clipped
terminal Q3 point, with the source error measured on the unit box. -/
theorem exists_inkSpotsQ3_source_density_cap
    (d : Nat) (hd : 0 < d) (lam : Real) (hlam : 0 < lam) (Lam : Real)
    (hlamLam : lam ≤ Lam) (a eta zeta C₀ : Real)
    (ha0 : 0 < a) (ha1 : a < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (hC₀ : 0 ≤ C₀)
    (hseed : SourceDensityToPoint d lam Lam (a ^ 2) (1 / 2) C₀) :
    ∃ h C : Real, 0 < h ∧ 0 ≤ C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (F u : TimeVelocity d → Real),
        IsOpen U →
        parabolicClosedBox 1 1 0 0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn Real 2 u U →
        ContinuousOn F U →
        IsNonnegativeOn u (parabolicBox 1 1 0 0) →
        IsNonnegativeOn F (parabolicBox 1 1 0 0) →
        HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0) →
        HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0) →
        IsParabolicSupersolutionOn B (fun z ↦ -F z) u
          (parabolicBox 1 1 0 0) →
        ∀ q : InkSpotsBox d,
          inkSpotsStrictDense
            (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) a q →
          ∀ z ∈ inkSpotsQ3 eta zeta q ∩ inkSpotsUnitBox d,
            h ≤ u z + C * parabolicLpNormOn d F
              (parabolicBox 1 1 0 0) := by
  let kappa := min (eta / 4) (1 - zeta)
  have hkappa0 : 0 < kappa := by
    positivity
  obtain ⟨delta, hdelta, m, hm, Cfp, hCfp, hprop⟩ :=
    exists_forward_propagation_source_constants d hd lam Lam kappa hlam hlamLam
      hkappa0 ((min_le_left _ _).trans (by nlinarith [heta1]))
  refine ⟨min (1 / 4) (delta * (1 / 2) ^ m * (1 / 4)),
    max C₀ Cfp, ?_, le_max_of_le_left hC₀, ?_⟩
  · positivity
  intro U B F u hU hunit hB hu hF hnonneg hFnonneg hlower hupper hsuper q hq z hz
  have hR := hq.1
  have hRone := inkSpots_radius_le_one hR hq.2.1
  have hsourceNorm : parabolicLpNormOn d F
      (parabolicBox 1 q.radius q.baseTime q.center) ≤
      parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    apply parabolicLpNormOn_mono_of_continuousOn hF hunit
      (isCompact_parabolicClosedBox 1 1 0 0)
    · exact parabolicBox_subset_closedBox
    · exact hq.2.1
  let p : ℝ := d / (d + 1)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hRpow :=
    Real.rpow_le_one hR.le hRone hp0
  have hsourceNormNonneg : 0 ≤ parabolicLpNormOn d F
      (parabolicBox 1 q.radius q.baseTime q.center) := ENNReal.toReal_nonneg
  have hseedErrorBound : C₀ * q.radius ^ p *
      parabolicLpNormOn d F (parabolicBox 1 q.radius q.baseTime q.center) ≤
      max C₀ Cfp * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    bound
  have hcap := hseed.scaled hR (by norm_num : (0 : ℝ) < 1) U B F u hU
    ((inkSpots_closedSourceBox_subset_closedUnitBox d q hR hq.2.1).trans hunit) hB hu hF
    (by exact hnonneg.mono hq.2.1)
    (by exact hFnonneg.mono hq.2.1)
    (by exact hlower.mono hq.2.1)
    (by exact hupper.mono hq.2.1)
    (by exact hsuper.mono hq.2.1)
    (inkSpots_squared_density ha0 ha1 hq)
  by_cases hlarge : (1 / 4) ≤ C₀ * q.radius ^ p *
      parabolicLpNormOn d F (parabolicBox 1 q.radius q.baseTime q.center)
  · have hunitError :=
      hlarge.trans hseedErrorBound
    have huzero := hnonneg z hz.2
    bound
  · have hsmall := lt_of_not_ge hlarge
    have hseedPointwise : ∀ v ∈ velocityClosedCube q.center (q.radius / 2),
        (1 / 4) < u (q.baseTime + q.radius ^ 2, v) := by
      grind
    obtain ⟨lower, upper, htLower, htUpper, hwidth, hbase, htarget, hrect⟩ :=
      exists_inkSpotsQ3_forward_corridor d eta zeta kappa q z heta0 heta1 hzeta0
        hzeta1 (by rfl) hR hq.2.1 hz
    let t0 := q.baseTime + q.radius ^ 2
    let tau := z.1 - t0
    let V := parabolicAffine t0 q.center 1 ⁻¹' U
    have hclosedV : parabolicClosedRectangle tau lower upper ⊆ V := by
      grind
    have hmapU : MapsTo (parabolicAffine t0 q.center 1) V U := fun _ hy => hy
    have htau0 : 0 < tau := by
      dsimp [tau, t0]
      nlinarith [htLower]
    have hmapOpen : MapsTo (parabolicAffine t0 q.center 1)
        (parabolicRectangle tau lower upper) (parabolicBox 1 1 0 0) := by
      apply mapsTo_openRectangle_of_closedRectangle htau0
      intro y hy
      exact hrect hy
    have hsuperPull : IsParabolicSupersolutionOn (pullbackCoefficient B t0 q.center 1)
        (fun y ↦ -pullbackScalar F t0 q.center 1 y)
        (pullbackScalar u t0 q.center 1) (parabolicRectangle tau lower upper) := by
      simpa using
        IsParabolicSupersolutionOn.pullback
          (U := parabolicBox 1 1 0 0) (V := parabolicRectangle tau lower upper)
          (isOpen_parabolicBox 1 1 0 0) (hu.mono (fun x hx => hunit
            (parabolicBox_subset_closedBox hx))) hsuper hmapOpen
    have hseedProp : ∀ v ∈ velocityClosedRectangle lower upper,
        v ∈ velocityCube 0 ((1 / 2) * q.radius) →
        (1 / 4) ≤ pullbackScalar u t0 q.center 1 (0, v) := by
      intro v _ hv
      have hv' : q.center + 1 • v ∈ velocityClosedCube q.center (q.radius / 2) := by
        intro i
        simpa [one_smul, div_eq_mul_inv, mul_comm] using (hv i).le
      have hpoint := (hseedPointwise (q.center + 1 • v) hv').le
      simpa [parabolicAffine] using hpoint
    have hforward := hprop q.radius (pullbackCoefficient B t0 q.center 1)
      0 lower upper tau V (pullbackScalar F t0 q.center 1)
      (pullbackScalar u t0 q.center 1) (1 / 2) (1 / 4) tau (z.2 - q.center)
      hR (hRone.trans (by norm_num)) (by exact htLower)
      (by exact htUpper) hwidth hbase (hU.preimage (contDiff_parabolicAffine t0 q.center 1).continuous) hclosedV
      (hB.pullback hmapU) (ContDiffOn.pullbackScalar hu hmapU)
      (hF.comp (contDiff_parabolicAffine t0 q.center 1).continuous.continuousOn hmapU)
      (hnonneg.pullbackScalar hmapOpen) (hlower.pullback hmapOpen)
      (hupper.pullback hmapOpen) (hFnonneg.pullbackScalar hmapOpen) hsuperPull
      (by norm_num) (by norm_num) (by norm_num) hseedProp
      (by exact htLower) (by rfl) htarget
    have hforwardNorm : parabolicLpNormOn d (pullbackScalar F t0 q.center 1)
        (parabolicRectangle tau lower upper) ≤
        parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      rw [show pullbackScalar F t0 q.center 1 =
          fun y ↦ 1 ^ 2 * F (parabolicAffine t0 q.center 1 y) by
            funext y; simp]
      rw [parabolicLpNormOn_pullback t0 q.center (by norm_num)]
      simp only [Real.one_rpow, one_mul]
      apply parabolicLpNormOn_mono_of_continuousOn hF hunit
        (isCompact_parabolicClosedBox 1 1 0 0)
      · exact parabolicBox_subset_closedBox
      · rintro y ⟨x, hx, rfl⟩
        exact hmapOpen hx
    have hforwardNormNonneg : 0 ≤ parabolicLpNormOn d
        (pullbackScalar F t0 q.center 1) (parabolicRectangle tau lower upper) :=
      ENNReal.toReal_nonneg
    have hforwardErrorBound : Cfp * q.radius ^ p *
        parabolicLpNormOn d (pullbackScalar F t0 q.center 1)
          (parabolicRectangle tau lower upper) ≤
        max C₀ Cfp * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      calc
        Cfp * q.radius ^ p * parabolicLpNormOn d (pullbackScalar F t0 q.center 1)
            (parabolicRectangle tau lower upper) ≤
            Cfp * 1 * parabolicLpNormOn d (pullbackScalar F t0 q.center 1)
              (parabolicRectangle tau lower upper) := by gcongr
        _ = Cfp * parabolicLpNormOn d (pullbackScalar F t0 q.center 1)
            (parabolicRectangle tau lower upper) := by ring
        _ ≤ Cfp * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by gcongr
        _ ≤ max C₀ Cfp * parabolicLpNormOn d F
            (parabolicBox 1 1 0 0) := by
          bound
    have hmain : delta * (1 / 2) ^ m * (1 / 4) <
        u z + Cfp * q.radius ^ p *
          parabolicLpNormOn d (pullbackScalar F t0 q.center 1)
            (parabolicRectangle tau lower upper) := by
      dsimp [p]
      simpa [pullbackScalar, parabolicAffine, tau, t0] using hforward
    exact (min_le_right _ _).trans
      (hmain.le.trans (by bound))

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

section
variable {d : ℕ} {xi : ℝ} {u : TimeVelocity d → ℝ} {q : InkSpotsBox d}

/-- The terminal time of a genuine source box in the unit box is at most one. -/
private theorem inkSpots_terminal_le_one
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    q.baseTime + q.radius ^ 2 ≤ 1 := by
  have htop : (q.baseTime + q.radius ^ 2, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    simp [hR.le]
  have htopUnit := (inkSpots_closedSourceBox_subset_closedUnitBox d q hR hq) htop
  aesop

/-- Strict density on a source box supplies the corresponding non-strict
density statement at the same level. -/
private theorem inkSpots_strict_density_nonneg
    (hq : inkSpotsStrictDense (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) xi q) :
    xi * (volume (parabolicBox 1 q.radius q.baseTime q.center)).toReal ≤
      (volume (parabolicBox 1 q.radius q.baseTime q.center ∩
        {z | 1 ≤ u z})).toReal := by
  have hrewrite : inkSpotsSourceBox q ∩
      (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) =
      inkSpotsSourceBox q ∩ {z | 1 ≤ u z} := by
    ext z
    simp only [mem_inter_iff]
    constructor
    · grind
    · rintro ⟨hz, hlevel⟩
      exact ⟨hz, hq.2.1 hz, hlevel⟩
  have hstrict := hq.2.2
  rw [hrewrite] at hstrict
  exact hstrict.le

end

/-- A selected forward crossing propagates a source-aware near-one density cap
to the terminal half-cube, with its sole source error measured on the unit
box. -/
theorem exists_selected_inkSpots_source_density_cap
    (d : Nat) (hd : 0 < d) (lam : Real) (hlam : 0 < lam) (Lam : Real)
    (hlamLam : lam ≤ Lam) (a eta c C₀ : Real)
    (ha0 : 0 < a) (ha1 : a < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hseed : SourceDensityToPoint d lam Lam (a ^ 2) (1 / 2) C₀) :
    ∃ h C : Real, 0 < h ∧ 0 ≤ C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (F u : TimeVelocity d → Real),
        IsOpen U →
        parabolicClosedBox 1 1 0 0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn Real 2 u U →
        ContinuousOn F U →
        IsNonnegativeOn u (parabolicBox 1 1 0 0) →
        IsNonnegativeOn F (parabolicBox 1 1 0 0) →
        HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0) →
        HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0) →
        IsParabolicSupersolutionOn B (fun z ↦ -F z) u
          (parabolicBox 1 1 0 0) →
        ∀ (q : InkSpotsBox d) (w : PDE.Vec d),
          inkSpotsStrictDense
            (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) a q →
          (1 + c, w) ∈ inkSpotsQ2 eta q →
          ∀ v ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2),
            h ≤ u (1, v) + C * parabolicLpNormOn d F
              (parabolicBox 1 1 0 0) := by
  let alpha := (1 + a) ^ (-(1 / ((d : ℝ) + 2)))
  let R0 := Real.sqrt (eta * c / 4)
  let kappa := (1 - alpha ^ 2) * R0 ^ 2
  have halpha0 : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halpha1 : alpha < 1 := by
    dsimp [alpha]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · linarith
    · exact neg_lt_zero.mpr (one_div_pos.mpr (by positivity))
  have hR0sq : R0 ^ 2 = eta * c / 4 := by
    rw [Real.sq_sqrt (by positivity)]
  have hR0pos : 0 < R0 := by
    positivity
  let Admissible := ∃ (U : Set (TimeVelocity d)) (B : CoefficientField d)
    (F u : TimeVelocity d → Real),
    IsOpen U ∧ parabolicClosedBox 1 1 0 0 ⊆ U ∧
    IsContinuousCoefficientOn B U ∧ ContDiffOn Real 2 u U ∧ ContinuousOn F U ∧
    IsNonnegativeOn u (parabolicBox 1 1 0 0) ∧
    IsNonnegativeOn F (parabolicBox 1 1 0 0) ∧
    HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0) ∧
    HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0) ∧
    IsParabolicSupersolutionOn B (fun z ↦ -F z) u
      (parabolicBox 1 1 0 0) ∧
    ∃ (q : InkSpotsBox d) (w : PDE.Vec d),
      inkSpotsStrictDense (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) a q ∧
      (1 + c, w) ∈ inkSpotsQ2 eta q
  by_cases hnone : ¬ Admissible
  · refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    grind
  obtain ⟨U0, B0, F0, u0, hU0, hunit0, hB0, hu0, hF0, hnonneg0, hFnonneg0,
    hlower0, hupper0, hsuper0, q0, w0, hq0, hcross0⟩ := not_not.mp hnone
  have hterminal0 :=
    inkSpots_terminal_le_one hq0.1 hq0.2.1
  have hcrossUpper0 : 1 + c < q0.baseTime + q0.radius ^ 2 +
      4 * q0.radius ^ 2 / eta := (mem_inkSpotsQ2_iff.mp hcross0).2.1
  have hR0ltSq : R0 ^ 2 < q0.radius ^ 2 := by
    rw [hR0sq]
    have hspan : c < 4 * q0.radius ^ 2 / eta := by linarith
    rw [lt_div_iff₀ heta0] at hspan
    nlinarith
  have hR0sqLtOne : R0 ^ 2 < 1 := by
    have hq0sq : q0.radius ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hq0.1.le (by norm_num)).2 (inkSpots_radius_le_one hq0.1 hq0.2.1)
    exact hR0ltSq.trans_le hq0sq
  have hkappa0 : 0 < kappa := by
    dsimp [kappa]
    exact mul_pos (by nlinarith [sq_pos_of_pos halpha0]) (sq_pos_of_pos hR0pos)
  have hkappa1 : kappa ≤ 1 := by
    dsimp [kappa]
    have hfactor : 0 < 1 - alpha ^ 2 := by nlinarith [sq_pos_of_pos halpha0]
    have hfactorOne : 1 - alpha ^ 2 < 1 := by nlinarith [sq_nonneg alpha]
    nlinarith
  obtain ⟨deltaS, hdeltaS, mS, hmS, CfpS, hCfpS, hprop⟩ :=
    exists_forward_propagation_source_constants d hd lam Lam kappa
      hlam hlamLam hkappa0 hkappa1
  refine ⟨min (1 / 4) (deltaS * (alpha / 2) ^ mS * (1 / 4)),
    max C₀ CfpS, ?_, le_max_of_le_left hC₀, ?_⟩
  · positivity
  intro U B F u hU hunit hB hu hF hnonneg hFnonneg hlower hupper hsuper q w hq
    hcross v hv
  have hR := hq.1
  have hRone := inkSpots_radius_le_one hR hq.2.1
  have hshrink :=
    inkSpotsStrictDense_shrunkSourceBox d _ a alpha q ha0 ha1 (by rfl) hq
  have hshrinkR : 0 < (inkSpotsShrunkSourceBox alpha q).radius := hshrink.1
  have hshrinkRone :=
    inkSpots_radius_le_one hshrinkR hshrink.2.1
  have hshrinkNorm : parabolicLpNormOn d F
      (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
        (inkSpotsShrunkSourceBox alpha q).baseTime
        (inkSpotsShrunkSourceBox alpha q).center) ≤
      parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    apply parabolicLpNormOn_mono_of_continuousOn hF hunit
      (isCompact_parabolicClosedBox 1 1 0 0)
    · exact parabolicBox_subset_closedBox
    · exact hshrink.2.1
  let p : ℝ := d / (d + 1)
  have hp0 : 0 ≤ p := by
    positivity
  have hshrinkRpow :=
    Real.rpow_le_one hshrinkR.le hshrinkRone hp0
  have hshrinkNormNonneg : 0 ≤ parabolicLpNormOn d F
      (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
        (inkSpotsShrunkSourceBox alpha q).baseTime
        (inkSpotsShrunkSourceBox alpha q).center) := ENNReal.toReal_nonneg
  have hseedErrorBound : C₀ * (inkSpotsShrunkSourceBox alpha q).radius ^ p *
      parabolicLpNormOn d F
        (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
          (inkSpotsShrunkSourceBox alpha q).baseTime
          (inkSpotsShrunkSourceBox alpha q).center) ≤
      max C₀ CfpS * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    bound
  have hcap := hseed.scaled hshrinkR (by norm_num : (0 : ℝ) < 1) U B F u hU
    ((inkSpots_closedSourceBox_subset_closedUnitBox d (inkSpotsShrunkSourceBox alpha q) hshrinkR hshrink.2.1).trans hunit) hB hu hF
    (by exact hnonneg.mono hshrink.2.1)
    (by exact hFnonneg.mono hshrink.2.1)
    (by exact hlower.mono hshrink.2.1)
    (by exact hupper.mono hshrink.2.1)
    (by exact hsuper.mono hshrink.2.1)
    (inkSpots_strict_density_nonneg hshrink)
  by_cases hlarge : (1 / 4) ≤ C₀ *
      (inkSpotsShrunkSourceBox alpha q).radius ^ p * parabolicLpNormOn d F
        (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
          (inkSpotsShrunkSourceBox alpha q).baseTime
          (inkSpotsShrunkSourceBox alpha q).center)
  · have htargetClosed : (1, v) ∈ closure (parabolicBox 1 1 0 0) := by
      rw [closure_parabolicBox_of_pos (by norm_num) (by norm_num)]
      rw [mem_parabolicClosedBox_iff]
      exact ⟨by norm_num, by norm_num, fun i => (hv i).trans (by norm_num)⟩
    have htargetU : (1, v) ∈ U := by
      apply hunit
      rw [← closure_parabolicBox_of_pos (by norm_num) (by norm_num)]
      exact htargetClosed
    have hmaps : MapsTo u (parabolicBox 1 1 0 0) (Ici 0) := by
      exact hnonneg
    have huvImage :=
      ((contDiffAt_of_contDiffOn_of_isOpen hU hu htargetU).continuousAt).continuousWithinAt.mem_closure htargetClosed hmaps
    have huv : 0 ≤ u (1, v) := by
      simpa using huvImage
    exact (min_le_left _ _).trans (by linarith)
  · have hsmall :=
      lt_of_not_ge hlarge
    have hseedPointwise : ∀ x ∈ velocityClosedCube q.center
        ((inkSpotsShrunkSourceBox alpha q).radius / 2),
        (1 / 4) < u
          ((inkSpotsShrunkSourceBox alpha q).baseTime +
            (inkSpotsShrunkSourceBox alpha q).radius ^ 2, x) := by
      intro x hx
      linarith [hcap x hx]
    obtain ⟨htLower, htUpper, hwidth, hbase, htarget, hrect⟩ :=
      selected_inkSpots_forward_corridor d a eta c alpha R0 kappa q v w ha0 ha1
        heta0 heta1 hc (by rfl) hR0sq hR0pos (by rfl) hR hq.2.1 hv hcross
    let t0 : ℝ := q.baseTime + alpha ^ 2 * q.radius ^ 2
    let tau := 1 - t0
    let V := parabolicAffine t0 0 1 ⁻¹' U
    have hclosedV : parabolicClosedRectangle tau (fun _ => (-1))
        (fun _ => 1) ⊆ V := by
      solve_by_elim
    have hmapU : MapsTo (parabolicAffine t0 0 1) V U := fun _ hy => hy
    have htau0 : 0 < tau := by
      dsimp [tau, t0]
      nlinarith [htLower]
    have hmapOpen : MapsTo (parabolicAffine t0 (0 : PDE.Vec d) 1)
        (parabolicRectangle tau (fun _ => (-1)) (fun _ => (1 : ℝ)))
        (parabolicBox 1 1 0 0) := by
      apply mapsTo_openRectangle_of_closedRectangle htau0
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      solve_by_elim [hrect]
    have hsuperPull : IsParabolicSupersolutionOn (pullbackCoefficient B t0 0 1)
        (fun z ↦ -pullbackScalar F t0 0 1 z) (pullbackScalar u t0 0 1)
        (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) := by
      simpa using
        IsParabolicSupersolutionOn.pullback
          (U := parabolicBox 1 1 0 0)
          (V := parabolicRectangle tau (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
          (isOpen_parabolicBox 1 1 0 0) (hu.mono (fun x hx => hunit
            (parabolicBox_subset_closedBox hx))) hsuper hmapOpen
    have hseedProp : ∀ x ∈ velocityClosedRectangle (fun _ => (-1))
        (fun _ => 1), x ∈ velocityCube q.center ((alpha / 2) * q.radius) →
        (1 / 4) ≤ pullbackScalar u t0 0 1 (0, x) := by
      intro x _ hx
      have hx' : x ∈ velocityClosedCube q.center
          ((inkSpotsShrunkSourceBox alpha q).radius / 2) := by
        intro i
        have hrad : (alpha / 2) * q.radius =
            (inkSpotsShrunkSourceBox alpha q).radius / 2 := by
          simp [inkSpotsShrunkSourceBox]
          ring
        rw [← hrad]
        exact (hx i).le
      have hpoint := (hseedPointwise x hx').le
      simpa [inkSpotsShrunkSourceBox, mul_pow, pullbackScalar, parabolicAffine, t0] using hpoint
    have halphaHalf : 0 < alpha / 2 := by positivity
    have hforward := hprop q.radius (pullbackCoefficient B t0 0 1) q.center
      (fun _ => (-1)) (fun _ => 1) tau V (pullbackScalar F t0 0 1)
      (pullbackScalar u t0 0 1) (alpha / 2) (1 / 4) tau v hR (hRone.trans (by norm_num))
      (by exact htLower) (by exact htUpper)
      hwidth hbase (hU.preimage (contDiff_parabolicAffine t0 0 1).continuous) hclosedV (hB.pullback hmapU) (ContDiffOn.pullbackScalar hu hmapU)
      (hF.comp (contDiff_parabolicAffine t0 0 1).continuous.continuousOn hmapU)
      (hnonneg.pullbackScalar hmapOpen) (hlower.pullback hmapOpen)
      (hupper.pullback hmapOpen) (hFnonneg.pullbackScalar hmapOpen) hsuperPull
      halphaHalf ((div_le_iff₀ (by norm_num)).2 (by linarith [halpha1])) (by norm_num) hseedProp
      (by exact htLower) (by rfl) htarget
    have hforwardNorm : parabolicLpNormOn d (pullbackScalar F t0 0 1)
        (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) ≤
        parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      rw [show pullbackScalar F t0 0 1 =
          fun y ↦ 1 ^ 2 * F (parabolicAffine t0 0 1 y) by
            funext y; simp]
      rw [parabolicLpNormOn_pullback t0 0 (by norm_num)]
      simp only [Real.one_rpow, one_mul]
      apply parabolicLpNormOn_mono_of_continuousOn hF hunit
        (isCompact_parabolicClosedBox 1 1 0 0)
      · exact parabolicBox_subset_closedBox
      · rintro y ⟨x, hx, rfl⟩
        exact hmapOpen hx
    have hRpow := Real.rpow_le_one hR.le hRone hp0
    have hforwardNormNonneg : 0 ≤ parabolicLpNormOn d (pullbackScalar F t0 0 1)
        (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) :=
      ENNReal.toReal_nonneg
    have hforwardErrorBound : CfpS * q.radius ^ p *
        parabolicLpNormOn d (pullbackScalar F t0 0 1)
          (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) ≤
        max C₀ CfpS * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      calc
        CfpS * q.radius ^ p * parabolicLpNormOn d (pullbackScalar F t0 0 1)
            (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) ≤
            CfpS * 1 * parabolicLpNormOn d (pullbackScalar F t0 0 1)
              (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) := by
          gcongr
        _ = CfpS * parabolicLpNormOn d (pullbackScalar F t0 0 1)
            (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) := by
          ring
        _ ≤ CfpS * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by gcongr
        _ ≤ max C₀ CfpS * parabolicLpNormOn d F
            (parabolicBox 1 1 0 0) := by
          bound
    have hmain : deltaS * (alpha / 2) ^ mS * (1 / 4) <
        u (1, v) + CfpS * q.radius ^ p *
          parabolicLpNormOn d (pullbackScalar F t0 0 1)
            (parabolicRectangle tau (fun _ => (-1)) (fun _ => 1)) := by
      simpa [pullbackScalar, parabolicAffine, tau, t0] using hforward
    exact (min_le_right _ _).trans
      (hmain.le.trans (by bound))

end HypoellipticAleksandrov.Parabolic
