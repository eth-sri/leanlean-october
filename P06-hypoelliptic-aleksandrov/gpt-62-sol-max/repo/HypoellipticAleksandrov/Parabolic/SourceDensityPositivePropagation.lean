module

import HypoellipticAleksandrov.Analysis.CompactLp

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
variable {d : ℕ}

/-- Nonnegativity in the open box extends to its terminal half-cube by continuity. -/
theorem nonneg_at_terminal_half_cube {U : Set (TimeVelocity d)} {u : TimeVelocity d → Real}
    (hU : IsOpen U) (hclosed : parabolicClosedBox 1 1 0 0 ⊆ U)
    (hu : ContDiffOn Real 2 u U) (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0))
    (v : PDE.Vec d) (hv : v ∈ velocityClosedCube 0 (1 / 2)) : 0 ≤ u (1, v) := by
  have hmem : (1, v) ∈ parabolicClosedBox 1 1 0 (0 : PDE.Vec d) :=
    mem_parabolicClosedBox_iff.mpr ⟨by norm_num, by norm_num, fun i => (hv i).trans (by norm_num)⟩
  have hcl : (1, v) ∈ closure (parabolicBox 1 1 0 (0 : PDE.Vec d)) := by
    rwa [closure_parabolicBox_of_pos (by norm_num) (by norm_num)]
  have hc := (contDiffAt_of_contDiffOn_of_isOpen hU hu (hclosed hmem)).continuousAt
  simpa only [isClosed_Ici.closure_eq, Set.mem_Ici] using
    hc.continuousWithinAt.mem_closure hcl (show MapsTo u (parabolicBox 1 1 0 0) (Ici 0) from hnonneg)

private theorem interior_parabolicClosedBox {r t a : ℝ} {v : PDE.Vec d} :
    interior (parabolicClosedBox a r t v) = parabolicBox a r t v := by
  have hc : velocityClosedCube v r = pi univ fun i => Icc (v i - r) (v i + r) := by
    ext w
    simp only [mem_velocityClosedCube_iff, mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
    exact forall_congr' fun i => by
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [parabolicClosedBox, parabolicBox, interior_prod_eq, interior_Icc, hc,
    interior_pi_set finite_univ]
  congr 1
  ext w
  simp only [mem_velocityCube_iff, mem_pi, mem_univ, true_implies, interior_Icc, mem_Ioo, abs_lt]
  exact forall_congr' fun i => by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- A closed translated propagation rectangle inside the closed unit box has
its open rectangle inside the open unit box. -/
private theorem mapsTo_openRectangle_of_closedRectangle {tau t0 : ℝ} {v0 lower upper : PDE.Vec d}
    (hclosed : parabolicAffine (d := d) t0 v0 1 ''
      parabolicClosedRectangle tau lower upper ⊆ parabolicClosedBox 1 1 0 0) :
    MapsTo (parabolicAffine t0 v0 1) (parabolicRectangle tau lower upper)
      (parabolicBox 1 1 0 0) := by
  rw [mapsTo_iff_image_subset, ← interior_parabolicClosedBox]
  have he : parabolicAffine t0 v0 1 = (Homeomorph.addLeft (t0, v0) : TimeVelocity d → TimeVelocity d) := by
    ext z <;> simp [parabolicAffine]
  have ho : IsOpen (parabolicAffine t0 v0 1 '' parabolicRectangle tau lower upper) := by
    rw [he]
    exact (Homeomorph.addLeft _).isOpenMap _ (isOpen_parabolicRectangle ..)
  refine interior_maximal ((image_mono ?_).trans hclosed) ho
  intro z hz
  obtain ⟨h₁, h₂, h₃⟩ := mem_parabolicRectangle_iff.mp hz
  exact mem_parabolicClosedRectangle_iff.mpr ⟨h₁.le, h₂.le, fun i => ⟨(h₃ i).1.le, (h₃ i).2.le⟩⟩

/-- Strict density gives the squared density required by the source seed. -/
private theorem inkSpots_squared_density {a : ℝ}
    {u : TimeVelocity d → ℝ} {q : InkSpotsBox d}
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
    · rintro ⟨hz, -, hlevel⟩
      exact ⟨hz, hlevel⟩
    · rintro ⟨hz, hlevel⟩
      exact ⟨hz, hq.2.1 hz, hlevel⟩
  have hstrict := hq.2.2
  rw [hrewrite] at hstrict
  have hsq : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1.le)]
  have hvol : 0 ≤ (volume (inkSpotsSourceBox q)).toReal := ENNReal.toReal_nonneg
  simpa only [inkSpotsSourceBox] using
    (le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsq hvol) hstrict))

/-- Continuous data on a compact collar makes restricted real `Lᵖ` norms
monotone for nested carriers. -/
theorem parabolicLpNormOn_mono_of_continuousOn {F : TimeVelocity d → ℝ} {U S T K : Set (TimeVelocity d)}
    (hF : ContinuousOn F U) (hKU : K ⊆ U) (hKcompact : IsCompact K)
    (hTK : T ⊆ K) (hST : S ⊆ T) :
    parabolicLpNormOn d F S ≤ parabolicLpNormOn d F T := 
  parabolicLpNormOn_mono_measure (Measure.restrict_mono_set volume hST)
    ((Analysis.memLp_restrict_of_isCompact hKcompact (hF.mono hKU) _).mono_measure
      (Measure.restrict_mono_set volume hTK))

end

private theorem scaledSourceError_le {C r N M : ℝ} (hC : 0 ≤ C)
    (hr : r ≤ 1) (hN : 0 ≤ N) (hNM : N ≤ M) : C * r * N ≤ C * M := by
  calc
    C * r * N ≤ C * 1 * N := by gcongr
    _ ≤ C * M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hNM hC

/-- Apply forward propagation at the end of a translated rectangle in the unit box. -/
private theorem forwardSourceInUnit {d : ℕ} {lam Lam kappa delta C : ℝ} {m : ℕ}
    (hprop : ForwardPropagationSourceEstimate d lam Lam kappa delta m C) (hC : 0 ≤ C)
    {U : Set (TimeVelocity d)} {B : CoefficientField d} {F u : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hunit : parabolicClosedBox 1 1 0 0 ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn ℝ 2 u U) (hF : ContinuousOn F U)
    (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0))
    (hFnonneg : IsNonnegativeOn F (parabolicBox 1 1 0 0))
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0))
    (hsuper : IsParabolicSupersolutionOn B (fun z ↦ -F z) u (parabolicBox 1 1 0 0))
    {R t0 tau eps ell : ℝ} {shift v0 lower upper v : PDE.Vec d}
    (hR : 0 < R) (hRone : R ≤ 1) (htau : kappa * R ^ 2 < tau) (htau' : tau ≤ kappa⁻¹ * R ^ 2)
    (hwidth : ∀ i, 2 * kappa * R < upper i - lower i ∧ upper i - lower i ≤ kappa⁻¹ * R)
    (hbase : ∀ i, lower i + kappa * R ≤ v0 i ∧ v0 i < upper i - kappa * R)
    (htarget : ∀ i, lower i + kappa * R < v i ∧ v i < upper i - kappa * R)
    (hrect : parabolicAffine t0 shift 1 '' parabolicClosedRectangle tau lower upper ⊆
      parabolicClosedBox 1 1 0 0)
    (heps : 0 < eps) (heps' : eps ≤ 1) (hell : 0 < ell)
    (hseed : ∀ x ∈ velocityClosedRectangle lower upper, x ∈ velocityCube v0 (eps * R) →
      ell ≤ u (t0, shift + x)) :
    delta * eps ^ m * ell < u (t0 + tau, shift + v) + C * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
  let T := parabolicAffine t0 shift 1
  let V := T ⁻¹' U
  have hV : IsOpen V := hU.preimage (contDiff_parabolicAffine ..).continuous
  have hVU : MapsTo T V U := fun _ hy => hy
  have hclosedV : parabolicClosedRectangle tau lower upper ⊆ V :=
    fun y hy => hunit (hrect ⟨y, hy, rfl⟩)
  have hmapOpen := mapsTo_openRectangle_of_closedRectangle hrect
  have hunitOpen : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U := parabolicBox_subset_closed.trans hunit
  have hsuperPull : IsParabolicSupersolutionOn (pullbackCoefficient B t0 shift 1)
      (fun y ↦ -pullbackScalar F t0 shift 1 y) (pullbackScalar u t0 shift 1)
      (parabolicRectangle tau lower upper) := by
    simpa only [pullbackScalar, Function.comp_def, one_pow, one_mul] using
      IsParabolicSupersolutionOn.pullback (isOpen_parabolicBox 1 1 0 0)
        (hu.mono hunitOpen) hsuper hmapOpen
  have hmain := hprop R (pullbackCoefficient B t0 shift 1) v0 lower upper tau V
    (pullbackScalar F t0 shift 1) (pullbackScalar u t0 shift 1) eps ell tau v hR
    (hRone.trans (by norm_num)) htau htau' hwidth hbase hV hclosedV (hB.pullback hVU)
    (ContDiffOn.pullbackScalar hu hVU) (hF.comp (contDiff_parabolicAffine ..).continuous.continuousOn hVU)
    (hnonneg.pullbackScalar hmapOpen) (hlower.pullback hmapOpen) (hupper.pullback hmapOpen)
    (hFnonneg.pullbackScalar hmapOpen) hsuperPull heps heps' hell
    (fun x hx hx' => by simpa [pullbackScalar, Function.comp_def, parabolicAffine] using hseed x hx hx')
    htau le_rfl htarget
  have he : pullbackScalar F t0 shift 1 = fun y => 1 ^ 2 * F (T y) := by
    simp [pullbackScalar, Function.comp_def, T]
  rw [he, parabolicLpNormOn_pullback t0 shift (by norm_num : (0 : ℝ) < 1)] at hmain
  simp only [Real.one_rpow, one_mul] at hmain
  have hmono := parabolicLpNormOn_mono_of_continuousOn hF hunit
    (isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)) parabolicBox_subset_closed
    (mapsTo_iff_image_subset.mp hmapOpen)
  have hpow : R ^ ((d : ℝ) / ((d : ℝ) + 1)) ≤ 1 := Real.rpow_le_one hR.le hRone (by positivity)
  have huEval : pullbackScalar u t0 shift 1 (tau, v) = u (t0 + tau, shift + v) := by
    simp [pullbackScalar, Function.comp_def, parabolicAffine]
  rw [huEval] at hmain
  exact hmain.trans_le (add_le_add_right (scaledSourceError_le hC hpow ENNReal.toReal_nonneg hmono) _)

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
  let kappa : ℝ := min (eta / 4) (1 - zeta)
  have hkappa0 : 0 < kappa := by
    dsimp [kappa]
    exact lt_min (by positivity) (by linarith)
  have hkappa1 : kappa ≤ 1 := by
    exact (min_le_left _ _).trans (by nlinarith [heta1])
  obtain ⟨delta, hdelta, m, hm, Cfp, hCfp, hprop⟩ :=
    exists_forward_propagation_source_constants d hd lam Lam kappa hlam hlamLam
      hkappa0 hkappa1
  refine ⟨min (1 / 4 : ℝ) (delta * (1 / 2 : ℝ) ^ m * (1 / 4 : ℝ)),
    max C₀ Cfp, ?_, le_max_of_le_left hC₀, ?_⟩
  · exact lt_min (by norm_num)
      (mul_pos (mul_pos hdelta (pow_pos (by norm_num) _)) (by norm_num))
  intro U B F u hU hunit hB hu hF hnonneg hFnonneg hlower hupper hsuper q hq z hz
  have hR : 0 < q.radius := hq.1
  have hRone : q.radius ≤ 1 := (inkSpots_source_bounds hR hq.2.1).2.2.1
  have hsourceClosed : parabolicClosedBox 1 q.radius q.baseTime q.center ⊆ U :=
    (inkSpots_closedSourceBox_subset_closedUnitBox d q hR hq.2.1).trans hunit
  have hsourceNorm : parabolicLpNormOn d F
      (parabolicBox 1 q.radius q.baseTime q.center) ≤
      parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    apply parabolicLpNormOn_mono_of_continuousOn hF hunit
      (isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d))
    · exact _root_.HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed
    · simpa only [inkSpotsSourceBox, inkSpotsUnitBox] using hq.2.1
  let p : ℝ := (d : ℝ) / ((d : ℝ) + 1)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hRpow : q.radius ^ p ≤ 1 :=
    Real.rpow_le_one hR.le hRone hp0
  have hseedErrorBound := (scaledSourceError_le hC₀ hRpow ENNReal.toReal_nonneg hsourceNorm).trans
    (mul_le_mul_of_nonneg_right (le_max_left C₀ Cfp) ENNReal.toReal_nonneg)
  have hcap := hseed.scaled hR (by norm_num : (0 : ℝ) < 1) U B F u hU
    hsourceClosed hB hu hF
    (by simpa only [inkSpotsSourceBox] using hnonneg.mono hq.2.1)
    (by simpa only [inkSpotsSourceBox] using hFnonneg.mono hq.2.1)
    (by simpa only [inkSpotsSourceBox] using hlower.mono hq.2.1)
    (by simpa only [inkSpotsSourceBox] using hupper.mono hq.2.1)
    (by simpa only [inkSpotsSourceBox] using hsuper.mono hq.2.1)
    (inkSpots_squared_density ha0 ha1 hq)
  by_cases hlarge : (1 / 4 : ℝ) ≤ C₀ * q.radius ^ p *
      parabolicLpNormOn d F (parabolicBox 1 q.radius q.baseTime q.center)
  · have hunitError : (1 / 4 : ℝ) ≤ max C₀ Cfp *
        parabolicLpNormOn d F (parabolicBox 1 1 0 0) :=
      hlarge.trans hseedErrorBound
    have huzero : 0 ≤ u z := hnonneg z hz.2
    exact (min_le_left _ _).trans (by linarith)
  · have hsmall : C₀ * q.radius ^ p *
        parabolicLpNormOn d F (parabolicBox 1 q.radius q.baseTime q.center) <
        (1 / 4 : ℝ) := lt_of_not_ge hlarge
    have hseedPointwise : ∀ v ∈ velocityClosedCube q.center (q.radius / 2),
        (1 / 4 : ℝ) < u (q.baseTime + q.radius ^ 2, v) := by
      intro v hv
      have hcapPoint := hcap v hv
      dsimp [p] at hsmall
      linarith
    obtain ⟨lower, upper, htLower, htUpper, hwidth, hbase, htarget, hrect⟩ :=
      exists_inkSpotsQ3_forward_corridor d eta zeta kappa q z heta0 heta1 hzeta0
        hzeta1 (by rfl) hR hq.2.1 hz
    let t0 : ℝ := q.baseTime + q.radius ^ 2
    let tau : ℝ := z.1 - t0
    have hforward := forwardSourceInUnit hprop hCfp.le hU hunit hB hu hF
      hnonneg hFnonneg hlower hupper hsuper (t0 := t0) (tau := tau) hR hRone
      htLower htUpper hwidth hbase htarget hrect
      (eps := (1 / 2 : ℝ)) (ell := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (fun v _ hv => (hseedPointwise (q.center + v) (fun i => by
        simpa [div_eq_mul_inv, mul_comm] using (hv i).le)).le)
    have hmain : delta * (1 / 2 : ℝ) ^ m * (1 / 4 : ℝ) <
        u z + Cfp * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      have ht : t0 + tau = z.1 := by dsimp [tau]; ring
      have hv : q.center + (fun i => z.2 i - q.center i) = z.2 := by
        ext i
        simp [Pi.add_apply]
      rw [ht, hv] at hforward
      exact hforward
    exact (min_le_right _ _).trans (hmain.le.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right (le_max_right C₀ Cfp) ENNReal.toReal_nonneg) _))

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

/-- Strict density on a source box supplies the corresponding non-strict
density statement at the same level. -/
private theorem inkSpots_strict_density_nonneg {d : ℕ} {xi : ℝ}
    {u : TimeVelocity d → ℝ} {q : InkSpotsBox d}
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
    · (intros; simp_all)
    · rintro ⟨hz, hlevel⟩
      exact ⟨hz, hq.2.1 hz, hlevel⟩
  have hstrict := hq.2.2
  rw [hrewrite] at hstrict
  simpa only [inkSpotsSourceBox] using hstrict.le

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
  let alpha : ℝ := (1 + a) ^ (-(1 / ((d : ℝ) + 2)))
  let R0 : ℝ := Real.sqrt (eta * c / 4)
  let kappa : ℝ := (1 - alpha ^ 2) * R0 ^ 2
  have halpha0 : 0 < alpha := by
    dsimp [alpha]
    exact Real.rpow_pos_of_pos (by linarith) _
  have halpha1 : alpha < 1 := by
    dsimp [alpha]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · linarith
    · exact neg_lt_zero.mpr (one_div_pos.mpr (by positivity))
  have hR0sq : R0 ^ 2 = eta * c / 4 := by
    dsimp [R0]
    rw [Real.sq_sqrt (by positivity)]
  have hR0pos : 0 < R0 := by
    dsimp [R0]
    exact Real.sqrt_pos.2 (by positivity)
  let Admissible : Prop := ∃ (U : Set (TimeVelocity d)) (B : CoefficientField d)
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
    intro U B F u hU hunit hB hu hF hnonneg hFnonneg hlower hupper hsuper q w hq
      hcross v hv
    exact False.elim (hnone ⟨U, B, F, u, hU, hunit, hB, hu, hF, hnonneg,
      hFnonneg, hlower, hupper, hsuper, q, w, hq, hcross⟩)
  obtain ⟨U0, B0, F0, u0, hU0, hunit0, hB0, hu0, hF0, hnonneg0, hFnonneg0,
    hlower0, hupper0, hsuper0, q0, w0, hq0, hcross0⟩ := not_not.mp hnone
  have hterminal0 : q0.baseTime + q0.radius ^ 2 ≤ 1 :=
    (inkSpots_source_bounds hq0.1 hq0.2.1).2.1
  have hcrossUpper0 : 1 + c < q0.baseTime + q0.radius ^ 2 +
      4 * q0.radius ^ 2 / eta := by
    exact (mem_inkSpotsQ2_iff.mp hcross0).2.1
  have hR0ltSq : R0 ^ 2 < q0.radius ^ 2 := by
    rw [hR0sq]
    have hspan : c < 4 * q0.radius ^ 2 / eta := by linarith
    rw [lt_div_iff₀ heta0] at hspan
    nlinarith
  have hR0sqLtOne : R0 ^ 2 < 1 := by
    have hq0Rle := (inkSpots_source_bounds hq0.1 hq0.2.1).2.2.1
    have hq0sq : q0.radius ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hq0.1.le (by norm_num : (0 : ℝ) ≤ 1)).2 hq0Rle
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
  refine ⟨min (1 / 4 : ℝ) (deltaS * (alpha / 2) ^ mS * (1 / 4 : ℝ)),
    max C₀ CfpS, ?_, le_max_of_le_left hC₀, ?_⟩
  · exact lt_min (by norm_num)
      (mul_pos (mul_pos hdeltaS (pow_pos (by positivity) _)) (by norm_num))
  intro U B F u hU hunit hB hu hF hnonneg hFnonneg hlower hupper hsuper q w hq
    hcross v hv
  have hR : 0 < q.radius := hq.1
  have hRone : q.radius ≤ 1 := (inkSpots_source_bounds hR hq.2.1).2.2.1
  have hshrink : inkSpotsStrictDense (inkSpotsUnitBox d ∩ {z | 1 ≤ u z})
      (a ^ 2) (inkSpotsShrunkSourceBox alpha q) :=
    inkSpotsStrictDense_shrunkSourceBox d _ a alpha q ha0 ha1 (by rfl) hq
  have hshrinkR : 0 < (inkSpotsShrunkSourceBox alpha q).radius := hshrink.1
  have hshrinkRone : (inkSpotsShrunkSourceBox alpha q).radius ≤ 1 :=
    (inkSpots_source_bounds hshrinkR hshrink.2.1).2.2.1
  have hsourceClosed : parabolicClosedBox 1 (inkSpotsShrunkSourceBox alpha q).radius
      (inkSpotsShrunkSourceBox alpha q).baseTime
      (inkSpotsShrunkSourceBox alpha q).center ⊆ U :=
    (inkSpots_closedSourceBox_subset_closedUnitBox d (inkSpotsShrunkSourceBox alpha q)
      hshrinkR hshrink.2.1).trans hunit
  have hshrinkNorm : parabolicLpNormOn d F
      (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
        (inkSpotsShrunkSourceBox alpha q).baseTime
        (inkSpotsShrunkSourceBox alpha q).center) ≤
      parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    apply parabolicLpNormOn_mono_of_continuousOn hF hunit
      (isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d))
    · exact _root_.HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed
    · simpa only [inkSpotsSourceBox, inkSpotsUnitBox] using hshrink.2.1
  let p : ℝ := (d : ℝ) / ((d : ℝ) + 1)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hshrinkRpow : (inkSpotsShrunkSourceBox alpha q).radius ^ p ≤ 1 :=
    Real.rpow_le_one hshrinkR.le hshrinkRone hp0
  have hseedErrorBound := (scaledSourceError_le hC₀ hshrinkRpow ENNReal.toReal_nonneg hshrinkNorm).trans
    (mul_le_mul_of_nonneg_right (le_max_left C₀ CfpS) ENNReal.toReal_nonneg)
  have hcap := hseed.scaled hshrinkR (by norm_num : (0 : ℝ) < 1) U B F u hU
    hsourceClosed hB hu hF
    (by simpa only [inkSpotsSourceBox] using hnonneg.mono hshrink.2.1)
    (by simpa only [inkSpotsSourceBox] using hFnonneg.mono hshrink.2.1)
    (by simpa only [inkSpotsSourceBox] using hlower.mono hshrink.2.1)
    (by simpa only [inkSpotsSourceBox] using hupper.mono hshrink.2.1)
    (by simpa only [inkSpotsSourceBox] using hsuper.mono hshrink.2.1)
    (inkSpots_strict_density_nonneg hshrink)
  by_cases hlarge : (1 / 4 : ℝ) ≤ C₀ *
      (inkSpotsShrunkSourceBox alpha q).radius ^ p * parabolicLpNormOn d F
        (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
          (inkSpotsShrunkSourceBox alpha q).baseTime
          (inkSpotsShrunkSourceBox alpha q).center)
  · have hunitError : (1 / 4 : ℝ) ≤ max C₀ CfpS *
        parabolicLpNormOn d F (parabolicBox 1 1 0 0) :=
      hlarge.trans hseedErrorBound
    have huv := nonneg_at_terminal_half_cube hU hunit hu hnonneg v hv
    exact (min_le_left _ _).trans (by linarith)
  · have hsmall : C₀ * (inkSpotsShrunkSourceBox alpha q).radius ^ p *
        parabolicLpNormOn d F
          (parabolicBox 1 (inkSpotsShrunkSourceBox alpha q).radius
            (inkSpotsShrunkSourceBox alpha q).baseTime
            (inkSpotsShrunkSourceBox alpha q).center) < (1 / 4 : ℝ) :=
      lt_of_not_ge hlarge
    have hseedPointwise : ∀ x ∈ velocityClosedCube q.center
        ((inkSpotsShrunkSourceBox alpha q).radius / 2),
        (1 / 4 : ℝ) < u
          ((inkSpotsShrunkSourceBox alpha q).baseTime +
            (inkSpotsShrunkSourceBox alpha q).radius ^ 2, x) := by
      intro x hx
      have hcapPoint := hcap x hx
      dsimp [p] at hsmall
      linarith
    obtain ⟨htLower, htUpper, hwidth, hbase, htarget, hrect⟩ :=
      selected_inkSpots_forward_corridor d a eta c alpha R0 kappa q v w ha0 ha1
        heta0 heta1 hc (by rfl) hR0sq hR0pos (by rfl) hR hq.2.1 hv hcross
    let t0 : ℝ := q.baseTime + alpha ^ 2 * q.radius ^ 2
    let tau : ℝ := 1 - t0
    have hrect' : parabolicAffine t0 (0 : PDE.Vec d) 1 ''
        parabolicClosedRectangle tau (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ⊆
        parabolicClosedBox 1 1 0 0 := by
      rintro y ⟨x, hx, rfl⟩
      exact hrect (by simpa only [tau, t0] using hx)
    have hforward := forwardSourceInUnit hprop hCfpS.le hU hunit hB hu hF
      hnonneg hFnonneg hlower hupper hsuper (t0 := t0) (tau := tau) hR hRone
      htLower htUpper hwidth hbase htarget hrect'
      (eps := alpha / 2) (ell := (1 / 4 : ℝ)) (by positivity) (by linarith) (by norm_num)
      (fun x _ hx => by
        have hx' : x ∈ velocityClosedCube q.center ((inkSpotsShrunkSourceBox alpha q).radius / 2) :=
          fun i => by simpa [inkSpotsShrunkSourceBox, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using (hx i).le
        simpa [inkSpotsShrunkSourceBox, mul_pow, t0] using (hseedPointwise x hx').le)
    have hmain : deltaS * (alpha / 2) ^ mS * (1 / 4 : ℝ) <
        u (1, v) + CfpS * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      have ht : t0 + tau = 1 := by dsimp [tau]; ring
      simpa only [ht, zero_add] using hforward
    exact (min_le_right _ _).trans (hmain.le.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right (le_max_right C₀ CfpS) ENNReal.toReal_nonneg) _))

end HypoellipticAleksandrov.Parabolic
