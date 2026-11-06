module

public import HypoellipticAleksandrov.Parabolic.MovingLensSign
public import HypoellipticAleksandrov.Parabolic.LocalClassical

/-!
# Geometry for forward propagation

This module supplies the coordinate rectangles and concrete moving-lens
containments used by the principal-part classical forward-propagation lemma.
It contains no coefficient, operator, comparison, or propagation conclusion.

The analytic rectangle is open in time, while `parabolicTerminalRectangle`
includes its terminal time.  This distinction matches the terminal-inclusive
active moving lens used by the compact causal minimum principle.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Set

/- An open coordinate rectangle in velocity space. -/
def velocityRectangle {d } (lower upper : PDE.Vec d) : Set (PDE.Vec d) :=
  {v | ∀ i, lower i < v i ∧ v i < upper i}

/- The closed coordinate rectangle with the same faces. -/
def velocityClosedRectangle {d } (lower upper : PDE.Vec d) : Set (PDE.Vec d) :=
  {v | ∀ i, lower i ≤ v i ∧ v i ≤ upper i}

/- The source open time--velocity rectangle based at time zero. -/
def parabolicRectangle {d } (tau : ℝ) (lower upper : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Ioo 0 tau ×ˢ velocityRectangle lower upper

/- The compact closed counterpart of `parabolicRectangle`. -/
def parabolicClosedRectangle {d } (tau : ℝ) (lower upper : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Icc 0 tau ×ˢ velocityClosedRectangle lower upper

/- The positive-time rectangle including its terminal face. -/
@[simp] theorem mem_parabolicRectangle_iff {d tau t}
    {lower upper v : PDE.Vec d} :
    (t, v) ∈ parabolicRectangle tau lower upper ↔
      0 < t ∧ t < tau ∧ v ∈ velocityRectangle lower upper := by
  constructor
  · rintro ⟨⟨ht0, htau⟩, hv⟩
    exact ⟨ht0, htau, hv⟩
  · rintro ⟨ht0, htau, hv⟩
    exact ⟨⟨ht0, htau⟩, hv⟩

/- Membership in the compact closed time--velocity rectangle. -/
@[simp] theorem mem_parabolicClosedRectangle_iff {d tau t}
    {lower upper v : PDE.Vec d} :
    (t, v) ∈ parabolicClosedRectangle tau lower upper ↔
      0 ≤ t ∧ t ≤ tau ∧ v ∈ velocityClosedRectangle lower upper := by
  constructor
  · rintro ⟨⟨ht0, htau⟩, hv⟩
    exact ⟨ht0, htau, hv⟩
  · rintro ⟨ht0, htau, hv⟩
    exact ⟨⟨ht0, htau⟩, hv⟩

/- Membership in the terminal-inclusive time--velocity rectangle. -/
theorem velocityRectangle_eq_pi {d } (lower upper : PDE.Vec d) :
    velocityRectangle lower upper =
      Set.univ.pi fun i => Ioo (lower i) (upper i) := by
  ext v
  constructor
  · intro hv i _
    exact hv i
  · intro hv i
    exact hv i (Set.mem_univ i)

/- The coordinate presentation of a closed rectangle as a finite product. -/
theorem velocityClosedRectangle_eq_pi {d } (lower upper : PDE.Vec d) :
    velocityClosedRectangle lower upper =
      Set.univ.pi fun i => Icc (lower i) (upper i) := by
  ext v
  constructor
  · intro hv i _
    exact hv i
  · intro hv i
    exact hv i (Set.mem_univ i)

/- Open coordinate rectangles are open in the native product topology. -/
theorem closure_parabolicRectangle {d tau}
    {lower upper : PDE.Vec d} (htau : 0 < tau)
    (hfaces : ∀ i, lower i < upper i) :
    closure (parabolicRectangle tau lower upper) =
      parabolicClosedRectangle tau lower upper := by
  unfold parabolicRectangle parabolicClosedRectangle
  have _h_inl_18 : closure (velocityRectangle lower upper) = velocityClosedRectangle lower upper := by
    rw [velocityRectangle_eq_pi, closure_pi_set,
      velocityClosedRectangle_eq_pi]
    exact Set.pi_congr rfl fun i _ => closure_Ioo (ne_of_lt (hfaces i))
  rw [closure_prod_eq, closure_Ioo (ne_of_lt htau),
    _h_inl_18]

/- Continuity extends nonnegativity from an open parabolic rectangle to its
closed counterpart. -/
theorem IsNonnegativeOn.parabolicClosedRectangle
    {d tau lower upper}
    {u : TimeVelocity d → ℝ} (htau : 0 < tau)
    (hfaces : ∀ i, lower i < upper i)
    (hcont : ContinuousOn u
      (HypoellipticAleksandrov.Parabolic.parabolicClosedRectangle tau lower upper))
    (hnonneg : HypoellipticAleksandrov.Parabolic.IsNonnegativeOn u
      (HypoellipticAleksandrov.Parabolic.parabolicRectangle tau lower upper)) :
    HypoellipticAleksandrov.Parabolic.IsNonnegativeOn u
      (HypoellipticAleksandrov.Parabolic.parabolicClosedRectangle tau lower upper) := by
  let Q := HypoellipticAleksandrov.Parabolic.parabolicRectangle tau lower upper
  have hclosure :=
    closure_parabolicRectangle htau hfaces
  have hcontClosure : ContinuousOn u (closure Q) := by
    rw [hclosure]
    exact hcont
  have hmaps : MapsTo u Q (Ici (0 : ℝ)) := by
    intro z hz
    exact hnonneg z hz
  have hmapsClosure :=
    hmaps.closure_of_continuousOn hcontClosure
  intro z hz
  have hzClosure : z ∈ closure Q := by
    rwa [hclosure]
  have huz := hmapsClosure hzClosure
  simpa only [isClosed_Ici.closure_eq, mem_Ici] using huz

/- Inverting the target time preserves the normalized coordinate-square
bound, including in dimension zero. -/
theorem euclideanBall_subset_velocityCube_inter_velocityRectangle
    {d } {center lower upper : PDE.Vec d} {rho eps margin : ℝ}
    (hrho : 0 < rho) (hrhoEps : rho ≤ eps) (hrhoMargin : rho < margin)
    (hcenter : ∀ i, lower i + margin ≤ center i ∧
      center i ≤ upper i - margin) :
    PDE.euclideanBall center rho ⊆
      velocityCube center eps ∩ velocityRectangle lower upper := by
  intro v hv
  have hvCube :=
    euclideanBall_subset_velocityCube hrho hv
  constructor
  · intro i
    exact (hvCube i).trans_le hrhoEps
  · intro i
    rcases abs_lt.mp (hvCube i) with ⟨hleft, hright⟩
    rcases hcenter i with ⟨hcenterLower, hcenterUpper⟩
    constructor <;> nlinarith

/- The fixed moving-lens denominator stays strictly below `kappa²` under
the normalized time and small-seed bounds. -/
theorem movingLensDenominator_lt_kappa_sq
    {kappa rho tau t : ℝ} (hkappa : 0 < kappa)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2) (ht : t ≤ tau)
    (htauUpper : tau ≤ kappa⁻¹) :
    movingLensDenominator (movingLensSignXi kappa) rho t < kappa ^ 2 := by
  have hxi : 0 ≤ movingLensSignXi kappa := by
    unfold movingLensSignXi
    positivity
  have hslope : movingLensSignXi kappa * t ≤ kappa ^ 2 / 2 := by
    calc
      movingLensSignXi kappa * t ≤
          movingLensSignXi kappa * kappa⁻¹ :=
        mul_le_mul_of_nonneg_left (ht.trans htauUpper) hxi
      _ = kappa ^ 2 / 2 := by
        unfold movingLensSignXi
        field_simp [hkappa.ne']
  unfold movingLensDenominator
  nlinarith

/- Every velocity section of a normalized closed moving lens lies strictly
inside the source coordinate rectangle. -/
theorem movingLensClosed_velocity_mem_velocityRectangle
    {d kappa rho tau tStar lower upper vStar}
    (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2)
    (htStar : 0 < tStar) (htStarTau : tStar ≤ tau)
    (htauUpper : tau ≤ kappa⁻¹)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 ≤ upper i - kappa)
    (htarget : ∀ i, lower i + kappa ≤ vStar i ∧
      vStar i ≤ upper i - kappa)
    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) rho tStar
      (tStar⁻¹ • vStar)) :
    z.2 ∈ velocityRectangle lower upper := by
  rcases hz with ⟨hz0, hzStar, hzSpatial⟩
  have hden : movingLensDenominator (movingLensSignXi kappa) rho z.1 <
      kappa ^ 2 :=
    movingLensDenominator_lt_kappa_sq hkappa hsmall
      (hzStar.trans htStarTau) htauUpper
  have hdenPos : 0 < movingLensDenominator
      (movingLensSignXi kappa) rho z.1 :=
    movingLensDenominator_pos (by
      unfold movingLensSignXi
      positivity) hrho hz0
  have hdenBounds : movingLensDenominator
      (movingLensSignXi kappa) rho z.1 ∈ Ioo 0 (kappa ^ 2) :=
    ⟨hdenPos, hden⟩
  let s : ℝ := z.1 * tStar⁻¹
  have htInvNonneg : 0 ≤ tStar⁻¹ := (inv_pos.mpr htStar).le
  have hs0 := mul_nonneg hz0 htInvNonneg
  have hs1 : s ≤ 1 := by
    dsimp only [s]
    calc
      z.1 * tStar⁻¹ ≤ tStar * tStar⁻¹ :=
        mul_le_mul_of_nonneg_right hzStar htInvNonneg
      _ = 1 := mul_inv_cancel₀ htStar.ne'
  intro i
  have hcenterLower : lower i + kappa ≤ s * vStar i := by
    have hleft : (1 - s) * (lower i + kappa) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs1) (hbase i).1
    have hright :=
      mul_le_mul_of_nonneg_left (htarget i).1 hs0
    nlinarith
  have hcenterUpper : s * vStar i ≤ upper i - kappa := by
    have hleft : 0 ≤ (1 - s) * (upper i - kappa) :=
      mul_nonneg (sub_nonneg.mpr hs1) (hbase i).2
    have hright :=
      mul_le_mul_of_nonneg_left (htarget i).2 hs0
    nlinarith
  have hcoordSq :
      movingLensDisplacement (tStar⁻¹ • vStar) z i ^ 2 < kappa ^ 2 :=
    calc
      movingLensDisplacement (tStar⁻¹ • vStar) z i ^ 2 ≤
          PDE.vecNormSq (movingLensDisplacement (tStar⁻¹ • vStar) z) :=
        PDE.sq_apply_le_vecNormSq _ i
      _ ≤ movingLensDenominator (movingLensSignXi kappa) rho z.1 := hzSpatial
      _ < kappa ^ 2 := hdenBounds.2
  have hcoordAbs :=
    abs_lt_of_sq_lt_sq hcoordSq hkappa.le
  have hdispEq : movingLensDisplacement (tStar⁻¹ • vStar) z i =
      z.2 i - s * vStar i := by
    unfold movingLensDisplacement
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s]
    ring
  rw [hdispEq, abs_lt] at hcoordAbs
  constructor <;> nlinarith

/- The normalized closed moving lens lies in the concrete closed source
rectangle. -/
theorem movingLensClosed_subset_parabolicClosedRectangle
    {d kappa rho tau tStar}
    {lower upper vStar : PDE.Vec d}
    (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2)
    (htStar : 0 < tStar) (htStarTau : tStar ≤ tau)
    (htauUpper : tau ≤ kappa⁻¹)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 ≤ upper i - kappa)
    (htarget : ∀ i, lower i + kappa ≤ vStar i ∧
      vStar i ≤ upper i - kappa) :
    movingLensClosed (movingLensSignXi kappa) rho tStar
        (tStar⁻¹ • vStar) ⊆
      parabolicClosedRectangle tau lower upper := by
  intro z hz
  have hvOpen :=
    movingLensClosed_velocity_mem_velocityRectangle hkappa hrho hsmall
      htStar htStarTau htauUpper hbase htarget hz
  rcases hz with ⟨hz0, hzStar, _⟩
  rw [mem_parabolicClosedRectangle_iff]
  exact ⟨hz0, hzStar.trans htStarTau,
    fun i => ⟨(hvOpen i).1.le, (hvOpen i).2.le⟩⟩

/- When its terminal time is below the ambient top face, the normalized
active moving lens lies in the open source rectangle. -/
theorem movingLensActive_subset_parabolicRectangle
    {d kappa rho tau tStar}
    {lower upper vStar : PDE.Vec d}
    (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2)
    (htStar : 0 < tStar) (htStarTau : tStar < tau)
    (htauUpper : tau ≤ kappa⁻¹)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 ≤ upper i - kappa)
    (htarget : ∀ i, lower i + kappa ≤ vStar i ∧
      vStar i ≤ upper i - kappa) :
    movingLensActive (movingLensSignXi kappa) rho tStar
        (tStar⁻¹ • vStar) ⊆
      parabolicRectangle tau lower upper := by
  intro z hz
  have hzClosed : z ∈ movingLensClosed (movingLensSignXi kappa) rho tStar
      (tStar⁻¹ • vStar) :=
    movingLensActive_subset_movingLensClosed _ _ _ _ hz
  have hvOpen :=
    movingLensClosed_velocity_mem_velocityRectangle hkappa hrho hsmall
      htStar htStarTau.le htauUpper hbase htarget hzClosed
  rw [mem_parabolicRectangle_iff]
  exact ⟨hz.1, hz.2.1.trans_lt htStarTau, hvOpen⟩

/- The lower faces of a velocity rectangle in positive-scale pullback
coordinates. -/
def pullbackRectangleLower {d } (v0 lower : PDE.Vec d) (R : ℝ) : PDE.Vec d :=
  R⁻¹ • (lower - v0)

/- The upper faces of a velocity rectangle in positive-scale pullback
coordinates. -/
def pullbackRectangleUpper {d } (v0 upper : PDE.Vec d) (R : ℝ) : PDE.Vec d :=
  R⁻¹ • (upper - v0)

/- Positive affine velocity scaling pulls an open rectangle back to its
normalized coordinate rectangle. -/
theorem mem_affineVelocity_velocityClosedRectangle_iff
    {d R} {v0 lower upper v : PDE.Vec d} (hR : 0 < R) :
    v0 + R • v ∈ velocityClosedRectangle lower upper ↔
      v ∈ velocityClosedRectangle (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
  constructor
  · intro hv i
    have hlPhysical : lower i - v0 i ≤ R * v i := by
      have := (hv i).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    have huPhysical : R * v i ≤ upper i - v0 i := by
      have := (hv i).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    constructor
    · change R⁻¹ * (lower i - v0 i) ≤ v i
      exact (inv_mul_le_iff₀ hR).2 hlPhysical
    · change v i ≤ R⁻¹ * (upper i - v0 i)
      exact (le_inv_mul_iff₀ hR).2 huPhysical
  · intro hv i
    have hlNormalized : R⁻¹ * (lower i - v0 i) ≤ v i := by
      simpa only [pullbackRectangleLower, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul] using (hv i).1
    have huNormalized : v i ≤ R⁻¹ * (upper i - v0 i) := by
      simpa only [pullbackRectangleUpper, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul] using (hv i).2
    have hlPhysical :=
      (inv_mul_le_iff₀ hR).1 hlNormalized
    have huPhysical :=
      (le_inv_mul_iff₀ hR).1 huNormalized
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith

/- Membership in the positive-scale affine preimage of an open parabolic
rectangle. -/
theorem mem_parabolicAffine_preimage_parabolicRectangle_iff
    {d R tau v0 lower upper}
    {z : TimeVelocity d} (hR : 0 < R) :
    parabolicAffine 0 v0 R z ∈ parabolicRectangle tau lower upper ↔
      z ∈ parabolicRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
  rcases z with ⟨t, v⟩
  have hRsq := sq_pos_of_pos hR
  rw [mem_parabolicRectangle_iff, mem_parabolicRectangle_iff]
  simp only [parabolicAffine, zero_add]
  have _h_inl_30 : v0 + R • v ∈ velocityRectangle lower upper ↔
      v ∈ velocityRectangle (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
      constructor
      · intro hv i
        have hlPhysical : lower i - v0 i < R * v i := by
          have := (hv i).1
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
          linarith
        have huPhysical : R * v i < upper i - v0 i := by
          have := (hv i).2
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
          linarith
        constructor
        · change R⁻¹ * (lower i - v0 i) < v i
          exact (inv_mul_lt_iff₀ hR).2 hlPhysical
        · change v i < R⁻¹ * (upper i - v0 i)
          exact (lt_inv_mul_iff₀ hR).2 huPhysical
      · intro hv i
        have hlNormalized : R⁻¹ * (lower i - v0 i) < v i := by
          simpa only [pullbackRectangleLower, Pi.smul_apply, Pi.sub_apply,
            smul_eq_mul] using (hv i).1
        have huNormalized : v i < R⁻¹ * (upper i - v0 i) := by
          simpa only [pullbackRectangleUpper, Pi.smul_apply, Pi.sub_apply,
            smul_eq_mul] using (hv i).2
        have hlPhysical :=
          (inv_mul_lt_iff₀ hR).1 hlNormalized
        have huPhysical :=
          (lt_inv_mul_iff₀ hR).1 huNormalized
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        constructor <;> linarith

    /- Positive affine velocity scaling pulls a closed rectangle back to its
    normalized coordinate rectangle. -/
  rw [_h_inl_30]
  constructor
  · rintro ⟨ht0, htau, hv⟩
    refine ⟨?_, ?_, hv⟩
    · nlinarith
    · rw [lt_div_iff₀ hRsq]
      simpa only [mul_comm] using htau
  · rintro ⟨ht0, htau, hv⟩
    refine ⟨?_, ?_, hv⟩
    · nlinarith
    · have := (lt_div_iff₀ hRsq).1 htau
      simpa only [mul_comm] using this

/- Membership in the positive-scale affine preimage of a closed parabolic
rectangle. -/
theorem mapsTo_parabolicAffine_parabolicRectangle
    {d R tau} {v0 lower upper : PDE.Vec d} (hR : 0 < R) :
    MapsTo (parabolicAffine 0 v0 R)
      (parabolicRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R))
      (parabolicRectangle tau lower upper) := by
  intro z hz
  exact (mem_parabolicAffine_preimage_parabolicRectangle_iff hR).2 hz

/- Positive parabolic scaling maps the normalized closed rectangle into its
physical counterpart. -/
theorem mapsTo_parabolicAffine_parabolicClosedRectangle
    {d R tau} {v0 lower upper : PDE.Vec d} (hR : 0 < R) :
    MapsTo (parabolicAffine 0 v0 R)
      (parabolicClosedRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R))
      (parabolicClosedRectangle tau lower upper) := by
  intro z hz
  have _h_inl_30 : parabolicAffine 0 v0 R z ∈ parabolicClosedRectangle tau lower upper ↔
      z ∈ parabolicClosedRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
    rcases z with ⟨t, v⟩
    have hRsq := sq_pos_of_pos hR
    rw [mem_parabolicClosedRectangle_iff, mem_parabolicClosedRectangle_iff]
    simp only [parabolicAffine, zero_add]
    rw [mem_affineVelocity_velocityClosedRectangle_iff hR]
    constructor
    · rintro ⟨ht0, htau, hv⟩
      refine ⟨?_, ?_, hv⟩
      · nlinarith
      · rw [le_div_iff₀ hRsq]
        simpa only [mul_comm] using htau
    · rintro ⟨ht0, htau, hv⟩
      refine ⟨?_, ?_, hv⟩
      · nlinarith
      · have := (le_div_iff₀ hRsq).1 htau
        simpa only [mul_comm] using this
  exact _h_inl_30.2 hz

theorem mem_affineVelocity_velocityCube_iff {d R eps v0 v} (hR : 0 < R) :
    v0 + R • v ∈ velocityCube v0 (eps * R) ↔
      v ∈ velocityCube (0 : PDE.Vec d) eps := by
  constructor <;> intro hv <;> intro i
  · have hi := hv i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hi ⊢
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hR, mul_comm eps R] at hi
    simpa only [sub_zero] using lt_of_mul_lt_mul_left hi hR.le
  · have hi := hv i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hi ⊢
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hR, mul_comm eps R]
    simpa only [sub_zero] using mul_lt_mul_of_pos_left hi hR

end

end HypoellipticAleksandrov.Parabolic
