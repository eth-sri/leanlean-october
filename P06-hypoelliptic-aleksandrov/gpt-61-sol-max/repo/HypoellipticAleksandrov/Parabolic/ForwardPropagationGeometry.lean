module

public import HypoellipticAleksandrov.Parabolic.MovingLensSign
public import HypoellipticAleksandrov.Parabolic.LocalClassical
import Aesop



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

variable {d : ℕ}

variable (lower upper : PDE.Vec d)

/-- An open coordinate rectangle in velocity space. -/
def velocityRectangle   : PDE.VelocityRegion d :=
  {v | ∀ i, lower i < v i ∧ v i < upper i}

/-- The closed coordinate rectangle with the same faces. -/
def velocityClosedRectangle   : PDE.VelocityRegion d :=
  {v | ∀ i, lower i ≤ v i ∧ v i ≤ upper i}

variable (tau : ℝ) (lower upper : PDE.Vec d)

/-- The source open time--velocity rectangle based at time zero. -/
def parabolicRectangle   :
    HypoellipticAleksandrov.Parabolic.Region d :=
  Ioo 0 tau ×ˢ velocityRectangle lower upper

/-- The compact closed counterpart of `parabolicRectangle`. -/
def parabolicClosedRectangle   :
    HypoellipticAleksandrov.Parabolic.Region d :=
  Icc 0 tau ×ˢ velocityClosedRectangle lower upper



variable {lower upper v : PDE.Vec d}

/-- Membership in an open velocity rectangle. -/
@[simp] theorem mem_velocityRectangle_iff   :
    v ∈ velocityRectangle lower upper ↔
      ∀ i, lower i < v i ∧ v i < upper i :=
  Iff.rfl



variable {tau t : ℝ} {lower upper v : PDE.Vec d}

/-- Membership in the source open time--velocity rectangle. -/
@[simp] theorem mem_parabolicRectangle_iff   :
    (t, v) ∈ parabolicRectangle tau lower upper ↔
      0 < t ∧ t < tau ∧ v ∈ velocityRectangle lower upper := by
  constructor
  · rintro ⟨⟨ht0, htau⟩, hv⟩
    exact ⟨ht0, htau, hv⟩
  · rintro ⟨ht0, htau, hv⟩
    exact ⟨⟨ht0, htau⟩, hv⟩

/-- Membership in the compact closed time--velocity rectangle. -/
@[simp] theorem mem_parabolicClosedRectangle_iff   :
    (t, v) ∈ parabolicClosedRectangle tau lower upper ↔
      0 ≤ t ∧ t ≤ tau ∧ v ∈ velocityClosedRectangle lower upper := by
  constructor
  · rintro ⟨⟨ht0, htau⟩, hv⟩
    exact ⟨ht0, htau, hv⟩
  · rintro ⟨ht0, htau, hv⟩
    exact ⟨⟨ht0, htau⟩, hv⟩



variable (lower upper : PDE.Vec d)

/-- The coordinate presentation of an open rectangle as a finite product. -/
theorem velocityRectangle_eq_pi   :
    velocityRectangle lower upper =
      Set.univ.pi fun i => Ioo (lower i) (upper i) := by
  aesop

/-- The coordinate presentation of a closed rectangle as a finite product. -/
theorem velocityClosedRectangle_eq_pi   :
    velocityClosedRectangle lower upper =
      Set.univ.pi fun i => Icc (lower i) (upper i) := by
  ext v
  constructor
  · intro hv i _
    exact hv i
  · intro hv i
    exact hv i (Set.mem_univ i)

/-- Open coordinate rectangles are open in the native product topology. -/
theorem isOpen_velocityRectangle   :
    IsOpen (velocityRectangle lower upper) := by
  rw [velocityRectangle_eq_pi]
  have hpi : Set.univ.pi (fun i  => Ioo (lower i) (upper i)) =
      ⋂ i ∈ (Finset.univ : Finset (Fin d)),
        (fun v : PDE.Vec d => v i) ⁻¹' Ioo (lower i) (upper i) := by
    ext v
    simp
  rw [hpi]
  exact isOpen_biInter_finset fun i _ =>
    isOpen_Ioo.preimage (continuous_apply i)

/-- Closed coordinate rectangles are compact. -/
theorem isCompact_velocityClosedRectangle
     :
    IsCompact (velocityClosedRectangle lower upper) := by
  rw [velocityClosedRectangle_eq_pi]
  exact isCompact_univ_pi fun i => isCompact_Icc

variable (tau : ℝ) (lower upper : PDE.Vec d)

/-- Open parabolic rectangles are open. -/
theorem isOpen_parabolicRectangle   :
    IsOpen (parabolicRectangle tau lower upper) :=
  isOpen_Ioo.prod (isOpen_velocityRectangle lower upper)

/-- Closed parabolic rectangles are compact. -/
theorem isCompact_parabolicClosedRectangle   :
    IsCompact (parabolicClosedRectangle tau lower upper) :=
  isCompact_Icc.prod (isCompact_velocityClosedRectangle lower upper)

/-- A nonempty closed velocity rectangle is the closure of its open counterpart. -/
theorem closure_velocityRectangle  {lower upper : PDE.Vec d}
    (hfaces : ∀ i, lower i < upper i) :
    closure (velocityRectangle lower upper) =
      velocityClosedRectangle lower upper := by
  rw [velocityRectangle_eq_pi, closure_pi_set,
    velocityClosedRectangle_eq_pi]
  exact Set.pi_congr rfl fun i _ => closure_Ioo (ne_of_lt (hfaces i))

variable {tau : ℝ} {lower upper : PDE.Vec d}

/-- A nonempty closed parabolic rectangle is exactly the closure of its open
counterpart. -/
theorem closure_parabolicRectangle   (htau : 0 < tau)
    (hfaces : ∀ i, lower i < upper i) :
    closure (parabolicRectangle tau lower upper) =
      parabolicClosedRectangle tau lower upper := by
  unfold parabolicRectangle parabolicClosedRectangle
  rw [closure_prod_eq, closure_Ioo (ne_of_lt htau),
    closure_velocityRectangle hfaces]

/-- Continuity extends nonnegativity from an open parabolic rectangle to its
closed counterpart. -/
theorem IsNonnegativeOn.parabolicClosedRectangle

    {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (htau : 0 < tau)
    (hfaces : ∀ i, lower i < upper i)
    (hcont : ContinuousOn u
      (HypoellipticAleksandrov.Parabolic.parabolicClosedRectangle tau lower upper))
    (hnonneg : HypoellipticAleksandrov.Parabolic.IsNonnegativeOn u
      (HypoellipticAleksandrov.Parabolic.parabolicRectangle tau lower upper)) :
    HypoellipticAleksandrov.Parabolic.IsNonnegativeOn u
      (HypoellipticAleksandrov.Parabolic.parabolicClosedRectangle tau lower upper) := by

  have hclosure  :=
    closure_parabolicRectangle htau hfaces


  have hmapsClosure  :=
    (show MapsTo u (HypoellipticAleksandrov.Parabolic.parabolicRectangle tau lower upper) (Ici (0 )) by
        intro z hz
        exact hnonneg z hz).closure_of_continuousOn (by
        rw [hclosure]
        exact hcont)
  intro z hz

  have huz := hmapsClosure (by
      rwa [hclosure])
  simpa only [isClosed_Ici.closure_eq, mem_Ici] using huz

/-- Inverting the target time preserves the normalized coordinate-square
bound, including in dimension zero. -/
theorem vecNormSq_inv_smul_le_of_mem_rectangle
     {kappa tStar : ℝ} {lower upper vStar : PDE.Vec d}
    (hkappa : 0 < kappa) (htStar : kappa ≤ tStar)
    (hwidth : ∀ i, upper i - lower i ≤ kappa⁻¹)
    (hzero : (0 : PDE.Vec d) ∈ velocityClosedRectangle lower upper)
    (hvStar : vStar ∈ velocityClosedRectangle lower upper) :
    PDE.vecNormSq (tStar⁻¹ • vStar) ≤
      (d : ℝ) * kappa ^ (-4 : ℤ) := by
  have htStarPos  := hkappa.trans_le htStar

  have hkappaInv  := (inv_pos.mpr hkappa).le
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, (tStar⁻¹ • vStar) i ^ 2 ≤
        ∑ _i : Fin d, kappa ^ (-4 : ℤ) := by
      let sharedTerm_479ae908f5 := ((kappa⁻¹ * kappa⁻¹) ^ 2)
      apply Finset.sum_le_sum
      intro i _
      have hvLower := (hvStar i).1
      have hvUpper := (hvStar i).2
      have hzeroLower := (hzero i).1
      have hzeroUpper := (hzero i).2
      simp only [Pi.zero_apply] at hzeroLower hzeroUpper



      calc
        (tStar⁻¹ • vStar) i ^ 2 = |(tStar⁻¹ • vStar) i| ^ 2 := by
          rw [sq_abs]
        _ ≤ sharedTerm_479ae908f5 := ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg hkappaInv hkappaInv)).2 (by
            simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
              abs_of_pos (inv_pos.mpr htStarPos)]
            calc
              tStar⁻¹ * |vStar i| ≤ kappa⁻¹ * |vStar i| :=
                mul_le_mul_of_nonneg_right ((inv_le_inv₀ htStarPos hkappa).2 htStar) (abs_nonneg _)
              _ ≤ kappa⁻¹ * kappa⁻¹ :=
                mul_le_mul_of_nonneg_left (by
                    rw [abs_le]
                    constructor <;> nlinarith [hwidth i]) hkappaInv))
        _ = kappa ^ (-4 : ℤ) := by
          rw [show sharedTerm_479ae908f5 = kappa⁻¹ ^ 4 by ring]
          norm_num [zpow_neg, inv_pow]
    _ = (d : ℝ) * kappa ^ (-4 : ℤ) := by
      simp [nsmul_eq_mul]

/-- A Euclidean seed ball lies in both the source coordinate cube and a
rectangle whose centre has the stated face margin. -/
theorem euclideanBall_subset_velocityCube_inter_velocityRectangle
     {center lower upper : PDE.Vec d} {rho eps margin : ℝ}
    (hrho : 0 < rho) (hrhoEps : rho ≤ eps) (hrhoMargin : rho < margin)
    (hcenter : ∀ i, lower i + margin ≤ center i ∧
      center i ≤ upper i - margin) :
    PDE.euclideanBall center rho ⊆
      velocityCube center eps ∩ velocityRectangle lower upper := by
  intro v hv
  have hvCube  :=
    euclideanBall_subset_velocityCube hrho hv
  constructor
  · intro i
    exact (hvCube i).trans_le hrhoEps
  · intro i
    rcases abs_lt.mp (hvCube i) with ⟨hleft, hright⟩
    rcases hcenter i with ⟨hcenterLower, hcenterUpper⟩
    constructor <;> nlinarith

/-- The fixed moving-lens denominator stays strictly below `kappa²` under
the normalized time and small-seed bounds. -/
theorem movingLensDenominator_lt_kappa_sq
    {kappa rho tau t : ℝ} (hkappa : 0 < kappa)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2) (ht : t ≤ tau)
    (htauUpper : tau ≤ kappa⁻¹) :
    movingLensDenominator (movingLensSignXi kappa) rho t < kappa ^ 2 := by

  have hslope : movingLensSignXi kappa * t ≤ kappa ^ 2 / 2 := by
    calc
      movingLensSignXi kappa * t ≤
          movingLensSignXi kappa * kappa⁻¹ :=
        mul_le_mul_of_nonneg_left (ht.trans htauUpper) (by
            unfold movingLensSignXi
            positivity)
      _ = kappa ^ 2 / 2 := by
        unfold movingLensSignXi
        field_simp [hkappa.ne']
  unfold movingLensDenominator
  nlinarith

variable {d : ℕ}

variable {kappa rho tau tStar : ℝ} {lower upper vStar : PDE.Vec d} (hkappa : 0 < kappa) (hrho : 0 < rho) (hsmall : 2 * rho ^ 2 < kappa ^ 2) (htStar : 0 < tStar)

section
variable (htStarTau : tStar ≤ tau) (htauUpper : tau ≤ kappa⁻¹) (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 ≤ upper i - kappa) (htarget : ∀ i, lower i + kappa ≤ vStar i ∧ vStar i ≤ upper i - kappa)

include hkappa hrho hsmall htStar htStarTau htauUpper hbase htarget
/-- Every velocity section of a normalized closed moving lens lies strictly
inside the source coordinate rectangle. -/
theorem movingLensClosed_velocity_mem_velocityRectangle

    {z : TimeVelocity d}
    (hz : z ∈ movingLensClosed (movingLensSignXi kappa) rho tStar
      (tStar⁻¹ • vStar)) :
    z.2 ∈ velocityRectangle lower upper := by
  let sharedTerm_1dbe63f96e := (movingLensDenominator (movingLensSignXi kappa) rho z.1)
  rcases hz with ⟨hz0, hzStar, hzSpatial⟩
  have hden  :=
    movingLensDenominator_lt_kappa_sq hkappa hsmall
      (hzStar.trans htStarTau) htauUpper
  have hdenPos : 0 < sharedTerm_1dbe63f96e :=
    movingLensDenominator_pos (by
      unfold movingLensSignXi
      positivity) hrho hz0
  have hdenBounds : sharedTerm_1dbe63f96e ∈ Ioo 0 (kappa ^ 2) :=
    ⟨hdenPos, hden⟩
  let s : ℝ := z.1 * tStar⁻¹
  have htInvNonneg  := (inv_pos.mpr htStar).le
  have hs0  := mul_nonneg hz0 htInvNonneg
  have hs1 : s ≤ 1 := by
    dsimp only [s]
    calc
      z.1 * tStar⁻¹ ≤ tStar * tStar⁻¹ :=
        mul_le_mul_of_nonneg_right hzStar htInvNonneg
      _ = 1 := mul_inv_cancel₀ htStar.ne'
  intro i
  have hcenterLower : lower i + kappa ≤ s * vStar i := by
    have hleft  :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs1) (hbase i).1
    have hright  :=
      mul_le_mul_of_nonneg_left (htarget i).1 hs0
    nlinarith
  have hcenterUpper : s * vStar i ≤ upper i - kappa := by
    have hleft  :=
      mul_nonneg (sub_nonneg.mpr hs1) (hbase i).2
    have hright  :=
      mul_le_mul_of_nonneg_left (htarget i).2 hs0
    nlinarith
  have hcoordSq  :=
    calc
      movingLensDisplacement (tStar⁻¹ • vStar) z i ^ 2 ≤
          PDE.vecNormSq (movingLensDisplacement (tStar⁻¹ • vStar) z) :=
        PDE.sq_apply_le_vecNormSq _ i
      _ ≤ sharedTerm_1dbe63f96e := hzSpatial
      _ < kappa ^ 2 := hdenBounds.2
  have hcoordAbs  :=
    abs_lt_of_sq_lt_sq hcoordSq hkappa.le
  have hdispEq : movingLensDisplacement (tStar⁻¹ • vStar) z i =
      z.2 i - s * vStar i := by
    unfold movingLensDisplacement
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s]
    ring
  rw [hdispEq, abs_lt] at hcoordAbs
  constructor <;> nlinarith

/-- The normalized closed moving lens lies in the concrete closed source
rectangle. -/
theorem movingLensClosed_subset_parabolicClosedRectangle
       :
    movingLensClosed (movingLensSignXi kappa) rho tStar
        (tStar⁻¹ • vStar) ⊆
      parabolicClosedRectangle tau lower upper := by
  intro z hz
  have hvOpen  :=
    movingLensClosed_velocity_mem_velocityRectangle hkappa hrho hsmall
      htStar htStarTau htauUpper hbase htarget hz
  rcases hz with ⟨hz0, hzStar, _⟩
  rw [mem_parabolicClosedRectangle_iff]
  exact ⟨hz0, hzStar.trans htStarTau,
    fun i => ⟨(hvOpen i).1.le, (hvOpen i).2.le⟩⟩
end


include hkappa hrho hsmall htStar in
/-- When its terminal time is below the ambient top face, the normalized
active moving lens lies in the open source rectangle. -/
theorem movingLensActive_subset_parabolicRectangle
      (htStarTau : tStar < tau)
    (htauUpper : tau ≤ kappa⁻¹)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 ≤ upper i - kappa)
    (htarget : ∀ i, lower i + kappa ≤ vStar i ∧
      vStar i ≤ upper i - kappa) :
    movingLensActive (movingLensSignXi kappa) rho tStar
        (tStar⁻¹ • vStar) ⊆
      parabolicRectangle tau lower upper := by
  intro z hz

  have hvOpen  :=
    movingLensClosed_velocity_mem_velocityRectangle hkappa hrho hsmall
      htStar htStarTau.le htauUpper hbase htarget (movingLensActive_subset_movingLensClosed _ _ _ _ hz)
  rw [mem_parabolicRectangle_iff]
  exact ⟨hz.1, hz.2.1.trans_lt htStarTau, hvOpen⟩

/-- The lower faces of a velocity rectangle in positive-scale pullback
coordinates. -/
def pullbackRectangleLower  (v0 lower : PDE.Vec d) (R : ℝ) : PDE.Vec d :=
  R⁻¹ • (lower - v0)

/-- The upper faces of a velocity rectangle in positive-scale pullback
coordinates. -/
def pullbackRectangleUpper  (v0 upper : PDE.Vec d) (R : ℝ) : PDE.Vec d :=
  R⁻¹ • (upper - v0)

section
variable {R : ℝ} {v0 lower upper v : PDE.Vec d} (hR : 0 < R)

include hR
/-- Positive affine velocity scaling pulls an open rectangle back to its
normalized coordinate rectangle. -/
theorem mem_affineVelocity_velocityRectangle_iff
      :
    v0 + R • v ∈ velocityRectangle lower upper ↔
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


    have hlPhysical  :=
      (inv_mul_lt_iff₀ hR).1 (show R⁻¹ * (lower i - v0 i) < v i by
          exact (hv i).1)
    have huPhysical  :=
      (lt_inv_mul_iff₀ hR).1 (show v i < R⁻¹ * (upper i - v0 i) by
          exact (hv i).2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith

/-- Positive affine velocity scaling pulls a closed rectangle back to its
normalized coordinate rectangle. -/
theorem mem_affineVelocity_velocityClosedRectangle_iff
      :
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


    have hlPhysical  :=
      (inv_mul_le_iff₀ hR).1 (show R⁻¹ * (lower i - v0 i) ≤ v i by
          exact (hv i).1)
    have huPhysical  :=
      (le_inv_mul_iff₀ hR).1 (show v i ≤ R⁻¹ * (upper i - v0 i) by
          exact (hv i).2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> linarith
end


variable {R tau : ℝ} {v0 lower upper : PDE.Vec d}

section
variable {z : TimeVelocity d} (hR : 0 < R)

include hR
/-- Membership in the positive-scale affine preimage of an open parabolic
rectangle. -/
theorem mem_parabolicAffine_preimage_parabolicRectangle_iff

     :
    parabolicAffine 0 v0 R z ∈ parabolicRectangle tau lower upper ↔
      z ∈ parabolicRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
  rcases z with ⟨t, v⟩
  have hRsq  := sq_pos_of_pos hR
  rw [mem_parabolicRectangle_iff, mem_parabolicRectangle_iff]
  simp only [parabolicAffine, zero_add]
  rw [mem_affineVelocity_velocityRectangle_iff hR]
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

/-- Membership in the positive-scale affine preimage of a closed parabolic
rectangle. -/
theorem mem_parabolicAffine_preimage_parabolicClosedRectangle_iff

     :
    parabolicAffine 0 v0 R z ∈ parabolicClosedRectangle tau lower upper ↔
      z ∈ parabolicClosedRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
  rcases z with ⟨t, v⟩
  have hRsq  := sq_pos_of_pos hR
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
end


section
variable (hR : 0 < R)

include hR
/-- The exact positive-scale preimage of an open parabolic rectangle. -/
theorem parabolicAffine_preimage_parabolicRectangle
       :
    parabolicAffine 0 v0 R ⁻¹' parabolicRectangle tau lower upper =
      parabolicRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R) := by
  ext z
  exact mem_parabolicAffine_preimage_parabolicRectangle_iff hR

/-- Positive parabolic scaling maps the normalized open rectangle into its
physical counterpart. -/
theorem mapsTo_parabolicAffine_parabolicRectangle
       :
    MapsTo (parabolicAffine 0 v0 R)
      (parabolicRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R))
      (parabolicRectangle tau lower upper) := by
  intro z hz
  exact (mem_parabolicAffine_preimage_parabolicRectangle_iff hR).2 hz

/-- Positive parabolic scaling maps the normalized closed rectangle into its
physical counterpart. -/
theorem mapsTo_parabolicAffine_parabolicClosedRectangle
       :
    MapsTo (parabolicAffine 0 v0 R)
      (parabolicClosedRectangle (tau / R ^ 2)
        (pullbackRectangleLower v0 lower R)
        (pullbackRectangleUpper v0 upper R))
      (parabolicClosedRectangle tau lower upper) := by
  intro z hz
  exact (mem_parabolicAffine_preimage_parabolicClosedRectangle_iff hR).2 hz
end


private theorem parabolicAffine_zero_surjective
     {R : ℝ} {v0 : PDE.Vec d} (hR : 0 < R) :
    Function.Surjective (parabolicAffine 0 v0 R) := by
  intro z
  refine ⟨(z.1 / R ^ 2, R⁻¹ • (z.2 - v0)), ?_⟩
  ext
  · dsimp [parabolicAffine]
    field_simp [hR.ne']
    ring
  · dsimp [parabolicAffine]
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
    ring

/-- The exact positive-scale affine image of an open parabolic rectangle. -/
theorem parabolicAffine_image_parabolicRectangle
     {R tau : ℝ} {v0 lower upper : PDE.Vec d} (hR : 0 < R) :
    parabolicAffine 0 v0 R ''
        parabolicRectangle (tau / R ^ 2)
          (pullbackRectangleLower v0 lower R)
          (pullbackRectangleUpper v0 upper R) =
      parabolicRectangle tau lower upper := by
  rw [← parabolicAffine_preimage_parabolicRectangle hR]
  exact Set.image_preimage_eq _ (parabolicAffine_zero_surjective hR)

/-- Positive affine velocity scaling pulls a translated coordinate cube back
to its normalized coordinate cube. -/
theorem mem_affineVelocity_velocityCube_iff  {R eps : ℝ}
    {v0 v : PDE.Vec d} (hR : 0 < R) :
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
