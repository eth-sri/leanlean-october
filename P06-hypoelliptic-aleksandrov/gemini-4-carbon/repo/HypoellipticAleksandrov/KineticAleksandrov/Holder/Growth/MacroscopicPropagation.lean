module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationDimensionless

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/-- Position path in physical affine coordinates, parameterized from its own start time. -/
def physicalPathPosition {d : ℕ} (P0 : KineticPoint d) (scale start : ℝ)
    (x : ℝ → PDE.Vec d) (s : ℝ) : PDE.Vec d :=
  P0.position + scale ^ 3 • x (s / scale ^ 2) +
    (scale ^ 2 * start + s) • P0.velocity

/-- Velocity of the physically transported position path. -/
def physicalPathVelocity {d : ℕ} (P0 : KineticPoint d) (scale : ℝ)
    (v : ℝ → PDE.Vec d) (s : ℝ) : PDE.Vec d :=
  P0.velocity + scale • v (s / scale ^ 2)




/-- The transported path is a source skeleton on any required closed interval. -/
theorem physicalPath_isSkeleton {d : ℕ} (P0 : KineticPoint d) {scale H : ℝ}
    (hscale : 0 < scale) (start a b : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) :
    IsSkeleton (physicalPathPosition P0 scale start x) (physicalPathVelocity P0 scale v)
      (H / scale) a b    := by
  have physicalPath_velocity_continuous :
      Continuous (physicalPathVelocity P0 scale v) := by
    have ht : Continuous (fun s : ℝ => s / scale ^ 2) := continuous_id.div_const _
    have hc : Continuous (fun s : ℝ => P0.velocity + scale • v (s / scale ^ 2)) :=
      (continuous_const (y := P0.velocity)).add ((hv.comp ht).const_smul scale)
    exact hc
  have physicalPath_velocity_lipschitz (s : ℝ) (t : ℝ) :
      PDE.vecEuclideanNorm (physicalPathVelocity P0 scale v s -
      physicalPathVelocity P0 scale v t) ≤ (H / scale) * |s - t| := by
    have heq : physicalPathVelocity P0 scale v s - physicalPathVelocity P0 scale v t =
        scale • (v (s / scale ^ 2) - v (t / scale ^ 2)) := by
      simp only [physicalPathVelocity, smul_sub]
      abel
    rw [heq, PDE.vecEuclideanNorm_smul, abs_of_pos hscale]
    have he := mul_le_mul_of_nonneg_left (hLip (s / scale ^ 2) (t / scale ^ 2)) hscale.le
    apply he.trans_eq
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hscale 2)]
    field_simp
  have physicalPath_derivative {scale : ℝ} (_hscale : scale ≠ 0) (s : ℝ) :
      HasDerivAt (physicalPathPosition P0 scale start x)
      (physicalPathVelocity P0 scale v s) s := by
    apply hasDerivAt_pi.mpr
    intro i
    have hin := (hasDerivAt_id s).div_const (scale ^ 2)
    have hx := ((hasDerivAt_pi.mp (hkin (s / scale ^ 2))) i).comp s hin
    have hfirst := (hx.const_mul (scale ^ 3)).const_add (P0.position i)
    have hlast := ((hasDerivAt_const s (scale ^ 2 * start)).add
      (hasDerivAt_id s)).mul_const (P0.velocity i)
    have h := hfirst.add hlast
    have hd : scale ^ 3 * (v (s / scale ^ 2) i * (1 / scale ^ 2)) +
        (0 + 1 : ℝ) * P0.velocity i = physicalPathVelocity P0 scale v s i := by
      simp only [physicalPathVelocity, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add]
      field_simp
      ring
    rw [hd] at h
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => by
      simp only [physicalPathPosition, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Function.comp_def, id_eq])
  exact ⟨(physicalPath_velocity_continuous).continuousOn,
    fun s _ => (physicalPath_derivative hscale.ne' s).hasDerivWithinAt,
    fun s _ t _ => physicalPath_velocity_lipschitz s t⟩



/-- A transported unit-width corridor lies in the transported reference region. -/
theorem physical_corridor_subset_image {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (start T : ℝ) (x v : ℝ → PDE.Vec d)
    (G : Set (KineticPoint d)) (hcorr : corridor start (-1) T 1 1 x v ⊆ G) :
    corridor (P0.time + scale ^ 2 * start) (-(scale ^ 2)) (scale ^ 2 * T)
      (scale ^ 3) scale (physicalPathPosition P0 scale start x)
      (physicalPathVelocity P0 scale v) ⊆ kineticAffine P0 scale '' G := by
  intro Q hQ
  let s := Q.time - (P0.time + scale ^ 2 * start)
  let Z := kineticAffineInverse P0 scale Q
  have hs : Z.time - start = s / scale ^ 2 := by
    dsimp only [Z, s, kineticAffineInverse]
    field_simp
    ring
  have hx : Z.position - x (Z.time - start) =
      (scale ^ 3)⁻¹ • (Q.position - physicalPathPosition P0 scale start x s) := by
    rw [hs]
    ext i
    simp only [Z, kineticAffineInverse, physicalPathPosition, relativePosition,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s]
    field_simp
    ring
  have hv : Z.velocity - v (Z.time - start) =
      scale⁻¹ • (Q.velocity - physicalPathVelocity P0 scale v s) := by
    rw [hs]
    ext i
    simp only [Z, kineticAffineInverse, physicalPathVelocity, relativeVelocity,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  apply (mem_kineticAffine_image_iff P0 Q hscale.ne' G).mpr
  apply hcorr
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    constructor
    · apply (le_div_iff₀ (pow_pos hscale 2)).mpr
      simpa only [neg_one_mul] using hQ.1.1
    · exact (div_le_iff₀ (pow_pos hscale 2)).mpr
        (hQ.1.2.trans_eq (mul_comm (scale ^ 2) T))
  · rw [hx, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (pow_pos hscale 3))]
    have he := mul_le_mul_of_nonneg_left hQ.2.1
      (inv_nonneg.mpr (pow_nonneg hscale.le 3))
    exact he.trans_eq (inv_mul_cancel₀ (pow_ne_zero 3 hscale.ne'))
  · rw [hv, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hscale)]
    have he := mul_le_mul_of_nonneg_left hQ.2.2 (inv_nonneg.mpr hscale.le)
    exact he.trans_eq (inv_mul_cancel₀ hscale.ne')

/-- Smaller closed intervals and Euclidean widths preserve corridor inclusion. -/
theorem corridor_mono {d : ℕ} (tminus : ℝ) {a a' b b' kx kx' kv kv' : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hx : kx' ≤ kx) (hv : kv' ≤ kv)
    (x v : ℝ → PDE.Vec d) :
    corridor tminus a' b' kx' kv' x v ⊆ corridor tminus a b kx kv x v := by
  intro P hP
  exact ⟨⟨ha.trans hP.1.1, hP.1.2.trans hb⟩, hP.2.1.trans hx, hP.2.2.trans hv⟩




/-- The cap-center affine image is exactly the source propagation start. -/
theorem cap_center_affine {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    kineticAffine P r (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d) =
      ⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ := by
  ext i
  all_goals simp only [kineticAffine, stackStartTime, stackStartPosition,
    smul_zero, add_zero, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals ring


/-- The physical image of an initial tangent is the tangent at the physical initial point. -/
theorem physicalPath_initial_tangent {d : ℕ} (P0 S : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0, x s = S.position + s • S.velocity ∧ v s = S.velocity)
    (s : ℝ) (hs : s ≤ 0) :
    physicalPathPosition P0 scale S.time x s =
        (kineticAffine P0 scale S).position + s • (kineticAffine P0 scale S).velocity ∧
      physicalPathVelocity P0 scale v s = (kineticAffine P0 scale S).velocity := by
  have he := hleft (s / scale ^ 2) (div_nonpos_of_nonpos_of_nonneg hs (sq_nonneg scale))
  constructor
  · unfold physicalPathPosition
    rw [he.1]
    ext i
    simp only [kineticAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · unfold physicalPathVelocity
    rw [he.2]
    rfl

/-- Transported path endpoints match the affine target exactly. -/
theorem physicalPath_endpoint {d : ℕ} (P0 S P : KineticPoint d) {scale : ℝ}
    (hscale : scale ≠ 0) (x v : ℝ → PDE.Vec d)
    (hx : x (P.time - S.time) = P.position) (hv : v (P.time - S.time) = P.velocity) :
    physicalPathPosition P0 scale S.time x (scale ^ 2 * (P.time - S.time)) =
        (kineticAffine P0 scale P).position ∧
      physicalPathVelocity P0 scale v (scale ^ 2 * (P.time - S.time)) =
        (kineticAffine P0 scale P).velocity := by
  have ht : (scale ^ 2 * (P.time - S.time)) / scale ^ 2 = P.time - S.time := by
    field_simp
  constructor
  · unfold physicalPathPosition
    rw [ht, hx]
    ext i
    simp only [kineticAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · unfold physicalPathVelocity
    rw [ht, hv]
    rfl




/-- The fixed macroscopic initial tube is contained in the cap of any larger sampling radius. -/
theorem macroscopic_initial_subset_cap {d : ℕ} (P0 P : KineticPoint d)
    {scale r0 r : ℝ} (hscale : 0 < scale) (hr0 : 0 < r0) (hr : r0 ≤ r)
    (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0,
      x s = stackStartPosition P r + s • P.velocity ∧ v s = P.velocity) :
    corridor (kineticAffine P0 scale
        (⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ : KineticPoint d)).time
      (-((r0 ^ 2 / 32) * scale ^ 2)) 0 ((r0 ^ 3 / 1024) * scale ^ 3)
      ((r0 / 16) * scale)
      (physicalPathPosition P0 scale (stackStartTime P r) x)
      (physicalPathVelocity P0 scale v) ⊆
      kineticAffine (kineticAffine P0 scale P) (scale * r) '' cap d  := by
  have physical_cap_center :
      kineticAffine P0 scale
        (⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ : KineticPoint d) =
      ⟨stackStartTime (kineticAffine P0 scale P) (scale * r),
        stackStartPosition (kineticAffine P0 scale P) (scale * r),
        (kineticAffine P0 scale P).velocity⟩ := by
    rw [← cap_center_affine P r]
    have hc := congrFun (kineticAffine_comp P0 P scale r)
      (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d)
    exact hc.trans (cap_center_affine _ _)
  let S : KineticPoint d := ⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩
  have hc := physical_cap_center
  have ht := congrArg KineticPoint.time hc
  have hx := congrArg KineticPoint.position hc
  have hv := congrArg KineticPoint.velocity hc
  have hrp : 0 < r := hr0.trans_le hr
  have hsq : r0 ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr0.le hr 2
  have hcube : r0 ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hr0.le hr 3
  have hleft' (s : ℝ) (hs : s ≤ 0) :=
    physicalPath_initial_tangent P0 S hscale x v hleft s hs
  have hinc := initial_corridor_subset_cap (kineticAffine P0 scale P)
    (mul_pos hscale hrp)
    (physicalPathPosition P0 scale S.time x) (physicalPathVelocity P0 scale v)
    (fun s hs => by simpa only [S, hx, hv] using hleft' s hs)
  rw [ht]
  apply Subset.trans _ hinc
  apply corridor_mono
  · rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg scale)]
  · exact le_rfl
  · rw [mul_pow]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hcube (pow_nonneg hscale.le 3)]
  · nlinarith [mul_le_mul_of_nonneg_left hr hscale.le]






/-- A cap on a sampling cylinder of radius at least `r0` controls the entire target cylinder.
The cap premise is the local near-full conclusion, to be discharged by the density argument. -/
theorem exists_macroscopic_cap_constant (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (m : ℕ) (r0 : ℝ)
    (hr0 : 0 < r0) (hr01 : r0 < 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (scale : ℝ), 0 < scale →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
        IsAdmissibleSupersolution A O p C_A u →
      ∀ (Q : KineticPoint d) (r ell : ℝ), r0 ≤ r →
        backwardCylinder Q r ⊆ samplingCylinder d m → 0 ≤ ell →
        (∀ Z ∈ kineticAffine (kineticAffine P0 scale Q) (scale * r) '' cap d,
          ell ≤ u Z) →
        ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
          c * ell ≤ u (kineticAffine P0 scale P)    := by
  let macroscopicAcceleration (m : ℕ) :=
    6 * ((m : ℝ) + 5) + 8
  have macroscopic_propagation_scaling {scale : ℝ} (hscale : 0 < scale) :
      (r0 ^ 2 / (32 * ((m : ℝ) + 3))) * (((m : ℝ) + 3) * scale ^ 2) =
        (r0 ^ 2 / 32) * scale ^ 2 ∧
      (macroscopicAcceleration m * Real.sqrt ((m : ℝ) + 3)) /
        Real.sqrt (((m : ℝ) + 3) * scale ^ 2) = macroscopicAcceleration m / scale ∧
      (r0 ^ 3 / (1024 * (((m : ℝ) + 3) ^ (3 / 2 : ℝ)))) *
        (((m : ℝ) + 3) * scale ^ 2) ^ (3 / 2 : ℝ) = (r0 ^ 3 / 1024) * scale ^ 3 ∧
      (r0 / (16 * Real.sqrt ((m : ℝ) + 3))) *
        Real.sqrt (((m : ℝ) + 3) * scale ^ 2) = (r0 / 16) * scale := by
    have hM : 0 < (m : ℝ) + 3 := by positivity
    have hs : Real.sqrt ((m : ℝ) + 3) ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
    have hp : ((m : ℝ) + 3) ^ (3 / 2 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hM _).ne'
    have hsqrt : Real.sqrt (((m : ℝ) + 3) * scale ^ 2) =
        Real.sqrt ((m : ℝ) + 3) * scale := by
      rw [Real.sqrt_mul hM.le, Real.sqrt_sq_eq_abs, abs_of_pos hscale]
    have hpow : (((m : ℝ) + 3) * scale ^ 2) ^ (3 / 2 : ℝ) =
        ((m : ℝ) + 3) ^ (3 / 2 : ℝ) * scale ^ 3 := by
      rw [Real.mul_rpow hM.le (sq_nonneg scale), ← Real.rpow_natCast scale 2,
        ← Real.rpow_mul hscale.le]
      norm_num
    refine ⟨?_, ?_, ?_, ?_⟩
    · field_simp
    · rw [hsqrt]
      field_simp
    · rw [hpow]
      field_simp
    · rw [hsqrt]
      field_simp
  have sampling_cap_center_mem {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r) (hsub : backwardCylinder P r ⊆ samplingCylinder d m) :
      (⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ : KineticPoint d) ∈
      closure (samplingCylinder d m) := by
    have reference_cap_center_mem :
        (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d) ∈ cap d := by
      norm_num [cap, PDE.euclideanBall, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
    apply subset_closure
    apply hsub
    rw [← cap_center_affine P r]
    apply (kineticAffine_mem_cylinder P _ hr).mpr
    exact (closedCap_subset_unitCylinder d) (cap_subset_closedCap d (reference_cap_center_mem))
  let M := (m : ℝ) + 3
  have hM : 0 < M := by dsimp only [M]; positivity
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hr02 : r0 ^ 2 ≤ 1 := by nlinarith only [hr0, hr01]
  have hr03 : r0 ^ 3 ≤ 1 := by
    exact (pow_le_pow_left₀ hr0.le hr01.le 3).trans_eq (by norm_num)
  obtain ⟨c, hc, hc1, hprop⟩ := propagation_dimensionless d hd lam Lam
    (r0 ^ 2 / (32 * M)) (macroscopicAcceleration m * Real.sqrt M)
    (r0 ^ 3 / (1024 * M ^ (3 / 2 : ℝ))) (r0 / (16 * Real.sqrt M))
    hlam hLam (by positivity) (by
      apply (div_le_one (by positivity : 0 < 32 * M)).mpr
      dsimp only [M]
      linarith only [hr02, hm])
    (by unfold macroscopicAcceleration; positivity) (by positivity) (by positivity)
  refine ⟨c, hc, hc1, ?_⟩
  intro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu Q r ell hr hQ hell hcap
    P hP
  have hrp : 0 < r := hr0.trans_le hr
  let S : KineticPoint d := ⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩
  have hS : S ∈ closure (samplingCylinder d m) := sampling_cap_center_mem Q hrp hQ
  obtain ⟨x, v, _, _, _, hxP, hvP, hleft, hvc, hxd, hLip, hcorr⟩ :=
    exists_reference_corridor m S P hS hP
  obtain ⟨hTlo, hThi, _, _⟩ := reference_endpoint_bounds m S P hS hP
  let tminus := (kineticAffine P0 scale S).time
  let TP := scale ^ 2 * (P.time - S.time)
  have ht : (kineticAffine P0 scale P).time - tminus = TP := by
    dsimp only [kineticAffine, tminus, TP]
    ring
  have htminus : tminus = P0.time + scale ^ 2 * S.time := rfl
  have hTPlo : (r0 ^ 2 / 32) * scale ^ 2 ≤ TP := by
    have he := mul_le_mul_of_nonneg_left hTlo (sq_nonneg scale)
    dsimp only [TP]
    have hn : r0 ^ 2 / 32 ≤ (m : ℝ) + 1 := by linarith only [hr02, hm]
    exact (mul_le_mul_of_nonneg_right hn (sq_nonneg scale)).trans (by
      simpa only [mul_comm] using he)
  have hTPhi : TP ≤ M * scale ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hThi (sq_nonneg scale)).trans_eq (mul_comm _ _)
  obtain ⟨hscT, hscH, hscX, hscV⟩ := macroscopic_propagation_scaling hscale
  let xp := physicalPathPosition P0 scale S.time x
  let vp := physicalPathVelocity P0 scale v
  have hsk := physicalPath_isSkeleton P0 hscale S.time
    (-((r0 ^ 2 / 32) * scale ^ 2)) TP hvc hxd hLip
  obtain ⟨hxend, hvend⟩ := physicalPath_endpoint P0 S P hscale.ne' x v hxP hvP
  have hcphys : corridor tminus (-((r0 ^ 2 / 32) * scale ^ 2)) TP
      ((r0 ^ 3 / 1024) * scale ^ 3) ((r0 / 16) * scale) xp vp ⊆ O := by
    apply Subset.trans _ (fun Z hZ => hregion (subset_closure hZ))
    apply Subset.trans _ (physical_corridor_subset_image P0 hscale S.time
      (P.time - S.time) x v _ hcorr)
    rw [htminus]
    apply corridor_mono
    · nlinarith only [mul_le_mul_of_nonneg_right hr02 (sq_nonneg scale), sq_nonneg scale]
    · exact le_rfl
    · nlinarith only [mul_le_mul_of_nonneg_right hr03 (pow_nonneg hscale.le 3),
        pow_nonneg hscale.le 3]
    · nlinarith only [mul_le_mul_of_nonneg_right hr01.le hscale.le, hscale]
  have hPO : kineticAffine P0 scale P ∈ O :=
    hregion (subset_closure ⟨P, unitCylinder_subset_reference d m hP, rfl⟩)
  have hcapInitial := macroscopic_initial_subset_cap P0 Q hscale hr0 hr x v hleft
  have hfinal := hprop (M * scale ^ 2) (mul_pos hM (sq_pos_of_pos hscale))
    p C_A hp A hA O hO tminus (kineticAffine P0 scale P) hPO
  rw [ht, neg_mul, hscT, hscH, hscX, hscV] at hfinal
  apply hfinal hTPlo hTPhi xp vp
    (by simpa only [macroscopicAcceleration] using hsk) hxend hvend hcphys
    ell hell u hnonneg hu
  intro Z hZ htZ
  apply hcap Z
  apply hcapInitial
  exact ⟨⟨hZ.1.1, sub_nonpos.mpr htZ⟩, hZ.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

