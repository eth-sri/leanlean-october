module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Hermite
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesBoundary

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set


/-- The source acceleration coefficient depends only on the stack height. -/
def stackAcceleration (m : ℕ) : ℝ := 384*((m : ℝ)+2)+32

/-- A generous common native-coordinate bound for every stack path. -/
def stackPathBound (m : ℕ) : ℝ := 64*((m : ℝ)+2)

/-- Uniform Euclidean acceleration bound for the source stack Hermite path. -/
theorem stack_hermite_acceleration {d : ℕ} {r T : ℝ} (hr : 0 < r)
    (m : ℕ) (hTlo : r^2/8 ≤ T) (x0 v0 x1 v1 : PDE.Vec d)
    (hx : PDE.vecEuclideanNorm (x1-x0-T • v0) ≤ ((m : ℝ)+2)*r^3)
    (hv : PDE.vecEuclideanNorm (v1-v0) ≤ r) :
    6*PDE.vecEuclideanNorm (x1-x0-T • v0)/T^2+
      4*PDE.vecEuclideanNorm (v1-v0)/T ≤ stackAcceleration m/r := by
  have hT : 0 < T := (by positivity : 0 < r^2/8).trans_le hTlo
  have hs : (r^2/8)^2 ≤ T^2 := by nlinarith
  have h₁ : 6*PDE.vecEuclideanNorm (x1-x0-T • v0)/T^2 ≤
      6*(((m : ℝ)+2)*r^3)/(r^2/8)^2 := by
    apply div_le_div₀ (by positivity) (by nlinarith only [hx]) (by positivity) hs
  have h₂ : 4*PDE.vecEuclideanNorm (v1-v0)/T ≤ 4*r/(r^2/8) := by
    apply div_le_div₀ (by positivity) (by nlinarith only [hv]) (by positivity) hTlo
  have heq : 6*(((m : ℝ)+2)*r^3)/(r^2/8)^2+4*r/(r^2/8) = stackAcceleration m/r := by
    unfold stackAcceleration
    field_simp
    ring
  rw [← heq]
  exact add_le_add h₁ h₂

/-- Elementary absolute-value bounds for the four Hermite coefficients. -/
theorem hermite_unit_coefficients {z : ℝ} (hz : z ∈ Icc 0 1) :
    |3*z^2-2*z^3| ≤ 1 ∧ |z^3-z^2| ≤ 1 ∧
      |6*z-6*z^2| ≤ 6 ∧ |3*z^2-2*z| ≤ 5 := by
  have hz2 : z^2 ≤ z := by nlinarith only [hz.1, hz.2]
  have hz3 : z^3 ≤ z^2 := by nlinarith only [hz.1, hz.2, sq_nonneg z]
  have hc : 0 ≤ z^3 := pow_nonneg hz.1 3
  have hpos : 0 ≤ 3*z^2-2*z^3 := by nlinarith
  have hupper : 3*z^2-2*z^3 ≤ 1 := by
    have h := mul_nonneg (sq_nonneg (1-z)) (by linarith only [hz.1] : 0 ≤ 1+2*z)
    nlinarith
  refine ⟨abs_le.mpr ⟨by linarith, hupper⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩,
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩⟩

/-- Source-relative position and velocity bounds for the unextended Hermite path. -/
theorem stack_hermite_bounds {d : ℕ} {r T : ℝ} (hr : 0 < r) (m : ℕ)
    (hTlo : r^2/8 ≤ T) (hThi : T ≤ ((m : ℝ)+1)*r^2)
    (x0 v0 x1 v1 : PDE.Vec d)
    (hx : PDE.vecEuclideanNorm (x1-x0-T • v0) ≤ ((m : ℝ)+2)*r^3)
    (hv : PDE.vecEuclideanNorm (v1-v0) ≤ r) {s : ℝ} (hs : s ∈ Icc 0 T) :
    PDE.vecEuclideanNorm (hermitePosition T x0 v0 x1 v1 s-x0-s • v0) ≤
      stackPathBound m*r^3 ∧
    PDE.vecEuclideanNorm (hermiteVelocity T x0 v0 x1 v1 s-v0) ≤ stackPathBound m*r := by
  have hT : 0 < T := (by positivity : 0 < r^2/8).trans_le hTlo
  have hz : s/T ∈ Icc 0 1 := ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩
  obtain ⟨hc₁, hc₂, hc₃, hc₄⟩ := hermite_unit_coefficients hz
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  constructor
  · rw [hermitePosition_eq hT.ne']
    have heq : x0+s • v0+(3*(s/T)^2-2*(s/T)^3) • (x1-x0-T • v0)+
        (T*((s/T)^3-(s/T)^2)) • (v1-v0)-x0-s • v0 =
        (3*(s/T)^2-2*(s/T)^3) • (x1-x0-T • v0)+
          (T*((s/T)^3-(s/T)^2)) • (v1-v0) := by abel
    rw [heq]
    have hsum := PDE.vecEuclideanNorm_add_le
      ((3*(s/T)^2-2*(s/T)^3) • (x1-x0-T • v0))
      ((T*((s/T)^3-(s/T)^2)) • (v1-v0))
    rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul,
      abs_mul, abs_of_pos hT] at hsum
    have h₁ := mul_le_mul hc₁ hx (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    have h₂ := mul_le_mul hc₂ hv (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    have h₂' := mul_le_mul_of_nonneg_left h₂ hT.le
    have ht := mul_le_mul_of_nonneg_right hThi hr.le
    unfold stackPathBound
    nlinarith only [hsum, h₁, h₂', ht, hn, pow_pos hr 3]
  · change PDE.vecEuclideanNorm
      (v0+((6*(s/T)-6*(s/T)^2)/T) • (x1-x0-T • v0)+
        (3*(s/T)^2-2*(s/T)) • (v1-v0)-v0) ≤ stackPathBound m*r
    rw [add_assoc, add_sub_cancel_left]
    have hsum := PDE.vecEuclideanNorm_add_le
      (((6*(s/T)-6*(s/T)^2)/T) • (x1-x0-T • v0))
      ((3*(s/T)^2-2*(s/T)) • (v1-v0))
    rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul, abs_div,
      abs_of_pos hT] at hsum
    have h₁ : (|6*(s/T)-6*(s/T)^2|/T)*PDE.vecEuclideanNorm (x1-x0-T • v0) ≤
        (6/(r^2/8))*(((m : ℝ)+2)*r^3) := by
      apply mul_le_mul
      · exact div_le_div₀ (by norm_num) hc₃ (by positivity) hTlo
      · exact hx
      · exact PDE.vecEuclideanNorm_nonneg _
      · positivity
    have h₂ := mul_le_mul hc₄ hv (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    have heq : (6/(r^2/8))*(((m : ℝ)+2)*r^3) = 48*((m : ℝ)+2)*r := by
      field_simp
      ring
    rw [heq] at h₁
    unfold stackPathBound
    nlinarith only [hsum, h₁, h₂, hn, hr]



/-- The cap-center start time in physical coordinates. -/
def stackStartTime {d : ℕ} (P0 : KineticPoint d) (r : ℝ) : ℝ := P0.time-3*r^2/16

/-- The cap-center start position in physical coordinates. -/
def stackStartPosition {d : ℕ} (P0 : KineticPoint d) (r : ℝ) : PDE.Vec d :=
  P0.position-(3*r^2/16) • P0.velocity

/-- Travel duration from the cap-center start to a prescribed stack endpoint. -/
def stackTravelTime {d : ℕ} (P0 P : KineticPoint d) (r : ℝ) : ℝ :=
  P.time-stackStartTime P0 r

/-- The fixed source comparison box for a chosen stack height. -/
def stackComparisonRegion (d m : ℕ) : Set (KineticPoint d) :=
  {P | -2 < P.time ∧ P.time < (m : ℝ)+1 ∧
    PDE.vecEuclideanNorm P.position < stackPathBound m+1 ∧
    PDE.vecEuclideanNorm P.velocity < stackPathBound m+1}

/-- Affine-image membership is inverse-coordinate membership. -/
theorem mem_kineticAffine_image_iff {d : ℕ} (P0 Z : KineticPoint d) {r : ℝ}
    (hr : r ≠ 0) (S : Set (KineticPoint d)) :
    Z ∈ kineticAffine P0 r '' S ↔ kineticAffineInverse P0 r Z ∈ S := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rwa [kineticAffineInverse_apply P0 hr]
  · intro h
    exact ⟨kineticAffineInverse P0 r Z, h, kineticAffine_apply_inverse P0 hr Z⟩

/-- Native position norm in inverse affine coordinates. -/
theorem inverse_position_norm {d : ℕ} (P0 Z : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    PDE.vecEuclideanNorm (kineticAffineInverse P0 r Z).position =
      PDE.vecEuclideanNorm (relativePosition P0 Z)/r^3 := by
  change PDE.vecEuclideanNorm ((r^3)⁻¹ • relativePosition P0 Z) = _
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (pow_pos hr 3))]
  ring

/-- Native velocity norm in inverse affine coordinates. -/
theorem inverse_velocity_norm {d : ℕ} (P0 Z : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    PDE.vecEuclideanNorm (kineticAffineInverse P0 r Z).velocity =
      PDE.vecEuclideanNorm (Z.velocity-P0.velocity)/r := by
  change PDE.vecEuclideanNorm (r⁻¹ • (Z.velocity-P0.velocity)) = _
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
  ring



/-- Increasing the acceleration bound preserves a skeleton. -/
theorem skeleton_mono_bound {d : ℕ} {x v : ℝ → PDE.Vec d} {H K a b : ℝ}
    (hx : IsSkeleton x v H a b) (hHK : H ≤ K) : IsSkeleton x v K a b :=
  ⟨hx.1, hx.2.1, fun s hs t ht => (hx.2.2 s hs t ht).trans
    (mul_le_mul_of_nonneg_right hHK (abs_nonneg _))⟩

/-- The cap-center free-transport displacement equals the path displacement. -/
theorem stack_relative_path {d : ℕ} (P0 : KineticPoint d) (r s : ℝ)
    (z : PDE.Vec d) :
    z-P0.position-(stackStartTime P0 r+s-P0.time) • P0.velocity =
      z-stackStartPosition P0 r-s • P0.velocity := by
  ext i
  simp only [stackStartTime, stackStartPosition, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring



/-- The initial tangent corridor lies in the source cap with strict spatial margins. -/
theorem initial_corridor_subset_cap {d : ℕ} (P0 : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0, x s = stackStartPosition P0 r+s • P0.velocity ∧
      v s = P0.velocity) :
    corridor (stackStartTime P0 r) (-(r^2/32)) 0 (r^3/(2*8^3)) (r/16) x v ⊆
      kineticAffine P0 r '' cap d := by
  intro Z hZ
  apply (mem_kineticAffine_image_iff P0 Z hr.ne' _).mpr
  have hl := hleft _ hZ.1.2
  have hrel : relativePosition P0 Z = Z.position-x (Z.time-stackStartTime P0 r) := by
    rw [hl.1]
    ext i
    simp only [relativePosition, stackStartTime, stackStartPosition, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsq : 0 < r^2 := pow_pos hr 2
  have hcube : 0 < r^3 := pow_pos hr 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -(1/4 : ℝ) < (Z.time-P0.time)/r^2
    apply (lt_div_iff₀ hsq).mpr
    have := hZ.1.1
    dsimp [stackStartTime] at this
    nlinarith
  · change (Z.time-P0.time)/r^2 < -(1/8 : ℝ)
    apply (div_lt_iff₀ hsq).mpr
    have := hZ.1.2
    dsimp [stackStartTime] at this
    nlinarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mpr
    rw [sub_zero, inverse_position_norm P0 Z hr, hrel]
    apply (div_lt_iff₀ hcube).mpr
    have := hZ.2.1
    norm_num at *
    nlinarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mpr
    rw [sub_zero, inverse_velocity_norm P0 Z hr]
    apply (div_lt_iff₀ hr).mpr
    have hv := hZ.2.2
    rw [hl.2] at hv
    linarith

/-- A uniformly bounded path corridor stays in the fixed comparison box. -/
theorem full_corridor_subset_comparison {d : ℕ} (P0 P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (m : ℕ) (hhi : stackTravelTime P0 P r ≤ ((m : ℝ)+1)*r^2)
    (x v : ℝ → PDE.Vec d)
    (hb : ∀ s ∈ Icc (-(r^2/32)) (stackTravelTime P0 P r),
      PDE.vecEuclideanNorm (x s-stackStartPosition P0 r-s • P0.velocity) ≤
        stackPathBound m*r^3 ∧
      PDE.vecEuclideanNorm (v s-P0.velocity) ≤ stackPathBound m*r) :
    corridor (stackStartTime P0 r) (-(r^2/32)) (stackTravelTime P0 P r)
      (r^3/(2*8^3)) (r/16) x v ⊆ kineticAffine P0 r '' stackComparisonRegion d m := by
  intro Z hZ
  apply (mem_kineticAffine_image_iff P0 Z hr.ne' _).mpr
  have hsq : 0 < r^2 := pow_pos hr 2
  have hcube : 0 < r^3 := pow_pos hr 3
  obtain ⟨hx, hv⟩ := hb _ hZ.1
  have hrel : relativePosition P0 Z =
      (Z.position-x (Z.time-stackStartTime P0 r))+
        (x (Z.time-stackStartTime P0 r)-stackStartPosition P0 r-
          (Z.time-stackStartTime P0 r) • P0.velocity) := by
    rw [← stack_relative_path]
    ext i
    simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hn := PDE.vecEuclideanNorm_add_le
    (Z.position-x (Z.time-stackStartTime P0 r))
    (x (Z.time-stackStartTime P0 r)-stackStartPosition P0 r-
      (Z.time-stackStartTime P0 r) • P0.velocity)
  rw [← hrel] at hn
  have hvn := PDE.vecEuclideanNorm_add_le
    (Z.velocity-v (Z.time-stackStartTime P0 r))
    (v (Z.time-stackStartTime P0 r)-P0.velocity)
  rw [sub_add_sub_cancel] at hvn
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -2 < (Z.time-P0.time)/r^2
    apply (lt_div_iff₀ hsq).mpr
    have := hZ.1.1
    dsimp [stackStartTime] at this
    nlinarith
  · change (Z.time-P0.time)/r^2 < (m : ℝ)+1
    apply (div_lt_iff₀ hsq).mpr
    have := hZ.1.2
    dsimp [stackStartTime] at this
    nlinarith
  · rw [inverse_position_norm P0 Z hr]
    apply (div_lt_iff₀ hcube).mpr
    have := hZ.2.1
    norm_num at this
    nlinarith only [hn, hx, this, hcube]
  · rw [inverse_velocity_norm P0 Z hr]
    apply (div_lt_iff₀ hr).mpr
    have := hZ.2.2
    nlinarith only [hvn, hv, this, hr]









/-- Exact source cap and comparison-region corridors for every stack endpoint. -/
theorem exists_stack_corridors {d : ℕ} (P0 P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hP : P ∈ forwardStack P0 r m) :
    ∃ x v : ℝ → PDE.Vec d,
      IsSkeleton x v ((384*((m : ℝ)+2)+32)/r)
        (-(r^2/32)) (P.time-stackStartTime P0 r) ∧
      x 0 = stackStartPosition P0 r ∧ v 0 = P0.velocity ∧
      x (P.time-stackStartTime P0 r) = P.position ∧
      v (P.time-stackStartTime P0 r) = P.velocity ∧
      r^2/8 ≤ P.time-stackStartTime P0 r ∧
      P.time-stackStartTime P0 r ≤ ((m : ℝ)+1)*r^2 ∧
      corridor (stackStartTime P0 r) (-(r^2/32)) 0 (r^3/(2*8^3)) (r/16) x v ⊆
        kineticAffine P0 r '' cap d ∧
      corridor (stackStartTime P0 r) (-(r^2/32)) (P.time-stackStartTime P0 r)
        (r^3/(2*8^3)) (r/16) x v ⊆ kineticAffine P0 r '' stackComparisonRegion d m   := by
  have stack_endpoint_data :
      r^2/8 ≤ stackTravelTime P0 P r ∧
      stackTravelTime P0 P r ≤ ((m : ℝ)+1)*r^2 ∧
      PDE.vecEuclideanNorm (P.position-stackStartPosition P0 r-
        stackTravelTime P0 P r • P0.velocity) ≤ ((m : ℝ)+2)*r^3 ∧
      PDE.vecEuclideanNorm (P.velocity-P0.velocity) ≤ r := by
    have hs := sq_pos_of_pos hr
    have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hP.2.2.1
    have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < ((m+2 : ℕ) : ℝ)*r^3)).mp hP.2.2.2
    rw [sub_zero] at hx
    have heq : P.position-stackStartPosition P0 r-stackTravelTime P0 P r • P0.velocity =
        relativePosition P0 P := by
      ext i
      simp only [stackStartPosition, stackTravelTime, stackStartTime, relativePosition,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, ?_, ?_, hv.le⟩
    · unfold stackTravelTime stackStartTime
      nlinarith only [hP.1, hs]
    · unfold stackTravelTime stackStartTime
      nlinarith only [hP.2.1, hs]
    · rw [heq]
      push_cast at hx
      exact hx.le
  have exists_stack_path :
      ∃ x v : ℝ → PDE.Vec d,
      IsSkeleton x v (stackAcceleration m/r) (-(r^2/32)) (stackTravelTime P0 P r) ∧
      x 0 = stackStartPosition P0 r ∧ v 0 = P0.velocity ∧
      x (stackTravelTime P0 P r) = P.position ∧
      v (stackTravelTime P0 P r) = P.velocity ∧
      (∀ s ≤ 0, x s = stackStartPosition P0 r+s • P0.velocity ∧ v s = P0.velocity) ∧
      (∀ s ∈ Icc (-(r^2/32)) (stackTravelTime P0 P r),
        PDE.vecEuclideanNorm (x s-stackStartPosition P0 r-s • P0.velocity) ≤
          stackPathBound m*r^3 ∧
        PDE.vecEuclideanNorm (v s-P0.velocity) ≤ stackPathBound m*r) := by
    obtain ⟨hlo, hhi, hpos, hvel⟩ := stack_endpoint_data
    let T := stackTravelTime P0 P r
    have hT : 0 < T := lt_of_lt_of_le (by positivity) hlo
    let xh := hermitePosition T (stackStartPosition P0 r) P0.velocity P.position P.velocity
    let vh := hermiteVelocity T (stackStartPosition P0 r) P0.velocity P.position P.velocity
    let H := 6*PDE.vecEuclideanNorm
      (P.position-stackStartPosition P0 r-T • P0.velocity)/T^2+
      4*PDE.vecEuclideanNorm (P.velocity-P0.velocity)/T
    have hsk : IsSkeleton xh vh H 0 T := hermite_isSkeleton hT _ _ _ _
    have hH : 0 ≤ H := by
      have hn₁ := PDE.vecEuclideanNorm_nonneg
        (P.position-stackStartPosition P0 r-T • P0.velocity)
      have hn₂ := PDE.vecEuclideanNorm_nonneg (P.velocity-P0.velocity)
      dsimp [H]
      positivity
    let x := extendPosition xh vh 0 T hT.le
    let v := extendVelocity vh 0 T hT.le
    have hleft (s : ℝ) (hs : s ≤ 0) :
        x s = stackStartPosition P0 r+s • P0.velocity ∧ v s = P0.velocity := by
      constructor
      · dsimp [x]
        rw [extendPosition_left xh vh hT.le hs]
        simp only [xh, vh, hermitePosition_zero, hermiteVelocity_zero, sub_zero]
      · dsimp [v, extendVelocity]
        rw [projIcc_of_le_left hT.le hs]
        exact hermiteVelocity_zero _ _ _ _ _
    refine ⟨x, v, skeleton_mono_bound
      (extendPosition_isSkeleton hT.le hH hsk _ _)
      (stack_hermite_acceleration hr m hlo _ _ _ _ hpos hvel),
      (by simpa using (hleft 0 le_rfl).1), (hleft 0 le_rfl).2, ?_, ?_, hleft, ?_⟩
    · dsimp [x]
      rw [extendPosition_eq hT.le hsk (right_mem_Icc.mpr hT.le)]
      exact hermitePosition_end hT.ne' _ _ _ _
    · dsimp [v]
      rw [extendVelocity_eq vh hT.le (right_mem_Icc.mpr hT.le)]
      exact hermiteVelocity_end hT.ne' _ _ _ _
    · intro s hs
      by_cases h : s ≤ 0
      · rw [(hleft s h).1, (hleft s h).2]
        simp only [add_sub_cancel_left, sub_self]
        rw [PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl]
        constructor <;> dsimp [stackPathBound] <;> positivity
      · have hs' : s ∈ Icc 0 T := ⟨(not_le.mp h).le, hs.2⟩
        dsimp [x, v]
        rw [extendPosition_eq hT.le hsk hs', extendVelocity_eq vh hT.le hs']
        exact stack_hermite_bounds hr m hlo hhi _ _ _ _ hpos hvel hs'
  obtain ⟨hlo, hhi, -, -⟩ := stack_endpoint_data
  obtain ⟨x, v, hsk, hx0, hv0, hxT, hvT, hleft, hb⟩ := exists_stack_path
  exact ⟨x, v, hsk, hx0, hv0, hxT, hvT, hlo, hhi,
    initial_corridor_subset_cap P0 hr x v hleft,
    full_corridor_subset_comparison P0 P hr m hhi x v hb⟩

/-- The same fixed comparison region encloses both reference closures. -/
theorem stackComparisonRegion_geometry (d m : ℕ) :
    IsOpen (stackComparisonRegion d m) ∧ Bornology.IsBounded (stackComparisonRegion d m) ∧
      closure (backwardCylinder (⟨0,0,0⟩ : KineticPoint d) 1) ⊆ stackComparisonRegion d m ∧
      closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
        stackComparisonRegion d m      := by
  have stackPathBound_large :
      (m : ℝ)+3 ≤ stackPathBound m := by
    dsimp [stackPathBound]
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have closure_unitStack_subset_comparison :
      closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
      stackComparisonRegion d m := by
    intro P hP
    have closure_unitStack_bounds :
        closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
        {P | 0 ≤ P.time ∧ P.time ≤ (m : ℝ) ∧
          PDE.vecEuclideanNorm P.position ≤ (m : ℝ)+2 ∧
          PDE.vecEuclideanNorm P.velocity ≤ 1} := by
      apply closure_minimal
      · intro P hP
        change 0 < P.time-0 ∧ P.time-0 ≤ (m : ℝ)*1^2 ∧
          P.velocity ∈ PDE.euclideanBall 0 1 ∧
          relativePosition (⟨0,0,0⟩ : KineticPoint d) P ∈
            PDE.euclideanBall 0 (((m+2 : ℕ) : ℝ)*1^3) at hP
        simp only [sub_zero, one_pow, mul_one] at hP
        have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
          (by positivity : 0 < ((m+2 : ℕ) : ℝ))).mp
          hP.2.2.2
        have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).mp hP.2.2.1
        simp only [relativePosition, sub_zero, smul_zero] at hx hv
        push_cast at hx
        exact ⟨hP.1.le, hP.2.1, hx.le, hv.le⟩
      · exact (isClosed_le continuous_const continuous_time).inter
          ((isClosed_le continuous_time continuous_const).inter
            ((isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_position)
              continuous_const).inter
              (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
                continuous_const)))
    have hb := closure_unitStack_bounds hP
    have hL := stackPathBound_large
    have hm := Nat.cast_nonneg (α := ℝ) m
    exact ⟨by linarith [hb.1], by linarith [hb.2.1],
      by linarith [hb.2.2.1], by linarith [hb.2.2.2]⟩
  have closure_unitCylinder_subset_comparison :
      closure (backwardCylinder (⟨0,0,0⟩ : KineticPoint d) 1) ⊆
      stackComparisonRegion d m := by
    intro P hP
    have hb := Covering.closure_cylinder_bounds (⟨0,0,0⟩ : KineticPoint d) 1 hP
    simp only [relativePosition, sub_zero, smul_zero, one_pow, zero_sub] at hb
    have hx := PDE.vecEuclideanNorm_sq P.position
    have hv := PDE.vecEuclideanNorm_sq P.velocity
    have hxn := PDE.vecEuclideanNorm_nonneg P.position
    have hvn := PDE.vecEuclideanNorm_nonneg P.velocity
    have hL := stackPathBound_large
    have hm := Nat.cast_nonneg (α := ℝ) m
    refine ⟨by linarith [hb.1], by linarith [hb.2.1], ?_, ?_⟩ <;>
      nlinarith [hb.2.2.1, hb.2.2.2]
  have isBounded_stackComparisonRegion :
      Bornology.IsBounded (stackComparisonRegion d m) := by
    let E : Set (KineticPoint d) := (KineticPoint.equivProd d) ⁻¹'
      (Icc (-2 : ℝ) ((m : ℝ)+1) ×ˢ
        (PDE.euclideanClosedBall (0 : PDE.Vec d) (stackPathBound m+1) ×ˢ
          PDE.euclideanClosedBall (0 : PDE.Vec d) (stackPathBound m+1)))
    have hL : 0 ≤ stackPathBound m+1 := by dsimp [stackPathBound]; positivity
    have hc : IsCompact E := (KineticPoint.homeomorphProd d).isCompact_preimage.mpr
      (isCompact_Icc.prod ((PDE.isCompact_euclideanClosedBall _ hL).prod
        (PDE.isCompact_euclideanClosedBall _ hL)))
    apply hc.isBounded.subset
    intro P hP
    refine ⟨⟨hP.1.le, hP.2.1.le⟩, ?_, ?_⟩
    · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
      change PDE.vecEuclideanNorm (P.position-0) ≤ stackPathBound m+1
      simpa only [sub_zero] using hP.2.2.1.le
    · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
      change PDE.vecEuclideanNorm (P.velocity-0) ≤ stackPathBound m+1
      simpa only [sub_zero] using hP.2.2.2.le
  have isOpen_stackComparisonRegion : IsOpen (stackComparisonRegion d m) :=
    (isOpen_lt continuous_const continuous_time).inter
        ((isOpen_lt continuous_time continuous_const).inter
          ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
            continuous_const).inter
            (isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
              continuous_const)))
  exact ⟨isOpen_stackComparisonRegion, isBounded_stackComparisonRegion,
    closure_unitCylinder_subset_comparison, closure_unitStack_subset_comparison⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

