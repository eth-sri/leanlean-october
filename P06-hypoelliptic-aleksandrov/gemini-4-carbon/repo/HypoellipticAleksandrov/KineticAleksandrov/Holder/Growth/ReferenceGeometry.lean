module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridors
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Real
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set


/-- The author-reference box with one extra unit of lower-time buffer. -/
def referenceRegion (d m : ℕ) (L : ℝ) : Set (KineticPoint d) :=
  {P | -((m : ℝ) + 5) < P.time ∧ P.time < 0 ∧
    PDE.vecEuclideanNorm P.position < L ∧ PDE.vecEuclideanNorm P.velocity < L}



/-- Reference-set containment automatically preserves the admissibility domain. -/
theorem buffered_reference_preserves_domain {d : ℕ} (P0 : KineticPoint d) {R eps L : ℝ}
    (hR : 0 < R) (m : ℕ)
    (hunit : kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' referenceRegion d m L ⊆
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
    (O : Set (KineticPoint d)) (hO : closure (backwardCylinder P0 R) ⊆ O) :
    closure (kineticAffine P0 (R * eps) '' referenceRegion d m L) ⊆ O := by
  apply (closure_mono ?_).trans hO
  rw [← kineticAffine_image_unitCylinder P0 hR]
  rintro _ ⟨P, hP, rfl⟩
  have hcomp := congrFun (kineticAffine_comp P0 (⟨0, 0, 0⟩ : KineticPoint d) R eps) P
  have hzero : kineticAffine P0 R (⟨0, 0, 0⟩ : KineticPoint d) = P0 := by
    simp only [kineticAffine, mul_zero, smul_zero, zero_smul, add_zero]
  rw [hzero] at hcomp
  exact ⟨kineticAffine ⟨0, 0, 0⟩ eps P, hunit ⟨P, hP, rfl⟩, hcomp⟩



/-- The source's reference sampling center before its small dilation. -/
def samplingCenter (d m : ℕ) : KineticPoint d := ⟨-((m : ℝ) + 2), 0, 0⟩

/-- The source's reference sampling cylinder before its small dilation. -/
def samplingCylinder (d m : ℕ) : Set (KineticPoint d) :=
  backwardCylinder (samplingCenter d m) 1

/-- The buffered reference region is open in physical coordinates. -/
theorem isOpen_referenceRegion (d m : ℕ) (L : ℝ) : IsOpen (referenceRegion d m L) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
        continuous_const).inter
        (isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
          continuous_const)))

/-- A finite rectangular envelope bounds the reference region. -/
theorem isBounded_referenceRegion (d m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Bornology.IsBounded (referenceRegion d m L) := by
  let E : Set (KineticPoint d) := (KineticPoint.equivProd d) ⁻¹'
    (Icc (-((m : ℝ) + 5)) 0 ×ˢ
      (PDE.euclideanClosedBall (0 : PDE.Vec d) L ×ˢ
        PDE.euclideanClosedBall (0 : PDE.Vec d) L))
  have hc : IsCompact E := (KineticPoint.homeomorphProd d).isCompact_preimage.mpr
    (isCompact_Icc.prod ((PDE.isCompact_euclideanClosedBall _ hL).prod
      (PDE.isCompact_euclideanClosedBall _ hL)))
  apply hc.isBounded.subset
  intro P hP
  refine ⟨⟨hP.1.le, hP.2.1.le⟩, ?_, ?_⟩
  · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
    change PDE.vecEuclideanNorm (P.position - 0) ≤ L
    simpa only [sub_zero] using hP.2.2.1.le
  · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
    change PDE.vecEuclideanNorm (P.velocity - 0) ≤ L
    simpa only [sub_zero] using hP.2.2.2.le

/-- Sampling closure coordinates have the exact unit Euclidean bounds. -/
theorem sampling_closure_bounds (d m : ℕ) (P : KineticPoint d)
    (hP : P ∈ closure (samplingCylinder d m)) :
    -((m : ℝ) + 3) ≤ P.time ∧ P.time ≤ -((m : ℝ) + 2) ∧
      PDE.vecEuclideanNorm P.position ≤ 1 ∧ PDE.vecEuclideanNorm P.velocity ≤ 1 := by
  have hb := Covering.closure_cylinder_bounds (samplingCenter d m) 1 hP
  simp only [samplingCenter, relativePosition, sub_zero, smul_zero, one_pow] at hb
  refine ⟨by linarith only [hb.1], hb.2.1, ?_, ?_⟩
  · have hn := PDE.vecEuclideanNorm_nonneg P.position
    have hs := PDE.vecEuclideanNorm_sq P.position
    nlinarith only [hn, hs, hb.2.2.2]
  · have hn := PDE.vecEuclideanNorm_nonneg P.velocity
    have hs := PDE.vecEuclideanNorm_sq P.velocity
    nlinarith only [hn, hs, hb.2.2.1]

/-- The added time buffer strictly encloses the entire sampling-cylinder closure. -/
theorem sampling_closure_subset_reference (d m : ℕ) {L : ℝ} (hL : 1 < L) :
    closure (samplingCylinder d m) ⊆ referenceRegion d m L := by
  intro P hP
  obtain ⟨htlo, htup, hx, hv⟩ := sampling_closure_bounds d m P hP
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  exact ⟨by linarith only [htlo], by linarith only [htup, hm],
    hx.trans_lt hL, hv.trans_lt hL⟩



/-- The reference endpoint estimates use the Euclidean triangle inequality for differences. -/
theorem reference_norm_sub_le {d : ℕ} (x y : PDE.Vec d) :
    PDE.vecEuclideanNorm (x - y) ≤ PDE.vecEuclideanNorm x + PDE.vecEuclideanNorm y := by
  rw [sub_eq_add_neg]
  simpa only [PDE.vecEuclideanNorm_neg] using PDE.vecEuclideanNorm_add_le x (-y)

/-- A fixed finite spatial reference bound, chosen before the physical scale. -/
def referenceBound (m : ℕ) : ℝ := 16 * stackPathBound m + (m : ℝ) + 20

/-- Reference endpoints give the source travel-time and Hermite displacement bounds. -/
theorem reference_endpoint_bounds {d : ℕ} (m : ℕ) (S P : KineticPoint d)
    (hS : S ∈ closure (samplingCylinder d m))
    (hP : P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) :
    (m : ℝ) + 1 ≤ P.time - S.time ∧ P.time - S.time ≤ (m : ℝ) + 3 ∧
      PDE.vecEuclideanNorm (P.position - S.position - (P.time - S.time) • S.velocity) ≤
        (m : ℝ) + 5 ∧ PDE.vecEuclideanNorm (P.velocity - S.velocity) ≤ 2 := by
  obtain ⟨hstlo, hstup, hsx, hsv⟩ := sampling_closure_bounds d m S hS
  have hpv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1)).mp hP.2.2.1
  have hpx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 ^ 3)).mp hP.2.2.2
  simp only [relativePosition, sub_zero, smul_zero, one_pow] at hpx hpv
  have hptlo : -1 < P.time := by simpa only [one_pow, zero_sub] using hP.1
  have hptup : P.time < 0 := hP.2.1
  have hTlo : (m : ℝ) + 1 ≤ P.time - S.time := by linarith only [hptlo, hstup]
  have hThi : P.time - S.time ≤ (m : ℝ) + 3 := by linarith only [hptup, hstlo]
  have hT : 0 ≤ P.time - S.time := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hTlo, hm]
  refine ⟨hTlo, hThi, ?_, ?_⟩
  · apply (reference_norm_sub_le _ _).trans
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hT]
    have hx := reference_norm_sub_le P.position S.position
    have hv := mul_le_mul_of_nonneg_left hsv hT
    linarith only [hx, hpx, hsx, hv, hThi]
  · have hv := reference_norm_sub_le P.velocity S.velocity
    linarith only [hv, hpv, hsv]

/-- The reference Hermite acceleration has exactly the source upper bound. -/
theorem reference_hermite_acceleration {d : ℕ} (m : ℕ) {T : ℝ}
    (hTlo : (m : ℝ) + 1 ≤ T) (x0 v0 x1 v1 : PDE.Vec d)
    (hx : PDE.vecEuclideanNorm (x1 - x0 - T • v0) ≤ (m : ℝ) + 5)
    (hv : PDE.vecEuclideanNorm (v1 - v0) ≤ 2) :
    6 * PDE.vecEuclideanNorm (x1 - x0 - T • v0) / T ^ 2 +
      4 * PDE.vecEuclideanNorm (v1 - v0) / T ≤ 6 * ((m : ℝ) + 5) + 8 := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hT : 1 ≤ T := by linarith only [hTlo, hm]
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hT2 : 1 ≤ T ^ 2 := by nlinarith only [hT]
  have hx0 := PDE.vecEuclideanNorm_nonneg (x1 - x0 - T • v0)
  have hv0 := PDE.vecEuclideanNorm_nonneg (v1 - v0)
  have he1 : 6 * PDE.vecEuclideanNorm (x1 - x0 - T • v0) / T ^ 2 ≤
      6 * ((m : ℝ) + 5) := by
    apply (div_le_iff₀ (sq_pos_of_pos hT0)).mpr
    have he := mul_le_mul_of_nonneg_left hT2
      (show 0 ≤ 6 * ((m : ℝ) + 5) by positivity)
    nlinarith only [he, hx]
  have he2 : 4 * PDE.vecEuclideanNorm (v1 - v0) / T ≤ 8 := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith only [hv, hT]
  exact add_le_add he1 he2



/-- All subcylinder comparison boxes share the same reference region. -/
theorem sampling_comparison_image_subset {d : ℕ} (m : ℕ) (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ samplingCylinder d m) :
    kineticAffine P r '' stackComparisonRegion d m ⊆ referenceRegion d m (referenceBound m)  := by
  have sampling_subcylinder_bounds :
      r ≤ 1 ∧ -((m : ℝ) + 3) ≤ P.time ∧ P.time ≤ -((m : ℝ) + 2) ∧
      PDE.vecEuclideanNorm P.position ≤ 1 ∧ PDE.vecEuclideanNorm P.velocity ≤ 1 := by
    have bottom_mem_closure_cylinder :
        (⟨P.time - r ^ 2, P.position + (-r ^ 2) • P.velocity, P.velocity⟩ : KineticPoint d) ∈
        closure (backwardCylinder P r) := by
      let f : ℝ → KineticPoint d := fun t =>
        ⟨t, P.position + (t - P.time) • P.velocity, P.velocity⟩
      have hf : Continuous f := KineticPoint.continuous_mk continuous_id
        (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const))
        continuous_const
      have hsub : f '' Ioo (P.time - r ^ 2) P.time ⊆ backwardCylinder P r := by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨ht.1, ht.2, PDE.center_mem_euclideanBall _ hr, ?_⟩
        have heq : relativePosition P (f t) = 0 := by
          ext i
          simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
            Pi.zero_apply, smul_eq_mul]
          ring
        rw [heq]
        exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)
      have ht : P.time - r ^ 2 ∈ closure (Ioo (P.time - r ^ 2) P.time) := by
        rw [closure_Ioo (sub_lt_self _ (sq_pos_of_pos hr)).ne]
        exact ⟨le_rfl, sub_le_self _ (sq_nonneg r)⟩
      have h := closure_mono hsub
        (hf.continuousOn.image_closure (mem_image_of_mem f ht))
      simpa only [f, sub_sub_cancel_left] using h
    have hc := closure_mono hsub
      (Covering.top_mem_closure_cylinder P hr (PDE.center_mem_euclideanBall _ hr))
    have hb := sampling_closure_bounds d m P hc
    have hbottom := (sampling_closure_bounds d m _
      (closure_mono hsub (bottom_mem_closure_cylinder))).1
    have hr2 : r ^ 2 ≤ 1 := by linarith only [hbottom, hb.2.1]
    exact ⟨by nlinarith only [hr2, hr], hb⟩
  obtain ⟨hr1, htlo, htup, hx, hv⟩ := sampling_subcylinder_bounds
  have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr, hr1]
  have hr3 : r ^ 3 ≤ 1 := by
    have he := mul_le_mul hr2 hr1 hr.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [he]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  rintro _ ⟨Y, hY, rfl⟩
  obtain ⟨hytlo, hytup, hyx, hyv⟩ := hY
  have hytime : |Y.time| ≤ (m : ℝ) + 3 := by
    exact abs_le.mpr ⟨by linarith only [hytlo, hm], by linarith only [hytup]⟩
  have htxlo := mul_lt_mul_of_pos_left hytlo (sq_pos_of_pos hr)
  have htxup := mul_le_mul_of_nonneg_left hytup.le (sq_nonneg r)
  have htm := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hyxscaled : r ^ 3 * PDE.vecEuclideanNorm Y.position ≤ stackPathBound m + 1 := by
    have he := mul_le_mul hr3 hyx.le (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    simpa only [one_mul] using he
  have hyvscaled : r * PDE.vecEuclideanNorm Y.velocity ≤ stackPathBound m + 1 := by
    have he := mul_le_mul hr1 hyv.le (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    simpa only [one_mul] using he
  have htimescaled : r ^ 2 * |Y.time| ≤ (m : ℝ) + 3 := by
    have he := mul_le_mul hr2 hytime (abs_nonneg _) (by norm_num)
    simpa only [one_mul] using he
  have htransport : PDE.vecEuclideanNorm ((r ^ 2 * Y.time) • P.velocity) ≤ (m : ℝ) + 3 := by
    rw [PDE.vecEuclideanNorm_smul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    have he := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg r) (abs_nonneg Y.time))
    simpa only [mul_one] using he.trans (by simpa only [mul_one] using htimescaled)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -((m : ℝ) + 5) < P.time + r ^ 2 * Y.time
    linarith only [htxlo, hr2, htlo]
  · change P.time + r ^ 2 * Y.time < 0
    linarith only [htup, htxup, htm]
  · change PDE.vecEuclideanNorm
        (P.position + r ^ 3 • Y.position + (r ^ 2 * Y.time) • P.velocity) < referenceBound m
    have he := PDE.vecEuclideanNorm_add_le
      (P.position + r ^ 3 • Y.position) ((r ^ 2 * Y.time) • P.velocity)
    have he' := PDE.vecEuclideanNorm_add_le P.position (r ^ 3 • Y.position)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)] at he'
    dsimp only [referenceBound]
    linarith only [he, he', hx, hyxscaled, htransport, hB]
  · change PDE.vecEuclideanNorm (P.velocity + r • Y.velocity) < referenceBound m
    have he := PDE.vecEuclideanNorm_add_le P.velocity (r • Y.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos hr] at he
    dsimp only [referenceBound]
    linarith only [he, hv, hyvscaled, hB, hm]



/-- Every reference endpoint has an actual source Hermite/tangent path in the buffered box. -/
theorem exists_reference_corridor {d : ℕ} (m : ℕ) (S P : KineticPoint d)
    (hS : S ∈ closure (samplingCylinder d m))
    (hP : P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) :
    ∃ x v : ℝ → PDE.Vec d,
      IsSkeleton x v (6 * ((m : ℝ) + 5) + 8) (-1) (P.time - S.time) ∧
      x 0 = S.position ∧ v 0 = S.velocity ∧
      x (P.time - S.time) = P.position ∧ v (P.time - S.time) = P.velocity ∧
      (∀ s ≤ 0, x s = S.position + s • S.velocity ∧ v s = S.velocity) ∧
      Continuous v ∧ (∀ s, HasDerivAt x (v s) s) ∧
      (∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤
        (6 * ((m : ℝ) + 5) + 8) * |s - t|) ∧
      corridor S.time (-1) (P.time - S.time) 1 1 x v ⊆
        referenceRegion d m (referenceBound m) := by
  obtain ⟨hTlo, hThi, hx, hv⟩ := reference_endpoint_bounds m S P hS hP
  obtain ⟨hstlo, _, hsx, hsv⟩ := sampling_closure_bounds d m S hS
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  let T := P.time - S.time
  have hT : 0 < T := by dsimp only [T]; linarith only [hTlo, hm]
  let xh := hermitePosition T S.position S.velocity P.position P.velocity
  let vh := hermiteVelocity T S.position S.velocity P.position P.velocity
  let H := 6 * PDE.vecEuclideanNorm (P.position - S.position - T • S.velocity) / T ^ 2 +
    4 * PDE.vecEuclideanNorm (P.velocity - S.velocity) / T
  have hH : 0 ≤ H := by
    have hx0 := PDE.vecEuclideanNorm_nonneg (P.position - S.position - T • S.velocity)
    have hv0 := PDE.vecEuclideanNorm_nonneg (P.velocity - S.velocity)
    dsimp only [H]
    positivity
  have hsk : IsSkeleton xh vh H 0 T := hermite_isSkeleton hT _ _ _ _
  let x := extendPosition xh vh 0 T hT.le
  let v := extendVelocity vh 0 T hT.le
  have hleft (s : ℝ) (hs : s ≤ 0) : x s = S.position + s • S.velocity ∧
      v s = S.velocity := by
    constructor
    · dsimp only [x]
      rw [extendPosition_left xh vh hT.le hs]
      simp only [xh, vh, hermitePosition_zero, hermiteVelocity_zero, sub_zero]
    · dsimp only [v, extendVelocity]
      rw [projIcc_of_le_left hT.le hs]
      exact hermiteVelocity_zero _ _ _ _ _
  have hB : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  have hbounds : ∀ s ∈ Icc (-1) T,
      PDE.vecEuclideanNorm (x s) ≤ (m : ℝ) + 4 + 8 * stackPathBound m ∧
        PDE.vecEuclideanNorm (v s) ≤ 1 + 2 * stackPathBound m := by
    intro s hs
    by_cases h : s ≤ 0
    · rw [(hleft s h).1, (hleft s h).2]
      have habs : |s| ≤ 1 := by rw [abs_of_nonpos h]; linarith only [hs.1]
      have hvbound := mul_le_mul habs hsv (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
      have hb := PDE.vecEuclideanNorm_add_le S.position (s • S.velocity)
      rw [PDE.vecEuclideanNorm_smul] at hb
      constructor <;> linarith only [hb, hvbound, hsx, hsv, hm, hB]
    · have hs' : s ∈ Icc 0 T := ⟨(lt_of_not_ge h).le, hs.2⟩
      have hb := stack_hermite_bounds (by norm_num : (0 : ℝ) < 2) m
        (by norm_num; linarith only [hTlo, hm] : (2 : ℝ) ^ 2 / 8 ≤ T)
        (by norm_num; linarith only [hThi, hm] : T ≤ ((m : ℝ) + 1) * (2 : ℝ) ^ 2)
        S.position S.velocity P.position P.velocity
        (by norm_num; linarith only [hx, hm]) (by exact hv) hs'
      norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num] at hb
      have hxs : x s = xh s := extendPosition_eq hT.le hsk hs'
      have hvs : v s = vh s := extendVelocity_eq vh hT.le hs'
      rw [hxs, hvs]
      have heq : xh s = S.position + s • S.velocity +
          (xh s - S.position - s • S.velocity) := by abel
      have hvq : vh s = S.velocity + (vh s - S.velocity) := by abel
      have hsbound : s ≤ (m : ℝ) + 3 := hs.2.trans hThi
      have hvnorm := mul_le_mul_of_nonneg_left hsv hs'.1
      have hxp := PDE.vecEuclideanNorm_add_le S.position (s • S.velocity)
      rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hs'.1] at hxp
      constructor
      · rw [heq]
        have he := PDE.vecEuclideanNorm_add_le (S.position + s • S.velocity)
          (xh s - S.position - s • S.velocity)
        linarith only [he, hxp, hvnorm, hsx, hsbound, hb.1]
      · rw [hvq]
        have he := PDE.vecEuclideanNorm_add_le S.velocity (vh s - S.velocity)
        linarith only [he, hsv, hb.2]
  refine ⟨x, v, skeleton_mono_bound
    (extendPosition_isSkeleton hT.le hH hsk _ _)
    (reference_hermite_acceleration m hTlo _ _ _ _ hx hv),
    (by simpa only [zero_smul, add_zero] using (hleft 0 le_rfl).1),
    (hleft 0 le_rfl).2, ?_, ?_, hleft,
    continuous_extendVelocity hT.le hsk.1,
    hasDerivAt_extendPosition hT.le hsk, ?_, ?_⟩
  · dsimp only [x]
    rw [extendPosition_eq hT.le hsk (right_mem_Icc.mpr hT.le)]
    exact hermitePosition_end hT.ne' _ _ _ _
  · dsimp only [v]
    rw [extendVelocity_eq vh hT.le (right_mem_Icc.mpr hT.le)]
    exact hermiteVelocity_end hT.ne' _ _ _ _
  · intro s t
    exact (extendVelocity_lipschitz hT.le hH hsk s t).trans
      (mul_le_mul_of_nonneg_right
        (reference_hermite_acceleration m hTlo _ _ _ _ hx hv) (abs_nonneg _))
  · intro Q hQ
    have hb := hbounds (Q.time - S.time) hQ.1
    have hpt : P.time < 0 := hP.2.1
    have hxq : Q.position = (Q.position - x (Q.time - S.time)) +
        x (Q.time - S.time) := by abel
    have hvq : Q.velocity = (Q.velocity - v (Q.time - S.time)) +
        v (Q.time - S.time) := by abel
    refine ⟨by linarith only [hQ.1.1, hstlo],
      by linarith only [hQ.1.2, hpt], ?_, ?_⟩
    · rw [hxq]
      apply (PDE.vecEuclideanNorm_add_le _ _).trans_lt
      dsimp only [referenceBound]
      linarith only [hQ.2.1, hb.1, hB]
    · rw [hvq]
      apply (PDE.vecEuclideanNorm_add_le _ _).trans_lt
      dsimp only [referenceBound]
      linarith only [hQ.2.2, hb.2, hB, hm]



/-- The reference bound strictly exceeds one. -/
theorem referenceBound_large (m : ℕ) : 1 < referenceBound m := by
  have hb : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold referenceBound
  linarith only [hb, hm]

/-- The target unit cylinder lies in the same reference region as the sampling closure. -/
theorem unitCylinder_subset_reference (d m : ℕ) :
    backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ⊆
      referenceRegion d m (referenceBound m) := by
  intro P hP
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hL := referenceBound_large m
  have hpv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1)).mp hP.2.2.1
  have hpx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 ^ 3)).mp hP.2.2.2
  simp only [relativePosition, sub_zero, smul_zero, one_pow] at hpx hpv
  have htlo : -1 < P.time := by simpa only [one_pow, zero_sub] using hP.1
  exact ⟨by linarith only [htlo, hm], hP.2.1, hpx.trans hL, hpv.trans hL⟩

/-- One smaller reference scale preserves all positivity and admissibility data. -/
theorem exists_reference_geometry (d m : ℕ) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
      IsOpen (referenceRegion d m (referenceBound m)) ∧
      Bornology.IsBounded (referenceRegion d m (referenceBound m)) ∧
      closure (samplingCylinder d m) ⊆ referenceRegion d m (referenceBound m) ∧
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ⊆
        referenceRegion d m (referenceBound m) ∧
      kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps ''
        referenceRegion d m (referenceBound m) ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
      closure (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' samplingCylinder d m) ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1  := by
  have exists_buffered_reference_scale {L : ℝ} (hL : 0 < L) :
      ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
      kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' referenceRegion d m L ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    have referenceRegion_scaled_subset_unit {L : ℝ} {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (ht : eps * ((m : ℝ) + 5) < 1) (hspace : eps * L < 1) :
        kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' referenceRegion d m L ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
      have heps2 : eps ^ 2 ≤ eps := by nlinarith only [heps.le, heps1]
      have heps3 : eps ^ 3 ≤ eps := by
        have he := mul_le_mul_of_nonneg_right heps2 heps.le
        nlinarith only [he, heps2]
      rintro _ ⟨P, hP, rfl⟩
      obtain ⟨hlo, hhi, hx, hv⟩ := hP
      have htime : eps ^ 2 * ((m : ℝ) + 5) < 1 :=
        (mul_le_mul_of_nonneg_right heps2 (by positivity)).trans_lt ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (0 : ℝ) - 1 ^ 2 < 0 + eps ^ 2 * P.time
        have he := mul_lt_mul_of_pos_left hlo (pow_pos heps 2)
        norm_num only [one_pow, zero_sub, zero_add]
        linarith only [he, htime]
      · change 0 + eps ^ 2 * P.time < (0 : ℝ)
        simpa only [zero_add] using mul_neg_of_pos_of_neg (pow_pos heps 2) hhi
      · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1)).mpr
        change PDE.vecEuclideanNorm (0 + eps • P.velocity - 0) < 1
        rw [zero_add, sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos heps]
        exact (mul_lt_mul_of_pos_left hv heps).trans hspace
      · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
          (by norm_num : (0 : ℝ) < 1 ^ 3)).mpr
        have hrel : relativePosition (⟨0, 0, 0⟩ : KineticPoint d)
            (kineticAffine ⟨0, 0, 0⟩ eps P) = eps ^ 3 • P.position := by
          simp only [relativePosition, kineticAffine, smul_zero, add_zero, zero_add, sub_zero]
        rw [hrel, sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos heps 3)]
        norm_num only [one_pow]
        have hx0 := PDE.vecEuclideanNorm_nonneg P.position
        exact ((mul_le_mul_of_nonneg_right heps3 hx0).trans_lt
          (mul_lt_mul_of_pos_left hx heps)).trans hspace
    let D := 2 * ((m : ℝ) + 5 + L + 1)
    let eps := D⁻¹
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hD : 0 < D := by dsimp only [D]; linarith only [hm, hL]
    have heps : 0 < eps := inv_pos.mpr hD
    have heq : eps * D = 1 := inv_mul_cancel₀ hD.ne'
    have hD1 : 1 < D := by dsimp only [D]; linarith only [hm, hL]
    have heps1 : eps < 1 := by
      have he := mul_lt_mul_of_pos_left hD1 heps
      rw [mul_one, heq] at he
      exact he
    have htime : eps * ((m : ℝ) + 5) < 1 := by
      have hd : (m : ℝ) + 5 < D := by dsimp only [D]; linarith only [hm, hL]
      exact (mul_lt_mul_of_pos_left hd heps).trans_eq heq
    have hspace : eps * L < 1 := by
      have hd : L < D := by dsimp only [D]; linarith only [hm, hL]
      exact (mul_lt_mul_of_pos_left hd heps).trans_eq heq
    exact ⟨eps, heps, heps1,
      referenceRegion_scaled_subset_unit heps heps1.le htime hspace⟩
  have hL := referenceBound_large m
  obtain ⟨eps, heps, heps1, himage⟩ := exists_buffered_reference_scale
    (lt_trans (by norm_num) hL)
  have hsigma := sampling_closure_subset_reference d m hL
  refine ⟨eps, heps, heps1, isOpen_referenceRegion d m _,
    isBounded_referenceRegion d m (le_of_lt (lt_trans (by norm_num) hL)), hsigma,
    unitCylinder_subset_reference d m, himage, ?_⟩
  let e := kineticAffineHomeomorph (⟨0, 0, 0⟩ : KineticPoint d) eps heps.ne'
  change closure (e '' samplingCylinder d m) ⊆ _
  rw [← e.image_closure]
  exact (image_mono hsigma).trans himage

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

