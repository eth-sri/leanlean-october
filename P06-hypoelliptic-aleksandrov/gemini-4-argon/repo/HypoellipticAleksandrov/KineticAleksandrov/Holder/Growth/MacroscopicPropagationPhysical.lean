module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPhysical
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationCorridor
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationEndpoints
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationInitial
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationParameters
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPathBounds
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationDimensionless

/-! # Macroscopic cap comparison stated entirely in physical coordinates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/- The uniform cap comparison applies to every physical sampling subcylinder above cutoff. -/
theorem exists_physical_macroscopic_cap_constant (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (m : ℕ) (r0 )
    (hr0 : 0 < r0) (hr01 : r0 < 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (scale : ℝ), 0 < scale →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
        IsAdmissibleSupersolution A O p C_A u →
      ∀ (Q : KineticPoint d) (r ell : ℝ), 0 < r → r0 * scale ≤ r →
        backwardCylinder Q r ⊆
          backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale →
        0 ≤ ell → (∀ Z ∈ kineticAffine Q r '' cap d, ell ≤ u Z) →
        ∀ P ∈ backwardCylinder P0 scale, c * ell ≤ u P := by
  obtain ⟨c, hc, hc1, hmacro⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
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
          c * ell ≤ u (kineticAffine P0 scale P) := by
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
    have hrp := hr0.trans_le hr
    let S : KineticPoint d := ⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩
    have hS : (⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩ : KineticPoint d) ∈
        closure (samplingCylinder d m) := by
        apply subset_closure
        apply hQ
        rw [← cap_center_affine Q r]
        apply (kineticAffine_mem_cylinder Q _ hrp).mpr
        have _h_inl_7 : (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d) ∈ cap d := by
            norm_num [cap, PDE.euclideanBall, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]

          /- The cap-center affine image is exactly the source propagation start. -/
        exact (closedCap_subset_unitCylinder d) (cap_subset_closedCap d _h_inl_7)

      /- The physical image of an initial tangent is the tangent at the physical initial point. -/
    obtain ⟨x, v, _, _, _, hxP, hvP, hleft, hvc, hxd, hLip, hcorr⟩ : ∃ x v : ℝ → PDE.Vec d,
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
    obtain ⟨hscT, hscH, hscX, hscV⟩ : (r0 ^ 2 / (32 * ((m : ℝ) + 3))) * (((m : ℝ) + 3) * scale ^ 2) =
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
    let xp := physicalPathPosition P0 scale S.time x
    let vp := physicalPathVelocity P0 scale v
    have hsk := physicalPath_isSkeleton P0 hscale S.time
      (-((r0 ^ 2 / 32) * scale ^ 2)) TP hvc hxd hLip
    obtain ⟨hxend, hvend⟩ : physicalPathPosition P0 scale S.time x (scale ^ 2 * (P.time - S.time)) =
          (kineticAffine P0 scale P).position ∧
        physicalPathVelocity P0 scale v (scale ^ 2 * (P.time - S.time)) =
          (kineticAffine P0 scale P).velocity := by
      have hscale := hscale.ne'
      have ht : (scale ^ 2 * (P.time - S.time)) / scale ^ 2 = P.time - S.time := by
        field_simp
      constructor
      · unfold physicalPathPosition
        rw [ht, hxP]
        ext i
        simp only [kineticAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · unfold physicalPathVelocity
        rw [ht, hvP]
        rfl
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
    have hcapInitial : corridor (kineticAffine P0 scale
          (⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩ : KineticPoint d)).time
        (-((r0 ^ 2 / 32) * scale ^ 2)) 0 ((r0 ^ 3 / 1024) * scale ^ 3)
        ((r0 / 16) * scale)
        (physicalPathPosition P0 scale (stackStartTime Q r) x)
        (physicalPathVelocity P0 scale v) ⊆
        kineticAffine (kineticAffine P0 scale Q) (scale * r) '' cap d := by
      let S : KineticPoint d := ⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩
      have hc : kineticAffine P0 scale
            (⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩ : KineticPoint d) =
          ⟨stackStartTime (kineticAffine P0 scale Q) (scale * r),
            stackStartPosition (kineticAffine P0 scale Q) (scale * r),
            (kineticAffine P0 scale Q).velocity⟩ := by
          rw [← cap_center_affine Q r]
          have hc := congrFun (kineticAffine_comp P0 Q scale r)
            (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d)
          exact hc.trans (cap_center_affine _ _)

        /- The fixed macroscopic initial tube is contained in the cap of any larger sampling radius. -/
      have ht := congrArg KineticPoint.time hc
      have hx := congrArg KineticPoint.position hc
      have hv := congrArg KineticPoint.velocity hc
      have hrp := hr0.trans_le hr
      have hsq := pow_le_pow_left₀ hr0.le hr 2
      have hcube := pow_le_pow_left₀ hr0.le hr 3
      have hleft' (s : ℝ) (hs : s ≤ 0) : physicalPathPosition P0 scale S.time x s =
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

        /- Transported path endpoints match the affine target exactly. -/
      have hinc := initial_corridor_subset_cap (kineticAffine P0 scale Q)
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
  refine ⟨c, hc, hc1, ?_⟩
  intro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu Q r ell hr hbig hsub
    hell hcap P hP
  let Qref := kineticAffineInverse P0 scale Q
  let Pref := kineticAffineInverse P0 scale P
  have hrref : r0 ≤ r / scale := (le_div_iff₀ hscale).mpr hbig
  have hsubref := physical_sampling_subcylinder P0 Q hscale hr m hsub
  have hPref : Pref ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    apply (kineticAffine_mem_cylinder P0 Pref hscale).mp
    simpa only [Pref, kineticAffine_apply_inverse P0 hscale.ne'] using hP
  have hcapref : ∀ Z ∈ kineticAffine (kineticAffine P0 scale Qref) (scale * (r / scale)) ''
      cap d, ell ≤ u Z := by
    simpa only [Qref, kineticAffine_apply_inverse P0 hscale.ne',
      mul_div_cancel₀ r hscale.ne'] using hcap
  have hbound := hmacro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu
    Qref (r / scale) ell hrref hsubref hell hcapref Pref hPref
  simpa only [Pref, kineticAffine_apply_inverse P0 hscale.ne'] using hbound

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
