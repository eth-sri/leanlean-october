module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockSource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockComparison
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockContainment
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockPositive
import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSign
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource

/-! # The source one-block comparison with all boundary and source terms discharged -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set
open MeasureTheory

/- Initial-strip comparison propagates throughout the source block in the halved tube. -/
theorem propagation_one_block {d } (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus sblock TP : ℝ)
    (hsblock : 0 ≤ sblock) (hblock : sblock + h ≤ TP)
    {x v } (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A } (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinit : ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      P.time - tminus - sblock ≤ 0 →
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus sblock x v P ≤ u P) :
    ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus sblock x v P ≤ u P := by
  let R := barrierW d lam Lam H T1 * Real.sqrt h
  let P₀ : KineticPoint d :=
    ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
  have hR : 0 < R := mul_pos
    (lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)) (Real.sqrt_pos.mpr hh)
  have hQO := (propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
    tminus sblock TP hsblock hblock hv.continuous hkin hLip).trans htube
  apply admissible_test_le_of_zero_source hu P₀ hR hQO
    (gaussianBarrier_isSmoothNear hlam hh Lam H (barrierL d lam Lam H T1)
      ell tminus sblock hx hv _)
  · intro P hP
    have _h_xinl_0 : gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P ≤ 0 := by
      have hv := hv.continuous
      by_contra hn
      have hp := lt_of_not_ge hn
      obtain ⟨hc, hb⟩ := mem_kineticBoundary_iff.mp hP
      obtain ⟨hvball, hxball⟩ : P.velocity ∈ PDE.euclideanBall (v (sblock + h))
            (barrierW d lam Lam H T1 * Real.sqrt h) ∧
          relativePosition ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ P ∈
            PDE.euclideanBall (0 : PDE.Vec d) ((barrierW d lam Lam H T1 * Real.sqrt h) ^ 3) := by
          let L := barrierL d lam Lam H T1
          let W := barrierW d lam Lam H T1
          let C := (3 / 2 : ℝ) * L * Real.sqrt lam
          let b := sblock + h
          let s := P.time - tminus
          let R := W * Real.sqrt h
          let P₀ : KineticPoint d := ⟨tminus + sblock + h, x b, v b⟩
          have hW2 : 2 ≤ W := two_le_barrierW hH
          have hW : 0 < W := by linarith only [hW2]
          have hR : 0 < R := mul_pos hW (Real.sqrt_pos.mpr hh)
          have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
          have ht := (closure_backwardCylinder_bounds P₀ hR hc).2.1
          have hs1 : P.time - tminus - sblock ≤ h := by
            change P.time ≤ tminus + sblock + h at ht
            linarith only [ht]
          obtain ⟨hs0, _⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
            hLam hell hbudget x v P hp
          obtain ⟨hy, hV⟩ := gaussianBarrier_positive_set hlam hh Lam H L ell tminus sblock
            hLam hell (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hbudget x v P hs1 hp
          have hdelta : 0 ≤ b - s ∧ b - s ≤ 2 * h := by
            dsimp only [b, s]
            constructor <;> linarith only [hs0, hs1, hh]
          have hhT1 : h ≤ T1 := by
            have he := (propagation_step_time hH hh hhstar).2
            linarith only [he, hT1, hh]
          have hhalf : h ≤ Real.sqrt T1 * Real.sqrt h := by
            have he := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hhT1) (Real.sqrt_nonneg h)
            nlinarith only [he, Real.sq_sqrt hh.le]
          have hthree : h ^ 2 ≤ Real.sqrt T1 * h ^ (3 / 2 : ℝ) := by
            have he : h ^ 2 = h ^ (3 / 2 : ℝ) * Real.sqrt h := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
              norm_num
            rw [he]
            simpa only [mul_comm] using mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hhT1) (Real.rpow_nonneg hh.le _)
          have hpathv := hLip s b
          rw [abs_sub_comm, abs_of_nonneg hdelta.1] at hpathv
          have hveq : P.velocity - v b = (P.velocity - v s) + (v s - v b) := by abel
          have hvbound : PDE.vecEuclideanNorm (P.velocity - v b) ≤
              (C + 2 * H * Real.sqrt T1) * Real.sqrt h := by
            rw [hveq]
            apply (PDE.vecEuclideanNorm_add_le _ _).trans
            calc
              _ ≤ C * Real.sqrt h + H * (b - s) := add_le_add hV hpathv
              _ ≤ C * Real.sqrt h + H * (2 * h) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hdelta.2 hH)
              _ ≤ C * Real.sqrt h + (2 * H) * (Real.sqrt T1 * Real.sqrt h) := by
                have he := mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
                nlinarith only [he]
              _ = _ := by ring
          have hrel : relativePosition P₀ P = (P.position - x s) +
              (x s - x b - (s - b) • v b) := by
            ext i
            simp only [relativePosition, P₀, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            dsimp only [b, s]
            ring
          have hrem := skeleton_position_remainder_le hv hkin hLip s b (sub_nonneg.mp hdelta.1)
          have hdeltaSq : (b - s) ^ 2 ≤ (2 * h) ^ 2 :=
            (sq_le_sq₀ hdelta.1 (by positivity)).mpr hdelta.2
          have hxb : PDE.vecEuclideanNorm (relativePosition P₀ P) ≤
              (C + 2 * H * Real.sqrt T1) * h ^ (3 / 2 : ℝ) := by
            rw [hrel]
            apply (PDE.vecEuclideanNorm_add_le _ _).trans
            calc
              _ ≤ C * h ^ (3 / 2 : ℝ) + H * (b - s) ^ 2 / 2 := add_le_add hy hrem
              _ ≤ C * h ^ (3 / 2 : ℝ) + H * (2 * h) ^ 2 / 2 :=
                add_le_add le_rfl (div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hdeltaSq hH) (by norm_num))
              _ = C * h ^ (3 / 2 : ℝ) + (2 * H) * h ^ 2 := by ring
              _ ≤ C * h ^ (3 / 2 : ℝ) + (2 * H) * (Real.sqrt T1 * h ^ (3 / 2 : ℝ)) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hthree (by positivity))
              _ = _ := by ring
          have hCW : C + 2 * H * Real.sqrt T1 < W := by dsimp only [C, L, W, barrierW]; linarith
          have hcube : W ≤ W ^ 3 := by
            have hsq : 1 ≤ W ^ 2 := by nlinarith only [hW2]
            nlinarith only [mul_nonneg hW.le (sub_nonneg.mpr hsq)]
          constructor
          · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
            exact hvbound.trans_lt (mul_lt_mul_of_pos_right hCW (Real.sqrt_pos.mpr hh))
          · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
            rw [sub_zero, propagation_block_radius_cube hh.le]
            exact hxb.trans_lt (mul_lt_mul_of_pos_right (hCW.trans_le hcube)
              (Real.rpow_pos_of_pos hh _))

        /- The Gaussian is nonpositive on the entire kinetic boundary of a source block. -/
      rcases hb with ht | hvface | ⟨hxface, _⟩
      · have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
        have hs := (gaussianBarrier_pos_quadratic hlam hh Lam H
          (barrierL d lam Lam H T1) ell tminus sblock hLam hell hbudget x v P hp).1
        have hW := two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
        rw [propagation_block_radius_sq hh.le] at ht
        change P.time = tminus + sblock + h - barrierW d lam Lam H T1 ^ 2 * h at ht
        have he : 4 * h ≤ barrierW d lam Lam H T1 ^ 2 * h := by
          have hw : 4 ≤ barrierW d lam Lam H T1 ^ 2 := by nlinarith only [hW]
          exact mul_le_mul_of_nonneg_right hw hh.le
        linarith only [ht, hs, he, hh]
      · exact (ne_of_lt hvball) hvface
      · exact (ne_of_lt hxball) hxface
    exact _h_xinl_0.trans
      (hnonneg P (hQO (mem_kineticBoundary_iff.mp hP).1))
  ·
    let L := (barrierL d lam Lam H T1)
    let S := {P : KineticPoint d | 0 < P.time - tminus - sblock ∧
      P.time - tminus - sblock ≤ h}
    have ht : Continuous (fun P : KineticPoint d => P.time - tminus - sblock) :=
      (continuous_time.sub continuous_const).sub continuous_const
    have hS : MeasurableSet S :=
      (isOpen_lt continuous_const ht).measurableSet.inter
        (isClosed_le ht continuous_const).measurableSet
    have hs := (ae_restrict_iff' hS).mp
      (gaussianBarrier_sign hlam hh Lam H L ell tminus sblock hLam hH hell A hA
        hx hv hkin hLip)
    let Q := backwardCylinder
      (⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ : KineticPoint d) R
    have hQ : MeasurableSet Q := (isOpen_backwardCylinder _ R hR).measurableSet
    filter_upwards [hs.filter_mono (ae_restrict_le (μ := volume) (s := Q)),
      ae_restrict_mem hQ] with P hsign hP
    by_cases hp : u P < gaussianBarrier lam Lam H h L ell tminus sblock x v P
    · have hc := subset_closure hP
      have hpositive : 0 < P.time - tminus - sblock := by
        by_contra hn
        exact (not_lt_of_ge (hinit P hc (le_of_not_gt hn))) hp
      have hupper := (closure_backwardCylinder_bounds
        (⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ : KineticPoint d)
        hR hc).2.1
      have hmem : P ∈ S := ⟨hpositive, by change P.time ≤ tminus + sblock + h at hupper
                                          linarith only [hupper]⟩
      have hnonpos := (hsign hmem).1.trans (hsign hmem).2
      rw [localizedSource, Set.indicator_of_mem (show P ∈ {Q | u Q <
        gaussianBarrier lam Lam H h L ell tminus sblock x v Q} from hp)]
      exact max_eq_right hnonpos
    · rw [localizedSource, Set.indicator_of_notMem (show P ∉ {Q | u Q <
        gaussianBarrier lam Lam H h L ell tminus sblock x v Q} from hp)]
      rfl

end HypoellipticAleksandrov.KineticAleksandrov.Holder
