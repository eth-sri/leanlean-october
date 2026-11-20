module
public import OAI.NumberTheory.DirichletL.Detector.EulerCoordinates

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

/-- A single local Euler-factor bound, with the product estimates expressed
as linear inequalities on the real parts. `s` pays for possible growth of `W`. -/
theorem unramifiedClosed_bound_of_exponents (Q : ℝ) (A eta v x w z : ℂ) (s t : ℝ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hs : 0 ≤ s) (hw : -w.re ≤ s) (ht : t ≤ -(1/2))
    (hx : 1/2 ≤ x.re) (hz : 1/2 ≤ 6*z.re)
    (hR : 4-6*x.re-6*z.re+2*s ≤ t) (hK : 1-x.re-w.re-6*z.re+s ≤ t)
    (hDV : -x.re-6*z.re ≤ t) (hVW : -6*z.re-w.re ≤ t) (hDW : -x.re-w.re ≤ t) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q^t := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have mono {u w : ℝ} (h : u ≤ w) : Q^u ≤ Q^w := Real.rpow_le_rpow_of_exponent_le hQ1 h
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^s
  let E := Q^(t-s)
  let T := Q^t
  have hL : 1 ≤ L := Real.one_le_rpow hQ1 hs
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have vB := (coordV_norm Q hQ0 z).le
  have rB := coordR_norm_le Q hQ0 A x z hA
  have wB := coordW_norm_le Q hQ0 v w hv
  have dB := coordD_norm_le Q hQ0 eta v x heta hv
  have kB := coordK_norm_le Q hQ1 eta x w heta
  have prod {a b u v c : ℝ} (hb : 0 ≤ b) (ha : a ≤ Q^u) (hb' : b ≤ Q^v)
      (hc : u+v ≤ c) : a*b ≤ Q^c := by
    exact (mul_le_mul ha hb' hb (Real.rpow_nonneg hQ0.le _)).trans
      ((Real.rpow_add hQ0 _ _).symm.le.trans (mono hc))
  have vH : ‖V‖ ≤ 1/2 := vB.trans (rpow_le_half Q _ hQ (by linarith))
  have rH : ‖R‖ ≤ 1/2 := rB.trans (rpow_le_half Q _ hQ (by linarith))
  have dH : ‖D‖ ≤ 1/2 := dB.trans (rpow_le_half Q _ hQ (by linarith))
  have qiH : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  have wL : ‖W‖ ≤ L := wB.trans (mono hw)
  have rL : ‖R‖*L ≤ E := prod (Real.rpow_nonneg hQ0.le _) rB le_rfl (by linarith)
  have kV : ‖K‖*‖V‖ ≤ E := prod (norm_nonneg _) kB vB (by linarith)
  have rW : ‖R‖*(1+‖W‖) ≤ 2*E := by
    calc
      _ ≤ ‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ ≤ _ := by nlinarith only [rL]
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖ ≤ 28*E := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D rH vH qiH dH
    dsimp only [P]
    linarith only [h,rW,kV]
  have hEL : E*L ≤ T := prod (Real.rpow_nonneg hQ0.le _) le_rfl le_rfl (by linarith)
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ (2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [hEL]
  have dV : ‖D‖*‖V‖ ≤ T := prod (norm_nonneg _) dB vB (by linarith only [hDV])
  have vW : ‖V‖*‖W‖ ≤ T := prod (norm_nonneg _) vB wB (by linarith only [hVW])
  have dW : ‖D‖*‖W‖ ≤ T := prod (norm_nonneg _) dB wB (by linarith only [hDW])
  have dVW : ‖D‖*‖V‖*‖W‖ ≤ T := by
    rw [mul_right_comm]
    exact (mul_le_of_le_one_right (by positivity) (by linarith only [vH])).trans dW
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P vH dH
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  linarith only [h,hWE,dV,vW,dW,dVW,hT]

theorem unramifiedClosed_second_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(363/200:ℝ)) := by
  apply unramifiedClosed_bound_of_exponents Q A eta v x w z 0 _ hQ hA heta hv
  all_goals linarith

end SevenEighths.ProbeEuler
end

end OAI
