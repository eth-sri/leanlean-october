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

/-- Bound the correction by comparing the exponents of its terms. The upper
bound `Q^b` for the variable `W` allows for growth in the first region. -/
private theorem unramifiedClosed_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {b e t : ℝ} (hb : 0 ≤ b) (hw : -w.re ≤ b)
    (hVh : -6*z.re ≤ -(1/2)) (hRh : 4-6*x.re-6*z.re ≤ -(1/2)) (hDh : -x.re ≤ -(1/2))
    (hRE : 4-6*x.re-6*z.re+b ≤ e) (hKE : 1-x.re-w.re-6*z.re ≤ e)
    (hET : e+b ≤ t) (hDV : -x.re-6*z.re ≤ t) (hVW : -6*z.re-w.re ≤ t)
    (hDW : -x.re-w.re ≤ t) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q^t := by
  have hQ₀ : 0 < Q := by linarith
  have hQ₁ : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^b
  let E := Q^e
  let T := Q^t
  have hV : ‖V‖ ≤ Q^(-6*z.re) := (coordV_norm Q hQ₀ z).le
  have hR := coordR_norm_le Q hQ₀ A x z hA
  have hD := coordD_norm_le Q hQ₀ eta v x heta hv
  have hW := coordW_norm_le Q hQ₀ v w hv
  have hK := coordK_norm_le Q hQ₁ eta x w heta
  have hV₁ := hV.trans (rpow_le_half Q _ hQ hVh)
  have hR₁ := hR.trans (rpow_le_half Q _ hQ hRh)
  have hD₁ := hD.trans (rpow_le_half Q _ hQ hDh)
  have hQinv : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ₀, ← one_div]
    exact (div_le_one hQ₀).mpr hQ₁
  have prod_bound {a c u v r : ℝ} (ha : a ≤ Q^u) (hc : c ≤ Q^v)
      (hc₀ : 0 ≤ c) (hr : u+v ≤ r) : a*c ≤ Q^r := by
    refine (mul_le_mul ha hc hc₀ (by positivity)).trans ?_
    rw [← Real.rpow_add hQ₀]
    exact Real.rpow_le_rpow_of_exponent_le hQ₁ hr
  have hRL : ‖R‖*L ≤ E := prod_bound hR le_rfl (by positivity) hRE
  have hKV : ‖K‖*‖V‖ ≤ E := prod_bound hK hV (norm_nonneg _) (by linarith)
  have hL : 1 ≤ L := Real.one_le_rpow hQ₁ hb
  have hWL : ‖W‖ ≤ L := hW.trans (Real.rpow_le_rpow_of_exponent_le hQ₁ hw)
  have hRW : ‖R‖*(1+‖W‖) ≤ 2*E := by
    calc
      _ ≤ ‖R‖*(2*L) := by gcongr; linarith
      _ ≤ _ := by linarith only [hRL, show ‖R‖*(2*L) = 2*(‖R‖*L) by ring]
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖ ≤ 28*E := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hR₁ hV₁ hQinv hD₁
    dsimp only [P]
    linarith only [h, hRW, hKV]
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ (2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [(prod_bound le_rfl le_rfl (by positivity) hET)]
  have h₁ : ‖D‖*‖V‖ ≤ T := prod_bound hD hV (norm_nonneg _) (by linarith)
  have h₂ : ‖V‖*‖W‖ ≤ T := prod_bound hV hW (norm_nonneg _) (by linarith)
  have h₃ : ‖D‖*‖W‖ ≤ T := prod_bound hD hW (norm_nonneg _) (by linarith)
  have h₄ : ‖D‖*‖V‖*‖W‖ ≤ T := by
    rw [mul_right_comm]
    exact (mul_le_of_le_one_right (by positivity) (by linarith only [hV₁])).trans h₃
  change ‖ProbeLocal.continuedCorrection V W D P - 1‖ ≤ 240*T
  nlinarith only [ProbeLocal.continuedCorrection_defect_bound V W D P hV₁ hD₁, h₁, h₂, h₃, h₄, hWE, show 0 ≤ T by positivity]

theorem unramifiedClosed_second_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(363/200:ℝ)) := by
  apply unramifiedClosed_bound Q A eta v x w z hQ hA heta hv (b := 0) (e := -(363/200)) <;> linarith

theorem unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  apply unramifiedClosed_bound Q A eta v x w z hQ hA heta hv (b := 0) (e := -(17/10)) <;> linarith

theorem unramifiedClosed_first_neighborhood_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have h₁ := min_le_left eps (1/50:ℝ)
  have h₂ := min_le_right eps (1/50:ℝ)
  apply unramifiedClosed_bound Q A eta v x w z hQ hA heta hv (b := 3/200) (e := -(26/25)) <;> linarith

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  exact unramifiedClosed_first_neighborhood_bound Q A eta v x w z eps hQ hA heta hv heps
    (by linarith) (by linarith) (by linarith) hxw

end SevenEighths.ProbeEuler
end

end OAI
