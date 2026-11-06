module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralCancellation
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma central_unramified_error_weights (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    let L := Q^(6*e)
    let E := unramifiedMarked Q A eta v x w z+coordD Q eta v x
    L^2*‖coordV Q z‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖coordD Q eta v x‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖E‖≤28*Q^(-(51/100:ℝ)) ∧
    L*‖star eta*(Q:ℂ)^x‖*‖E‖≤28*Q^(-(51/100:ℝ)) := by
  dsimp only
  pm_3932
  pm_3933
  let L : ℝ := Q^(6*e)
  have hL : 1≤L := Real.one_le_rpow hQ1 (by positivity)
  have hL0 : 0≤L := by positivity
  have hR := coordR_norm_le Q hQ0 A x z hA
  have hV := coordV_norm Q hQ0 z
  have hD := coordD_norm_le Q hQ0 eta v x heta hv
  have hK := coordK_norm_le Q hQ1 eta x w heta
  have hW : ‖W‖≤L := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by grind))
  pm_3935
  pm_8179 hRh R hR.trans
  pm_8179 hVh V hV.le.trans
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by rw [hx];linarith))
  pm_3934
  have hE : ‖unramifiedMarked Q A eta v x w z+D‖≤24*L*‖R‖+4*‖K‖*‖V‖ := by
    pm_6640 hh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (show 1+‖W‖≤2*L by linarith) (norm_nonneg R)]
  have weighted (k r : ℝ) (N : ℝ) (hN : N≤Q^r) (hexp : k+r≤-(51/100:ℝ)) :
      Q^k*N≤Q^(-(51/100:ℝ)) := by
    calc
      _ ≤ Q^k*Q^r := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hQ0.le _)
      _ = Q^(k+r) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hLR : L^3*‖R‖≤Q^(-(51/100:ℝ)) := by
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    pm_5398 hR hx
  have hLKV : L^2*(‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hkv : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
      calc
        _ ≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hkv (by rw [hx,hw,hz];linarith)
  have hLBR : L^2*(‖B‖*‖R‖)≤Q^(-(51/100:ℝ)) := by
    have hbr : ‖B‖*‖R‖≤Q^(4-5*x.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(4-6*x.re-6*z.re) := mul_le_mul hB hR (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    pm_5398 hbr hx
  have hLBKV : L*(‖B‖*‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hbkv : ‖B‖*‖K‖*‖V‖≤Q^(1-w.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(1-x.re-w.re)*Q^(-6*z.re) := by
          gcongr
          exact hV.le
        _ = _ := by rw [←Real.rpow_add hQ0,←Real.rpow_add hQ0];congr 1;ring
    pm_5398 hbkv hw
  pm_4898
  pm_5336 V hV.le hz
  pm_5336 D hD hx
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
    change L^2*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLR,hLKV]
  · have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hL0 (norm_nonneg B))
    change L*‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLBR,hLBKV]

end SevenEighths.ProbeEuler

end OAI
