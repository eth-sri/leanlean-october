module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedCancellation
public import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRegion
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

def unramifiedMarked (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹ (coordK Q eta x w)
    (-coordD Q eta v x+coordW Q v w*coordR Q A x z) 1

lemma unramifiedMarked_selected_error (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 ∧
    ‖star eta*(Q:ℂ)^x‖*‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 := by
  pm_3932
  pm_3933
  have hR : ‖R‖≤Q^(4-6*x.re-6*z.re) := coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖=Q^(-6*z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖≤Q^(-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : ‖W‖≤1 := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : ‖K‖≤Q^(1-x.re-w.re) := coordK_norm_le Q hQ1 eta x w heta
  pm_3935
  pm_8180 hRh R hR.trans
  have hVh : ‖V‖≤1/2 := by rw [hV];exact rpow_le_half Q _ hQ (by linarith)
  pm_8180 hDh D hD.trans
  pm_3934
  have hprod (a b aa bb : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (he : aa+bb≤0) : a*b≤1 := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  pm_7576 hKV K V hK hV.le
  pm_7576 hBR B R hB hR
  have hKV' : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
    calc
      _≤Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _=_ := by rw [←Real.rpow_add hQ0];congr 1;ring
  have hBKV : ‖B‖*(‖K‖*‖V‖)≤1 := hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  pm_6640 hE
  change ‖unramifiedMarked Q A eta v x w z+D‖≤_ at hE
  have hE' : ‖unramifiedMarked Q A eta v x w z+D‖≤24*‖R‖+4*(‖K‖*‖V‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  · change ‖unramifiedMarked Q A eta v x w z+D‖≤28
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change ‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤28
    nlinarith

end SevenEighths.ProbeEuler
end

end OAI
