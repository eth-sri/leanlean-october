module
public import DensityEnergyGM.SharpCountBudgets
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem gmTraceEnergyMargin_affine_length (σ P Q C t : ℝ)
    (hd : Q*σ-C ≠ 0) (j : Fin 3) (i : Fin 5) :
    gmTraceEnergyMargin σ (P/(Q*σ-C)) (t*(P/(Q*σ-C))) j i =
      ((2-gmTraceB j-gmTraceG j-gmTraceD j*gmEnergyR i)*3*P*(1-σ)-
        (gmTraceA j+gmTraceD j*gmEnergyV i)*(Q*σ-C)+
        ((4-2*gmTraceB j-gmTraceD j*gmEnergyW i)*σ-3+gmTraceB j-
          gmTraceD j*gmEnergyU i)*t*P)/(Q*σ-C) := by
  unfold gmTraceEnergyMargin
  field_simp
  ring

set_option hygiene false in
macro "pf_122" x1:term:max x2:term:max x3:term:max : tactic => `(tactic| (
  have hd : 0 < ($x1:term)*σ-$x2:term := by linarith
  apply gmTraceEnergyMargin_of_endpoints j i hx hx'
  · have he := gmTraceEnergyMargin_affine_length σ $x3:term $x1:term $x2:term 1 hd.ne' j i
    simp only [one_mul] at he
    rw [he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [gmTraceA,gmTraceB,gmTraceG,gmTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
      linarith
  · have he := gmTraceEnergyMargin_affine_length σ $x3:term $x1:term $x2:term (3/2) hd.ne' j i
    have hm : 3*($x3:term/(($x1:term)*σ-$x2:term))/2 = (3/2)*($x3:term/(($x1:term)*σ-$x2:term)) := by ring
    rw [hm,he]
    apply div_nonneg _ hd.le
    fin_cases j <;> fin_cases i <;>
      norm_num [gmTraceA,gmTraceB,gmTraceG,gmTraceD,gmEnergyU,gmEnergyV,gmEnergyW,gmEnergyR] <;>
      linarith))
section
variable {σ x : ℝ}
include σ x
/-- Every sharp-trace/five-energy monomial fits the entire unperturbed
row6 length rectangle, including both closed sigma joins. -/
theorem gmTraceEnergyMargin_row6
    (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038)
    (hx : 597962/(2187648*σ-772245) ≤ x)
    (hx' : x ≤ 3*(597962/(2187648*σ-772245))/2) (j : Fin 3) (i : Fin 5) :
    0 ≤ gmTraceEnergyMargin σ (597962/(2187648*σ-772245)) x j i := by pf_122 2187648 772245 597962

/-- Every sharp-trace/five-energy monomial fits the entire unperturbed
row7 length rectangle, including both closed sigma joins. -/
theorem gmTraceEnergyMargin_row7
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354)
    (hx : 16504356/(62198298*σ-22870785) ≤ x)
    (hx' : x ≤ 3*(16504356/(62198298*σ-22870785))/2) (j : Fin 3) (i : Fin 5) :
    0 ≤ gmTraceEnergyMargin σ (16504356/(62198298*σ-22870785)) x j i := by
  pm_494
  apply gmTraceEnergyMargin_of_endpoints j i hx hx'
  · have he := gmTraceEnergyMargin_affine_length σ 16504356 62198298 22870785 1 hd.ne' j i
    pm_429
    pm_4038
  · have he := gmTraceEnergyMargin_affine_length σ 16504356 62198298 22870785 (3/2) hd.ne' j i
    have hm : 3*(16504356/(62198298*σ-22870785))/2 = (3/2)*(16504356/(62198298*σ-22870785)) := by ring
    rw [hm,he]
    apply div_nonneg _ hd.le
    pm_4038

/-- Every sharp-trace/five-energy monomial fits the entire unperturbed
row8 length rectangle, including both closed sigma joins. -/
theorem gmTraceEnergyMargin_row8
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8)
    (hx : 2172/(8226*σ-3045) ≤ x)
    (hx' : x ≤ 3*(2172/(8226*σ-3045))/2) (j : Fin 3) (i : Fin 5) :
    0 ≤ gmTraceEnergyMargin σ (2172/(8226*σ-3045)) x j i := by pf_122 8226 3045 2172
end

end Montgomery.RationalMoment
