module
public import TraceAlternatives.CubeCountBudgets
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem cubeTraceEnergyMargin_affine_length (σ P Q C t : ℝ)
    (hd : Q*σ-C ≠ 0) (j : Fin 2) (i : Fin 5) :
    cubeTraceEnergyMargin σ (P/(Q*σ-C)) (t*(P/(Q*σ-C))) j i =
      ((2-cubeTraceB j-cubeTraceG j-cubeTraceD j*gmEnergyR i)*3*P*(1-σ)-
        (cubeTraceA j+cubeTraceD j*gmEnergyV i)*(Q*σ-C)+
        ((4-2*cubeTraceB j-cubeTraceD j*gmEnergyW i)*σ-3+cubeTraceB j-
          cubeTraceD j*gmEnergyU i)*t*P)/(Q*σ-C) := by
  unfold cubeTraceEnergyMargin
  field_simp
  ring

/-- Every sharp-trace/five-energy monomial fits the entire unperturbed
row3 length rectangle, including both closed sigma joins. -/
theorem cubeTraceEnergyMargin_row3 {σ x : ℝ}
    (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370)
    (hx : 31544/(107010*σ-33609) ≤ x)
    (hx' : x ≤ 3*(31544/(107010*σ-33609))/2) (j : Fin 2) (i : Fin 5) :
    0 ≤ cubeTraceEnergyMargin σ (31544/(107010*σ-33609)) x j i := by
  pm_493
  apply cubeTraceEnergyMargin_of_endpoints j i hx hx'
  · have he := cubeTraceEnergyMargin_affine_length σ 31544 107010 33609 1 hd.ne' j i
    pm_429
    pm_2736
  · have he := cubeTraceEnergyMargin_affine_length σ 31544 107010 33609 (3/2) hd.ne' j i
    have hm : 3*(31544/(107010*σ-33609))/2 = (3/2)*(31544/(107010*σ-33609)) := by ring
    rw [hm,he]
    apply div_nonneg _ hd.le
    pm_2736

end Montgomery.RationalMoment
