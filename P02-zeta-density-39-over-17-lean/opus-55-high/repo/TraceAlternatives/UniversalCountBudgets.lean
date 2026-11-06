module
public import DensityEnergyGM.SharpCountEnergyExpansion
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def universalTraceA : Fin 3 → ℝ := ![1,1/2,9/16]
def universalTraceB : Fin 3 → ℝ := ![-1,-1/3,-1/2]
def universalTraceG : Fin 3 → ℝ := ![0,1,19/12]
def universalTraceD : Fin 3 → ℝ := ![1/2,1/4,5/48]

def universalTraceEnergyMargin (σ a x : ℝ) (j : Fin 3) (i : Fin 5) : ℝ :=
  (2-universalTraceB j-universalTraceG j-universalTraceD j*gmEnergyR i)*(3*a*(1-σ))-
    universalTraceA j-universalTraceD j*gmEnergyV i+
    ((4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
      universalTraceD j*gmEnergyU i)*x

theorem universalTraceEnergy_sublinearity (j : Fin 3) (i : Fin 5) :
    universalTraceG j+universalTraceD j*gmEnergyR i ≤ 15/8 := by
  pm_6346 universalTraceG universalTraceD

theorem universalTraceEnergyMargin_of_endpoints {σ a x : ℝ} (j : Fin 3) (i : Fin 5)
    (hx : a ≤ x) (hx' : x ≤ 3*a/2)
    (hlo : 0 ≤ universalTraceEnergyMargin σ a a j i)
    (hhi : 0 ≤ universalTraceEnergyMargin σ a (3*a/2) j i) :
    0 ≤ universalTraceEnergyMargin σ a x j i := by pm_4037 universalTraceB universalTraceD universalTraceEnergyMargin

theorem universalTraceEnergy_length_slope_nonneg {σ : ℝ} (hσ : 7873/9370 ≤ σ)
    (j : Fin 3) (i : Fin 5) :
    0 ≤ (4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
      universalTraceD j*gmEnergyU i := by
  pm_2729

theorem universalTraceEnergyMargin_mono_length {σ a x y : ℝ} (hσ : 7873/9370 ≤ σ)
    (hxy : x ≤ y) (j : Fin 3) (i : Fin 5) :
    universalTraceEnergyMargin σ a x j i ≤ universalTraceEnergyMargin σ a y j i := by
  pm_5255 universalTraceEnergy_length_slope_nonneg universalTraceEnergyMargin

end Montgomery.RationalMoment
