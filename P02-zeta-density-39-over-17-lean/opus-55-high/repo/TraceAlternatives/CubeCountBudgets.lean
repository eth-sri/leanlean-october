module
public import DensityEnergyGM.SharpCountEnergyExpansion
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def cubeTraceA : Fin 2 → ℝ := ![1,1/3]
def cubeTraceB : Fin 2 → ℝ := ![-1,0]
def cubeTraceG : Fin 2 → ℝ := ![2/3,2/3]
def cubeTraceD : Fin 2 → ℝ := ![1/3,1/3]

def cubeTraceEnergyMargin (σ a x : ℝ) (j : Fin 2) (i : Fin 5) : ℝ :=
  (2-cubeTraceB j-cubeTraceG j-cubeTraceD j*gmEnergyR i)*(3*a*(1-σ))-
    cubeTraceA j-cubeTraceD j*gmEnergyV i+
    ((4-2*cubeTraceB j-cubeTraceD j*gmEnergyW i)*σ-3+cubeTraceB j-
      cubeTraceD j*gmEnergyU i)*x

theorem cubeTraceEnergy_sublinearity (j : Fin 2) (i : Fin 5) :
    cubeTraceG j+cubeTraceD j*gmEnergyR i ≤ 7/4 := by
  pm_6346 cubeTraceG cubeTraceD

theorem cubeTraceEnergyMargin_of_endpoints {σ a x : ℝ} (j : Fin 2) (i : Fin 5)
    (hx : a ≤ x) (hx' : x ≤ 3*a/2)
    (hlo : 0 ≤ cubeTraceEnergyMargin σ a a j i)
    (hhi : 0 ≤ cubeTraceEnergyMargin σ a (3*a/2) j i) :
    0 ≤ cubeTraceEnergyMargin σ a x j i := by pm_4037 cubeTraceB cubeTraceD cubeTraceEnergyMargin

theorem cubeTraceEnergy_length_slope_nonneg {σ : ℝ} (hσ : 13/16 ≤ σ)
    (j : Fin 2) (i : Fin 5) :
    0 ≤ (4-2*cubeTraceB j-cubeTraceD j*gmEnergyW i)*σ-3+cubeTraceB j-
      cubeTraceD j*gmEnergyU i := by
  pm_2736

theorem cubeTraceEnergyMargin_mono_length {σ a x y : ℝ} (hσ : 13/16 ≤ σ)
    (hxy : x ≤ y) (j : Fin 2) (i : Fin 5) :
    cubeTraceEnergyMargin σ a x j i ≤ cubeTraceEnergyMargin σ a y j i := by
  pm_5255 cubeTraceEnergy_length_slope_nonneg cubeTraceEnergyMargin

end Montgomery.RationalMoment
