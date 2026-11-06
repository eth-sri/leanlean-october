module
public import DensityEnergyGM.SharpCountAlgebra
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def gmEnergyU : Fin 5 → ℝ := ![4,4,5/2,40/31,40/19]
def gmEnergyV : Fin 5 → ℝ := ![0,2,9/8,9/31,17/19]
def gmEnergyW : Fin 5 → ℝ := ![-4,-8,-5,-80/31,-80/19]
def gmEnergyR : Fin 5 → ℝ := ![1,0,3/2,84/31,36/19]
def gmTraceA : Fin 3 → ℝ := ![1,4/5,9/20]
def gmTraceB : Fin 3 → ℝ := ![-1,-4/5,-1/5]
def gmTraceG : Fin 3 → ℝ := ![0,1,1]
def gmTraceD : Fin 3 → ℝ := ![1/2,1/4,1/4]

def gmTraceEnergyMargin (σ a x : ℝ) (j : Fin 3) (i : Fin 5) : ℝ :=
  (2-gmTraceB j-gmTraceG j-gmTraceD j*gmEnergyR i)*(3*a*(1-σ))-
    gmTraceA j-gmTraceD j*gmEnergyV i+
    ((4-2*gmTraceB j-gmTraceD j*gmEnergyW i)*σ-3+gmTraceB j-
      gmTraceD j*gmEnergyU i)*x

theorem gmTraceEnergy_sublinearity (j : Fin 3) (i : Fin 5) :
    gmTraceG j+gmTraceD j*gmEnergyR i ≤ 7/4 := by
  pm_6346 gmTraceG gmTraceD

theorem gmTraceEnergyMargin_of_endpoints {σ a x : ℝ} (j : Fin 3) (i : Fin 5)
    (hx : a ≤ x) (hx' : x ≤ 3*a/2)
    (hlo : 0 ≤ gmTraceEnergyMargin σ a a j i)
    (hhi : 0 ≤ gmTraceEnergyMargin σ a (3*a/2) j i) :
    0 ≤ gmTraceEnergyMargin σ a x j i := by pm_4037 gmTraceB gmTraceD gmTraceEnergyMargin

theorem gmTraceEnergy_length_slope_nonneg {σ : ℝ} (hσ : 4/5 ≤ σ)
    (j : Fin 3) (i : Fin 5) :
    0 ≤ (4-2*gmTraceB j-gmTraceD j*gmEnergyW i)*σ-3+gmTraceB j-
      gmTraceD j*gmEnergyU i := by
  pm_4038

theorem gmTraceEnergyMargin_mono_length {σ a x y : ℝ} (hσ : 4/5 ≤ σ)
    (hxy : x ≤ y) (j : Fin 3) (i : Fin 5) :
    gmTraceEnergyMargin σ a x j i ≤ gmTraceEnergyMargin σ a y j i := by
  pm_5255 gmTraceEnergy_length_slope_nonneg gmTraceEnergyMargin

end Montgomery.RationalMoment
