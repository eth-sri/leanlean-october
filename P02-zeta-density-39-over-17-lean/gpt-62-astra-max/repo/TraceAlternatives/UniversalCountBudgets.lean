module
public import DensityEnergyGM.SharpCountEnergyExpansion

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
  fin_cases j <;> fin_cases i <;>
    norm_num [universalTraceG,universalTraceD,gmEnergyR]




end Montgomery.RationalMoment
