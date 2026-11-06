module
public import DensityEnergyGM.SharpCountAlgebra

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

def gmEnergyU : Fin 5 → ℝ := ![4,4,5/2,40/31,40/19]
def gmEnergyV : Fin 5 → ℝ := ![0,2,9/8,9/31,17/19]
def gmEnergyW : Fin 5 → ℝ := ![-4,-8,-5,-80/31,-80/19]
def gmEnergyR : Fin 5 → ℝ := ![1,0,3/2,84/31,36/19]






