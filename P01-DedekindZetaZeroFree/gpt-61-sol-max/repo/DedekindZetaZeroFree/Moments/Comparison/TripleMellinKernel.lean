module

public import Mathlib

public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section


namespace DedekindZetaZeroFree

noncomputable section

def comparisonA : ℝ := 9 / 10

def comparisonB : ℝ := 133 / 1000

def comparisonH₀ : ℝ := 1 / 10

def comparisonX (Z : ℝ)  := Z ^ comparisonA

def comparisonY (Z : ℝ)  := Z ^ comparisonB




def comparisonRealPower (Z : ℝ) (s : ℂ)  :=
  Complex.exp (s * (Real.log Z : ℂ))









end
end DedekindZetaZeroFree
