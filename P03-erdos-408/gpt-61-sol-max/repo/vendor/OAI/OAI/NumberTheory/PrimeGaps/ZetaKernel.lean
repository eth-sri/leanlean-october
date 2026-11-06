module

public import OAI.NumberTheory.PrimeGaps.BoxMeans
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

noncomputable def frequencyW (u : ℝ) : ℂ := 1+Complex.I*(u:ℂ)

@[simp] theorem frequencyW_re (u : ℝ) : (frequencyW u).re=1 := by simp [frequencyW]

end LargePrimeGaps

end OAI
