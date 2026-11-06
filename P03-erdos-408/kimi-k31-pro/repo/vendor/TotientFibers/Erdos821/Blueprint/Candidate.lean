module

public import Erdos821.Blueprint.Classical
public import Mathlib.Data.Nat.Squarefree

/-! P7: geometric slot lists, their literal coefficient and uniform candidate bounds. -/

@[expose] public section

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint
open Analytic

structure BandData where
  geometry : Geometry
  groups : ℝ → PrimeGroups
  r₀ : ℕ
  c₁ : ℝ
  c₂ : ℝ
  s' : ℝ
  ratio : ℝ
  last : ℝ → ℕ



end Erdos821.Blueprint
