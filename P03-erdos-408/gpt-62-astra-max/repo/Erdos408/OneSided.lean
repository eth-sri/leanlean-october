module

public import Erdos408.OneSided.Cauchy
public import Erdos408.OneSided.Major
public import Erdos408.OneSided.Replacement

/-!
# The one-sided Type II estimate

A proof of `OneSidedTypeII` (PD Theorem 3.1, extended), following PD §§3–5 as restated in
`blueprint/one_sided_type_ii.md`. The exponents are fixed in terms of `(D_*, C)`:
`K₀ = bandThreshold`, `A₀ = arcExp`, `B = freqExp` and `A = twistExp`.

* `cauchy_reduction` (interface 1): Cauchy's inequality reduces the sum to the Cauchy
  squares `Q_Y`, `Y = 2^j`, and a bound `Q_Y ≪ X Y L^{-D₁}` suffices.
* `eventually_replacement` (interface 2): for `K ≥ K₀`, `Q_Y` differs from the major sum
  `Q_Y^maj` by `O(X Y L^{-D₁ - 1})`.
* `eventually_majorSquare` (interface 3): under P4 and (G), `Q_Y^maj = O(X Y L^{-D₁ - 1})`.
-/

@[expose] public section

namespace Erdos408

open Filter OneSided

/-- The extended one-sided marked Type II estimate. -/
theorem oneSidedTypeII : OneSidedTypeII := by
  intro q C Dstar CX alo ahi hq hq₁ hC hD hCX halo _ hahi
  refine ⟨bandThreshold Dstar C, arcExp Dstar C, freqExp Dstar C, twistExp Dstar C,
    fun K hK g c₄ cG hg => ?_⟩
  obtain ⟨C₂, h₂⟩ := eventually_replacement  hC hD hCX halo hahi hK hg
  obtain ⟨C₃, h₃⟩ := eventually_majorSquare (K := K) (Dstar := Dstar)
    hC hD hCX halo hahi
  obtain ⟨C₁, h₁⟩ := cauchy_reduction hq hq₁ halo hahi
    ((one_le_bandThreshold hD hC).trans hK) hg (|C₂| + |C₃|)
  refine ⟨C₁, ?_⟩
  filter_upwards [h₁, h₂, h₃, eventually_ge_atTop (Real.exp 1)] with x h₁ h₂ h₃ hx
  intro a γ Hm Hn F α β ha hgap hγ hHm hHn hX₁ hX₂ hF hFinv hα hP4 hβ hG
  let d : Data K := ⟨a, γ, Hm, Hn, F, α, β⟩
  have hd : Admissible C CX alo ahi g x d :=
    ⟨ha, hgap, hγ, hHm, hHn, hX₁, hX₂, hF, hFinv, hα, hβ⟩
  have hL : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  have hX := lt_of_lt_of_le (div_pos ((Real.exp_pos 1).trans_le hx) (by linarith)) hd.X_ge
  refine h₁ d hd fun j => ?_
  -- `‖Q_Y‖ ≤ ‖Q_Y - Q_Y^maj‖ + ‖Q_Y^maj‖`
  calc _
      = ‖(cauchySquare x d (2 ^ j) - majorSquare (arcExp Dstar C) x d (2 ^ j)) +
          majorSquare (arcExp Dstar C) x d (2 ^ j)‖ := by simp
    _ ≤ (C₂ + C₃) * (d.X * 2 ^ j * Real.log x ^ (-(squarePrec Dstar + 1))) := ((norm_add_le _ _).trans (add_le_add (h₂ d hd j) (h₃ d hd hP4 hG j))).trans_eq (by ring)
    _ ≤ (|C₂| + |C₃|) * (d.X * 2 ^ j * Real.log x ^ (-(squarePrec Dstar + 1))) := by
        gcongr <;> exact le_abs_self _
    _ ≤ (|C₂| + |C₃|) * (d.X * 2 ^ j * Real.log x ^ (-squarePrec Dstar)) := by
        gcongr
        linarith
    _ = _ := by ring

end Erdos408
