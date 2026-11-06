module

public import ImprovedExponents.Optimum.PerCCrossing
public import ThreeSumApsp.TacticsShort

@[expose] public section

/-!
# The supremum of the savings for a fixed `c`

Fix `c > 10` and a thinness constant `A > 0`. The savings `tupleSaving c θ σ ε` of the admissible
parameters `(θ, σ, ε)` have the least upper bound `savingF A (Gam c) = R(Γ) Γ/2`
(`isLUB_tupleSaving`), and the bound is not attained:

* every admissible tuple has `tupleSaving c θ σ ε < savingF A (Gam c)` (`tupleSaving_lt_savingF`).
  With `a = γX(c, θ)`, `u = 2σ - 1` and `v = min(u, min(a, σ - q) - u) > 0` one has `2v ≤ a` and
  `3v ≤ u + 2((1 - u)/2 - q) = 1 - 2q`, so `2v ≤ μ := min(a, γ_Q(θ)) ≤ Γ`, and
  `ε v < R(a) v ≤ R(μ) μ/2 = F(μ) ≤ F(Γ)`;
* every `s < savingF A (Gam c)` is exceeded (`exists_tupleSaving_gt`): at the crossing point `θ*`
  and `σ = 1/2 + Γ/4` the saving is `ε Γ/2` (`tupleSaving_crossing`), and `ε` may be any number
  below `R(Γ)`.
-/

namespace ImprovedExponents

open ThreeSumApsp

variable {A c θ σ ε : ℝ}

/-- At the crossing point `θ*` and the balanced prime size `σ = 1/2 + Γ/4`, the saving is
`ε Γ/2`. -/
theorem tupleSaving_crossing (hX : gammaX c θ = Gam c) (hQ : gammaQ θ = Gam c) (ε : ℝ) :
    tupleSaving c θ (1 / 2 + Gam c / 4) ε = ε * (Gam c / 2) := by
  have hq := gammaQ_eq_iff.1 hQ
  have e1 : 1 / 2 + Gam c / 4 - qOf θ = Gam c := by
    rw [hq]
    ring
  have e2 : 2 * (1 / 2 + Gam c / 4) - 1 = Gam c / 2 := by ring
  have e3 : Gam c - Gam c / 2 = Gam c / 2 := by ring
  rw [tupleSaving, effGamma, hX, e1, e2, min_self, e3, min_self]

/-- **The bound `R(Γ) Γ/2` is approached**: every smaller number is exceeded by the saving of an
admissible tuple. -/
theorem exists_tupleSaving_gt (hc : 10 < c) (hA : 0 < A) {s : ℝ}
    (hs : s < savingF A (Gam c)) :
    ∃ θ σ ε, AdmissibleX A c θ σ ε ∧ s < tupleSaving c θ σ ε := by
  obtain ⟨θ, hθ, hX, hQ⟩ := exists_crossing_eq_Gam hc
  have hΓ := Gam_pos hc
  have hΓ' := Gam_lt_two_thirds hc
  have hR := thinR_pos hA hΓ.le
  have hs' : s / (Gam c / 2) < thinR A (Gam c) := by
    rw [div_lt_iff₀ tac_linarith]
    unfold savingF at hs
    linarith
  obtain ⟨ε, hε1, hε2⟩ := exists_between (max_lt hs' hR)
  have hε0 : 0 < ε := (le_max_right _ _).trans_lt hε1
  have hεs : s / (Gam c / 2) < ε := (le_max_left _ _).trans_lt hε1
  refine ⟨θ, 1 / 2 + Gam c / 4, ε, ⟨hc, hθ.1, hθ.2, by linarith, by linarith, hε0, ?_⟩, ?_⟩
  · rwa [hX]
  · rw [tupleSaving_crossing hX hQ]
    rwa [div_lt_iff₀ tac_linarith] at hεs

end ImprovedExponents