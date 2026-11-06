module

public import Erdos821.P3Edge.PowRho
public import Erdos821.Leaves.Damped

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

/-- Small fresh-label counts against `q` damping, uniformly in the
remaining-zero count. This is the small-group analogue of
`eq:promotion-count`, with fixed `ell` in place of `a ≤ ell+m`. -/
lemma small_count_damp (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, ell ≤ Y →
      (Y : ℝ) ^ ell * q ^ ((((Y - ell : ℕ)) : ℝ) / 2) ≤ C := by
  classical
  have hsq0 := Real.sqrt_pos.mpr hq0
  have hsq1 : Real.sqrt q < 1 := by
    have h := Real.sqrt_lt_sqrt hq0.le hq1
    simpa using h
  obtain ⟨C₀, hC₀pos, hC₀⟩ := pow_mul_rho_bound (Real.sqrt q) hsq0 hsq1 ell
  refine ⟨C₀ / (Real.sqrt q) ^ ell, by positivity, fun Y hY => ?_⟩
  have hsq :=
    Erdos821.GraphLemmas.sqrt_pow_eq q hq0 (Y - ell)
  have hnum := hC₀ ell (le_refl _) Y
  have hpow : (Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell
      = (Real.sqrt q) ^ Y := by
    have hY2 := Nat.sub_add_cancel hY
    calc (Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell
        = (Real.sqrt q) ^ ((Y - ell) + ell) := by ring
      _ = (Real.sqrt q) ^ Y := by simp_all
  have hfin : (Y : ℝ) ^ ell * (Real.sqrt q) ^ (Y - ell) ≤ C₀ / (Real.sqrt q) ^ ell := by
    rw [le_div_iff₀ (by positivity)]
    have heq : (Y : ℝ) ^ ell * (Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell
        = (Y : ℝ) ^ ell * (Real.sqrt q) ^ Y := by
      calc _ = (Y : ℝ) ^ ell * ((Real.sqrt q) ^ (Y - ell) * (Real.sqrt q) ^ ell) := by
              ring
        _ = _ := by simp_all
    rw [heq]
    exact hnum
  simp_all

end Erdos821.P3Edge
