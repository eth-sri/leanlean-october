module

public import FixedPointTheorems.brouwer
public import PottsDiscontinuity.Bethe.RatioAnySign
public import PottsDiscontinuity.SixVertex.Cor34FinalExistence

/-!
# Theorem 1.3 ratio limit at the critical six-vertex parameter

The assembly uses Theorem 2.3 to select the two symmetric Bethe families,
the Fourier eigenvalue-ratio limit for both parities (`Bethe/Ratio*`), and the
proved Corollary 3.4 analytic-family identifications.
-/

public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open Bethe BetheAnsatz SixVertex

/-- Theorem 1.3, equation (1.7), along the tail of the subsequence `N ∈ 4ℕ`.
The finite-size Bethe/Perron-root identification uses the proved Corollary 3.4
endpoint-family theorem. -/
theorem apply_17_at_critical_c
    (q : ℝ) (hq : 4 < q) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : ℕ, ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q / 2))) atTop
        (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) r /
          Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 0)
        atTop (𝓝 (Real.exp (-(r : ℝ) *
          (Real.arcosh (Real.sqrt q / 2) + 2 * S)))) := by
  have h2 : 2 < √q := by rw [Real.lt_sqrt] <;> linarith
  have hΔ : -√q / 2 < -1 := by linarith
  set c := √(2 + √q)
  have hc : 2 < c := by rw [Real.lt_sqrt] <;> linarith
  have hlam : Bethe.lamOf (-√q / 2) = Real.arcosh (√q / 2) :=
    (Bethe.eq_lamOf (Real.arcosh_pos (by linarith)) (by rw [Real.cosh_arcosh (by linarith)]; ring)).symm
  have hcΔ : BetheAnsatz.anisotropy c = -√q / 2 := by grind [Real.sqrt, BetheAnsatz.anisotropy]
  obtain ⟨Kq, hKq, Nq, -, hQ⟩ := cor34_final_exists_family_at_endpoint r hΔ
  obtain ⟨Kp, -, Np, -, hP⟩ := cor34_final_exists_family_at_endpoint 0 hΔ
  rw [show √(2 - 2 * (-√q / 2)) = c by ring_nf; rfl] at hQ hP
  set B := max (max Nq Np) (r + 2)
  choose hnQ hsQ q' hqm hqBE hqD hqL using fun i => hQ ((4 * (i + B))) (by omega) ⟨2 * (i + B), by omega⟩
  choose hnP hsP p hpm hpBE hpD hpL using fun i => hP ((4 * (i + B))) (by omega) ⟨2 * (i + B), by omega⟩
  have hp (i) : BetheAnsatz.eigenvalueRegular c (p i) = Lambda c ((4 * (i + B))) 0 := by
    rw [← hpL, Bethe.ratio_eigenvalueRegular hc (hpm i)]
    simp [cor34BetheLambda, show Even ((4 * (i + B)) / 2) from ⟨i + B, by omega⟩]
  have hNlim : Tendsto (fun i => ((4 * (i + B) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp <| tendsto_atTop_mono (fun i => (by omega : i ≤ (4 * (i + B)))) tendsto_id
  have hK := le_max_of_le_right (b := Kp) hKq.le
  have hrate : ∀ᶠ i in atTop, _ ∧ _ := .of_forall fun i => ⟨(hpD i).trans (div_le_div_of_nonneg_right (le_max_left _ Kq) (Nat.cast_nonneg _)), (hqD i).trans (div_le_div_of_nonneg_right (le_max_right Kp _) (Nat.cast_nonneg _))⟩
  suffices ∃ S, Tendsto (PottsDiscontinuity.altTanhPartial (Bethe.lamOf (-√q / 2))) atTop (𝓝 S) ∧ Tendsto (fun i => ((Lambda c ((4 * (i + B))) r / Lambda c ((4 * (i + B))) 0 : ℝ) : ℂ)) atTop (𝓝 (Real.exp (-(r : ℝ) * (Bethe.lamOf (-√q / 2) + 2 * S)) : ℂ)) by
    obtain ⟨S, hS, h⟩ := this
    exact ⟨B, S, hlam ▸ hS, hlam ▸ tendsto_ofReal_iff.1 h⟩
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · obtain ⟨S, hS, h'⟩ := Bethe.ratio_even_eigenvalue_limit_fourier_any_sign hΔ r (fun i => 4 * (i + B)) (fun i => ⟨i + B, rfl⟩) (fun i => by omega) (fun i => by omega) hnQ p q' hpm hqm hpBE hqBE hNlim _ _ hK hrate h hr hcΔ
    refine ⟨S, hS, h'.congr fun i => ?_⟩
    rw [hp, ← hqL, Bethe.ratio_eigenvalueRegular hc (hqm i)]
    simp [cor34BetheLambda, show Even ((4 * (i + B)) / 2 - r) from ⟨((4 * (i + B)) / 2 - r) / 2, by omega⟩]
  · obtain ⟨S, hS, h'⟩ := Bethe.ratio_odd_eigenvalue_limit_fourier_any_sign hΔ r (fun i => 4 * (i + B)) (fun i => ⟨i + B, rfl⟩) (fun i => by omega) (fun i => by omega) hnQ p q' hpm hqm hpBE hqBE hNlim _ _ hK hrate (by omega) hcΔ
    refine ⟨S, hS, h'.congr fun i => ?_⟩
    have hn : ¬ Even ((4 * (i + B)) / 2 - r) := Nat.not_even_iff_odd.2 ⟨((4 * (i + B)) / 2 - r) / 2, by omega⟩
    rw [hp, ← hqL, Bethe.ratio_eigenvalueZero hc (hqm i) _ (by simpa using cor34_odd_S_n_center_zero (hqm i) (q := ((4 * (i + B)) / 2 - r) / 2 + 1) (by omega))]
    simp [cor34BetheLambda, hn]

end PottsDiscontinuity.RCMProof
