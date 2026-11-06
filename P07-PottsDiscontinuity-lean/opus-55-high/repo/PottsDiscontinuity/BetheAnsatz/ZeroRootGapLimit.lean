module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Formula
public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordLimit

/-!
# The punctured gap-sum identity at a zero root

Away from the singular value, the cyclic gap sum is exactly its finite word
expansion. Combining that expansion with the root-slot partition gives the
T₀ plus paired T₁ decomposition on a punctured neighborhood.
-/

public section

open Finset Complex Classical Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- Near a zero momentum, every perturbed spectral parameter is away from one. -/
theorem eventually_perturbedMomenta_z_ne_one {m : ℕ} (p : Fin (m + 2) → ℝ)
    (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0) :
    ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ k, z (perturbedMomenta p l t k) ≠ 1 := by
  have hpk0 : ∀ k, k ≠ l → p k ≠ 0 := by
    grind
  filter_upwards [eventually_z_ne_one_zero] with t ht k
  by_cases hkl : k = l
  · simp_all
  · rw [perturbedMomenta_of_ne p l k t hkl]
    exact z_ne_one (hp k) (hpk0 k hkl)

section
variable {N m : ℕ} {c : ℝ} (hc : 2 < c) (x : Fin (m + 2) → ℤ) (hx : StrictMono x) (hspan : x (Fin.last (m + 1)) - x 0 < (N : ℤ)) (p : Fin (m + 2) → ℝ) (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
include hc hx hspan hp hinj hpl hBE
/-- On a punctured neighborhood, the fixed-amplitude cyclic gap sum is the
constant T₀ expression plus the canonical paired T₁ terms. -/
theorem eventually_fixedAmplitudeGapSum_eq_constant_plus_t1  :
    (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude (anisotropy c) p σ *
          cyclicGapSum c N x (perturbedMomenta p l t) σ) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ =>
        constantWordSumPerturbed (N := N) c x p l t +
          ∑ i : T1PairIndex (m + 1) l, t1PairTerm (N := N) c x p l t i) := by
  filter_upwards [(eventually_perturbedMomenta_z_ne_one p hp hinj l hpl)] with t ht
  let q := perturbedMomenta p l t
  calc
    _ = ∑ σ : Equiv.Perm (Fin (m + 2)),
        ∑ w : Fin (m + 2) → Bool,
          fixedAmplitudeWordTerm c x p q σ w := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [cyclicGapSum_eq_sum_words c x q σ hx hspan ht, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      unfold fixedAmplitudeWordTerm
      ring
    _ = constantWordSumPerturbed c x p l t +
        ∑ i : T1PairIndex (m + 1) l, t1PairTerm c x p l t i :=
      fixedAmplitudeWordSum_eq_constant_plus_t1 hc (by omega) x p hp hinj l hpl hBE t

/-- The fixed-amplitude cyclic gap sum converges to the degenerate eigenvalue
times the coordinate wave. This identifies the perturbed transfer action without
assuming that the perturbed momenta satisfy the Bethe equations. -/
theorem tendsto_fixedAmplitudeGapSum_zeroRoot  :
    Tendsto (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude (anisotropy c) p σ *
          cyclicGapSum c N x (perturbedMomenta p l t) σ)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (eigenvalueZero N c p l * coordinateWave (anisotropy c) p x)) := by
  have h := (tendsto_constantWordSumPerturbed hc x p hp hinj l hpl hBE).add (tendsto_sum_t1PairTerm hc x p hp hinj l hpl hBE)
  rw [← t0RegularizedSum_zero, t0_t1_pairLimits_eq_eigenvalueZero hc x p hp hinj l hpl hBE] at h
  exact h.congr' (eventually_fixedAmplitudeGapSum_eq_constant_plus_t1 hc x hx hspan p hp hinj l hpl hBE).symm

/-- The limiting fixed-amplitude gap sum agrees with its value at the original
zero-root tuple, by continuity of the gap expression. -/
theorem fixedAmplitudeGapSum_zero_eq_eigenvalueZero  :
    (∑ σ : Equiv.Perm (Fin (m + 2)),
      amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ) =
      eigenvalueZero N c p l * coordinateWave (anisotropy c) p x :=
  tendsto_nhds_unique ((tendsto_fixedAmplitude_gapSum c (anisotropy c) x p l).mono_left nhdsWithin_le_nhds) (tendsto_fixedAmplitudeGapSum_zeroRoot hc x hx hspan p hp hinj l hpl hBE)
end

end PottsDiscontinuity.BetheAnsatz
