module

public import PottsDiscontinuity.LinearAlgebra.PerronFrobeniusGrowth
public import PottsDiscontinuity.SixVertex.Irreducible
public import PottsDiscontinuity.SixVertex.TraceFormula

/-!
# Perron–Frobenius eigenvalue of the blocks `V^{[n]}` and the rate of `Z^{(r)}_{6V}`

For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is symmetric, irreducible and has a simple positive
Perron–Frobenius eigenvalue with a strictly positive eigenvector.  With
`Λ_r(N) = pfRoot (V^{[N/2 - r]})` we obtain
`lim_{M → ∞} (1/M) log Z^{(r)}_{6V}(N, M) = log Λ_r(N)` for `N ≥ 1`, `0 ≤ r ≤ N/2`.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c : ℝ}

/-- `Λ_r(N)`: the Perron–Frobenius eigenvalue (largest eigenvalue) of the block `V^{[N/2 - r]}`. -/
noncomputable def Lambda (c : ℝ) (N r : ℕ) : ℝ := pfRoot (transferBlock N c (N / 2 - r))

/-- Positivity, a positive eigenvector, and simplicity of the block Perron root. -/
theorem transferBlock_perronFrobenius (hc : 0 < c) {n : ℕ} (hn : n ≤ N) :
    0 < pfRoot (transferBlock N c n) ∧
    (∃ v : State N n → ℝ, (∀ x, 0 < v x) ∧
      transferBlock N c n *ᵥ v = pfRoot (transferBlock N c n) • v) ∧
    (transferBlock N c n).charpoly.rootMultiplicity (pfRoot (transferBlock N c n)) = 1 := by
  let : Nonempty (State N n) := ⟨packed hn⟩
  have hA := transferBlock_isHermitian (N := N) (c := c) n
  have hnn := transferBlock_nonneg (N := N) hc.le n
  have hirr := exists_pos_pow_block hc hn
  exact ⟨pfRoot_pos_of_irreducible hnn hirr hA, exists_pos_eigenvector hnn hirr hA,
    rootMultiplicity_charpoly_pfRoot hnn hirr hA⟩

theorem transferBlock_trace_pos (hc : 0 < c) {n : ℕ} (hn : n ≤ N) (M : ℕ) :
    0 < (transferBlock N c n ^ M).trace := by
  let : Nonempty (State N n) := ⟨packed hn⟩
  have hp := (transferBlock_perronFrobenius (N := N) hc hn).1
  exact (show 0 < min 1 (pfRoot (transferBlock N c n))⁻¹ * pfRoot (transferBlock N c n) ^ M by positivity).trans_le
    (trace_pow_lower (transferBlock_isHermitian n) (transferBlock_nonneg hc.le n) (by simp) hp M)

/-- `Λ_r(N) > 0` for `0 ≤ r ≤ N/2` and `c > 0`. -/
theorem Lambda_pos (hc : 0 < c) {r : ℕ} (hr : r ≤ N / 2) : 0 < Lambda c N r :=
  (transferBlock_perronFrobenius hc (n := N / 2 - r) (by omega)).1

/-- Rate of a six-vertex sector indexed by its arrow number. -/
theorem tendsto_log_Z6Vn (hc : 0 < c) (hN : 0 < N) {n : ℕ} (hn : n ≤ N) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vn c N M n)) atTop
      (𝓝 (Real.log (pfRoot (transferBlock N c n)))) := by
  let : Nonempty (State N n) := ⟨packed hn⟩
  refine (tendsto_log_trace_pow (transferBlock_isHermitian n) (transferBlock_nonneg hc.le n)
    (by simp) (transferBlock_perronFrobenius hc hn).1).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  rw [Z6Vn_eq_trace_block hN hM c n]

theorem Z6Vr_eq_Z6Vn (c : ℝ) (N M r : ℕ) (hr : r ≤ N / 2) :
    Z6Vr c N M r = Z6Vn c N M (N / 2 - r) := by
  unfold Z6Vr Z6Vn
  congr 1
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  omega

end PottsDiscontinuity.SixVertex
