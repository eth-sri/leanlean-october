module
public import PottsDiscontinuity.BetheAnsatz.SpectralCancellation
public import PottsDiscontinuity.BetheAnsatz.GapTransfer

/-! # The two constant words give the row eigenvalue

At the physical weights this is a limit of finite sums, so no perturbation of
the roots, the amplitudes, or the Bethe equations is necessary.
-/
@[expose] public section
open Finset Complex Matrix Classical Filter Topology
namespace PottsDiscontinuity.BetheAnsatz
noncomputable section
variable {N n : ℕ}

def rowScalar (N : ℕ) (Δ v : ℂ) (p : Fin n → ℝ) :=
  v^N * (∏ j, rowL Δ v (z (p j))) + ∏ j, rowM Δ v (z (p j))

private lemma gauge_predecessor {v : ℂ} (hv : v ≠ 0) (x : Fin (n+1) → ℤ) :
    gauge v x (cyclicPredecessorPositions N x) = v^N := by
  have h (s : Finset (Fin (n+1))) (f : Fin (n+1) → ℤ) : (∏ j ∈ s, v^(f j)) = v^(∑ j ∈ s, f j) := by
    induction s using Finset.induction_on <;> simp_all [zpow_add₀ hv]
  simp only [gauge, h, cyclicPredecessorPositions, sum_sub_distrib, Equiv.sum_comp,
    sum_ite_eq', mem_univ, ↓reduceIte, sub_sub_cancel, zpow_natCast]

section
variable (c : ℝ) {Δ : ℝ} (hΔ : Δ < -1) (v : ℂ) (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ)
    (σ : Equiv.Perm (Fin (n+1)))

include hΔ in
private lemma constant_word (hBE : BetheEquations N Δ p) (b : Bool) :
    (∑ σ, wordTerm (N := N) Δ v x p σ (fun _ => b)) =
      (∏ j, (if b then rowL else rowM) Δ v (z (p j))) * coordinateWave Δ p x := by
  let coefficient' := wordCoefficient (fun j => rowL Δ v (z (p j))) (fun j => rowM Δ v (z (p j)))
  cases b with
  | false =>
    have hw σ : coefficient' σ (fun _ => false) = _ :=
      Equiv.prod_comp σ (fun j => rowM Δ v (z (p j)))
    change (∑ σ, amplitude Δ p σ * _ * planeWave p σ x) = _
    grind [coordinateWave, mul_sum]
  | true =>
    have hw σ : coefficient' σ (fun _ => true) = _ :=
      Equiv.prod_comp (σ * finRotate (n+1)) (fun j => rowL Δ v (z (p j)))
    rw [coordinateWave_cyclicPredecessor hΔ p hBE x]
    change (∑ σ, amplitude Δ p σ * _ * planeWave p σ (cyclicPredecessorPositions N x)) = _
    grind [coordinateWave, mul_sum]

include hΔ in
theorem spectral_row {v : ℂ} (hv : v ≠ 0) (x : Fin (n+2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (n+1)) - x 0 < N) (p : Fin (n+2) → ℝ) (hp : ∀ j, z (p j) ≠ v)
    (hBE : BetheEquations N Δ p) :
    (∑ σ, amplitude Δ p σ * spectralGap Δ v N x p σ) = rowScalar N Δ v p * coordinateWave Δ p x := by
  let G := fun w => gauge v x (wordPositions N x w) * ∑ σ, wordTerm (N := N) Δ v x p σ w
  calc
    _ = ∑ w, G w := by
      simp_rw [spectralGap_words hv x hx hspan p hp, mul_sum]; rw [sum_comm]
      apply sum_congr rfl; intro w _; unfold G; rw [mul_sum]; apply sum_congr rfl; intro σ _; unfold wordTerm; ring
    _ = G (fun _ => true) + G (fun _ => false) := by
      rw [← sum_subset (show {(fun _ => true), (fun _ => false)} ⊆ univ by simp)]
      · rw [sum_pair (by grind)]
      intro w _ hw; simp at hw; simp [G, sum_wordTerm_eq_zero_of_nonconstant hΔ x p hp hBE w hw.1 hw.2]
    _ = _ := by
      simp only [G,constant_word hΔ v x p hBE, ↓reduceIte]
      change gauge v x (cyclicPredecessorPositions N x) * _ + gauge v x x * _ = _
      rw [gauge_predecessor hv]; simp [gauge,rowScalar]; ring

lemma spectralGap_one :
    spectralGap (anisotropy c) 1 N x p σ = cyclicGapSum c N x p σ := by
  have h : 1+1⁻¹ - 2*(anisotropy c : ℂ) = c^2 := by unfold anisotropy; push_cast; ring
  apply sum_congr rfl; intro y _
  rw [gapWeight, planeWave_powers, ← prod_mul_distrib]; apply prod_congr rfl; intro k _
  simp only [rowKernel, rowEntry, h, div_one, _root_.one_zpow, one_mul, inv_one]; grind

end

lemma hasDerivAt_z_zero : HasDerivAt z I 0 := by
  convert! (hasDerivAt_exp_smul_const (I : ℂ) _).comp_ofReal using 1
  · ext t; simp [z, smul_eq_mul, mul_comm, Complex.exp_eq_exp_ℂ]
  · simp

lemma eventually_avoid (u : ℂ) : ∀ᶠ t : ℝ in 𝓝[≠] 0, u ≠ z t := by
  by_cases hu : u = 1
  · subst u
    have hi : Set.Ioo (-Real.pi) Real.pi ∈ 𝓝[≠] 0 := nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos)
    filter_upwards [hi, self_mem_nhdsWithin] with t ht ht0 using (z_ne_one ht ht0).symm
  · have hz : Tendsto z (𝓝[≠] 0) (𝓝 1) := by simpa using hasDerivAt_z_zero.continuousAt.continuousWithinAt.tendsto
    exact hz.eventually_ne (Ne.symm hu) |>.mono fun _ h => Ne.symm h

/-- Any limit of the scalar expression at the physical parameter acts on the
fixed Bethe wave by the physical transfer matrix. -/
theorem eigen_of_row_limit {c : ℝ} (hc : 2 < c) (p : Fin (n+2) → ℝ) (hBE : BetheEquations N (anisotropy c) p)
    {E : ℂ} (hE : Tendsto (fun t => rowScalar N (anisotropy c) (z t) p) (𝓝[≠] 0) (𝓝 E)) :
    (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p = E • betheVector (anisotropy c) p := by
  funext y; by_cases hy : y.card = n+2
  · let s : SixVertex.State N (n+2) := ⟨y,hy⟩
    let x := positions s
    have heK (a b k : ℤ) (u : ℝ) : ContinuousAt (fun v : ℂ => rowKernel (anisotropy c) v (z u) a b k) 1 := by
      unfold rowKernel rowEntry; split_ifs <;> fun_prop (disch := simp [z_ne_zero])
    have hcA : ContinuousAt (fun v : ℂ => ∑ σ, amplitude (anisotropy c) p σ * spectralGap (anisotropy c) v N x p σ) 1 := by
      unfold spectralGap; fun_prop
    have ht := hcA.tendsto.comp (by simpa using hasDerivAt_z_zero.continuousAt.continuousWithinAt.tendsto (s := {0}ᶜ))
    have hlim := (hE.mul_const _).congr' <| (eventually_all.mpr fun j => eventually_avoid _).mono fun t h =>
      (spectral_row (anisotropy_lt_neg_one hc) (z_ne_zero t) x (positions_strictMono s) (positions_span_lt s) p h hBE).symm
    have he := tendsto_nhds_unique ht hlim
    simp only [spectralGap_one] at he
    change _ = E * extendByZero _ s.1
    rw [extendByZero_coe, transfer_betheVector_eq_cyclicGapSum c (anisotropy_lt_neg_one hc) p hBE s]; exact he
  · rw [complex_transfer_mulVec_supported c _ _ (fun z hz => betheVector_eq_zero _ _ hz) y hy]; simp [betheVector_eq_zero _ _ hy]

end
end PottsDiscontinuity.BetheAnsatz
