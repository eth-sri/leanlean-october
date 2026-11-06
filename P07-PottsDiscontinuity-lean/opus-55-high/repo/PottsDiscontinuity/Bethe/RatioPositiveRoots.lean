module

public import PottsDiscontinuity.Bethe.RatioCentralScaling
public import PottsDiscontinuity.Bethe.RatioOffsetProjection

/-! # The positive half of the source full-root family -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- The positive roots of the N/2-root symmetric family, indexed from zero. -/
noncomputable def ratioPositiveRoot (N : ℕ) (h4 : 4 ∣ N) (p : Fin (N / 2) → ℝ)
    (j : Fin (N / 4)) : ℝ := p ⟨N / 4 + j.val, by omega⟩

section
variable {N : ℕ} (h4 : 4 ∣ N) {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2))
include hp
theorem ratio_positiveRoot_pos (j : Fin (N / 4)) : 0 < ratioPositiveRoot N h4 p j := by
  let i : Fin (N / 2) := ⟨N / 4 + j.val, by omega⟩
  have hi : Fin.rev i < i := by
    grind
  have h := hp.2.1 hi
  rw [show p (Fin.rev i) = -p i from hp.2.2 i] at h
  aesop

theorem ratio_positiveRoot_mem_Ioo (j : Fin (N / 4)) :
    ratioPositiveRoot N h4 p j ∈ Ioo (-Real.pi) Real.pi := hp.1 _

/-- The source positive-root separation, in the corrected N/4-centered indexing. -/
theorem ratio_positiveRoot_lower (hn : 0 < N / 2) {M : ℝ}
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (N / 2) p hp hn (by omega) x ≤ M) (j : Fin (N / 4)) :
    (j.val : ℝ) + 1 / 2 ≤ (M * N) * ratioPositiveRoot N h4 p j := by
  have hc : 2 * (N / 4) = N / 2 := by omega
  let p' := fun i => p (Fin.cast hc i)
  have hp' := mem_S_n_cast hc hp
  have hs' : 2 * (2 * (N / 4)) ≤ N := by omega
  have hupper' : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (2 * (N / 4)) p' hp' (by omega) hs' x ≤ M := by
    intro x hx
    rw [congrFun (rootStepDensity_cast hc p hp (by omega) hn hs' (by omega)) x]
    simp_all
  exact ratio_positive_rank_lower (Nat.zero_lt_of_lt j.isLt) hp' hs' hupper' j.val j.isLt
end

/-- The source full family has the proved fixed-rank half-integer scaling.
Only weighted density convergence is required for this auxiliary result. -/
theorem ratio_full_positive_rank_scaling {Δ : ℝ} (hΔ : Δ < -1)
    (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i) (hN : ∀ i, 0 < N i)
    (p : ∀ i, Fin (N i / 2) → ℝ) (hp : ∀ i, p i ∈ S_n (N i / 2))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by grind) (by omega)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (by grind) (by omega) x - rho Δ x) (hb i)) atTop (𝓝 0))
    (k : ℕ) (hk : ∀ i, k < N i / 4) :
    Tendsto (fun i => (N i : ℝ) * ratioPositiveRoot (N i) (h4 i) (p i) ⟨k, hk i⟩) atTop
      (𝓝 (((k : ℝ) + 1 / 2) / rho Δ 0)) := by
  let m := fun i => N i / 4
  have hc (i : ℕ) : 2 * m i = N i / 2 := by grind
  let P := fun i j => p i (Fin.cast (hc i) j)
  have hP (i : ℕ) := mem_S_n_cast (hc i) (hp i)
  have hs (i : ℕ) : 2 * (2 * m i) ≤ N i := by grind
  have hρcast (i : ℕ) : rootStepDensity (N i) (2 * m i) (P i) (hP i) (by grind) (hs i) =
      rootStepDensity (N i) (N i / 2) (p i) (hp i) (by grind) (by omega) :=
    rootStepDensity_cast (hc i) (p i) (hp i) (by grind) (by grind) (hs i) (by omega)
  have hB (i : ℕ) : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (2 * m i) (P i) (hP i)
        (by grind) (hs i) (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) := by
    simpa only [hρcast i] using hb i
  have hL : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (2 * m i) (P i) (hP i)
        (by grind) (hs i) x - rho Δ x) (hB i)) atTop (𝓝 0) := by
    simp_all
  have hnP (i : ℕ) : 0 < N i / 2 := by grind
  obtain ⟨mρ, hmρ, hmesh⟩ := eventually_rootPartition_gap_le hΔ 0 N (fun i => N i / 2)
    p hp hnP (fun i => by omega) (by grind) hb hlim
  let d := fun i => (2 / mρ) / (N i : ℝ)
  have hmesh' : ∀ᶠ i in atTop, ∀ j : Fin (2 * m i + 1),
      rootPartitionPoint (2 * m i) (P i) (by grind) j.succ -
        rootPartitionPoint (2 * m i) (P i) (by grind) j.castSucc ≤ d i := by
    filter_upwards [hmesh] with i hi
    apply ratio_root_mesh_cast (hc i) (by grind) (hnP i) (p i)
    intro j
    apply (hi j).trans_eq
    ring
  exact ratio_positive_rank_scaling hΔ N m (by grind) P hP hs hB hL d (tendsto_const_nhds.div_atTop hNlim) hmesh' hNlim k hk

end PottsDiscontinuity.Bethe
