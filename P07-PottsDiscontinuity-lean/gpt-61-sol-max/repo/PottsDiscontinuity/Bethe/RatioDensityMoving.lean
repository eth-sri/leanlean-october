module
public import Mathlib

public import PottsDiscontinuity.Bethe.Asymptotic26Cast

/-! # Moving-point density limits and central root gaps -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem ratio_density_moving_tendsto {ι : Type*} {l : Filter ι} {Δ x₀ : ℝ}
    (hΔ : Δ < -1) (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i)) l (𝓝 0))
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc (-Real.pi) Real.pi) (hxlim : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => f i (x i)) l (𝓝 (rho Δ x₀)) := by
  
  
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_densityNorm_div hΔ (fun i y => f i y - rho Δ y) hb hlim).eventually (gt_mem_nhds (show (0 ) < ε / 2 by positivity)),
    Metric.tendsto_nhds.mp ((continuous_rho hΔ).continuousAt.tendsto.comp hxlim) (ε / 2) (by positivity)] with i hi hρi
  have herr := abs_le_densityNorm_div hΔ (fun y => f i y - rho Δ y) (hb i) (hx i)
  rw [Real.dist_eq] at hρi ⊢
  grind

/-- At a moving root converging to zero, the rescaled next gap converges
to `1/ρ(0)`. This uses the exact interior step-density formula. -/
theorem ratio_gap_tendsto_at_zero {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ι → ℕ) (q : ∀ i, Fin (n i) → ℝ) (hq : ∀ i, q i ∈ S_n (n i))
    (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i) x - rho Δ x) (hb i)) l (𝓝 0))
    (j : ∀ i, Fin (n i)) (hj : ∀ i, (j i).val + 1 < n i)
    (hzero : Tendsto (fun i => q i (j i)) l (𝓝 0)) :
    Tendsto (fun i => (N i : ℝ) * (q i ⟨(j i).val + 1, hj i⟩ - q i (j i))) l
      (𝓝 (rho Δ 0)⁻¹) := by
  
  
  apply ((ratio_density_moving_tendsto hΔ
                         (fun i => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)) hb hlim
                         (fun i => q i (j i)) (fun i => ⟨((hq i).1 _).1.le, ((hq i).1 _).2.le⟩) hzero).inv₀ (rho_pos hΔ 0).ne').congr
  intro i
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (hn i).ne'
  
  let q'  := fun t => q i (Fin.cast hk.symm t)
  have hq' : q' ∈ S_n (k + 1) := by
                                   solve_by_elim [_root_.PottsDiscontinuity.Bethe.mem_S_n_cast]
  let t : Fin k := ⟨(j i).val, by have := hj i; omega⟩
  
  have he₁ : Fin.cast hk.symm t.succ = ⟨(j i).val + 1, hj i⟩ := Fin.ext rfl
  
  rw [← congrFun (rootStepDensity_cast hk.symm (q i) (hq i) (by omega) (hn i)
                    (by have := hs i; omega) (hs i)) (q i (j i)), rootStepDensity_interior hq' (by have := hs i; omega) t (by
                                                                                               
                                                                                               
                                                                                               exact ⟨le_rfl, (hq i).2.1 (by grind)⟩)]
  dsimp only [q']
  rw [(Fin.ext rfl : Fin.cast hk.symm t.castSucc = j i), he₁, one_div, inv_inv]

end PottsDiscontinuity.Bethe
