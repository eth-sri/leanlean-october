module

public import PottsDiscontinuity.Bethe.AsymptoticDefs
public import PottsDiscontinuity.Bethe.Prop21Positivity

/-! # Pointwise estimates from the weighted density norm

The estimates here use convergence to zero, without imposing a rate.  They
are the norm-equivalence part of the repair of Theorem 2.6.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace PottsDiscontinuity.Bethe

section
variable {Δ : ℝ} (hΔ : Δ < -1) (f : ℝ → ℝ) (hb : BddAbove (range fun α : Icc (-Real.pi) Real.pi => |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|))
theorem weighted_abs_le_densityNorm (α : Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)| ≤ densityNorm Δ hΔ f hb :=
  le_csSup hb ⟨α, rfl⟩

theorem densityNorm_nonneg  :
    0 ≤ densityNorm Δ hΔ f hb := by
  let α : Icc (-Real.pi) Real.pi := ⟨0, by constructor <;> linarith [Real.pi_pos]⟩
  exact (abs_nonneg _).trans (weighted_abs_le_densityNorm hΔ f hb α)
end

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
/-- An explicit positive lower bound for the weight `k'`. -/
theorem density_weight_lower_pos  :
    0 < Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1) :=
  div_pos (Real.sinh_pos_iff.mpr (lamOf_pos hΔ)) (by positivity)

theorem abs_le_densityNorm_div (f : ℝ → ℝ)
    (hb : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|))
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |f x| ≤ densityNorm Δ hΔ f hb /
      (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)) := by
  let α : Icc (-Real.pi) Real.pi :=
    ⟨kInv (lamOf Δ) x, kInv_mem_Icc (lamOf_pos hΔ) hx⟩
  have h := weighted_abs_le_densityNorm hΔ f hb α
  rw [kMap_kInv (lamOf_pos hΔ), abs_mul,
    abs_of_pos (Xi_pos (lamOf_pos hΔ) _)] at h
  apply (le_div_iff₀ (density_weight_lower_pos hΔ)).mpr
  calc
    |f x| * (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))
        ≤ |f x| * Xi (lamOf Δ) (kInv (lamOf Δ) x) :=
      mul_le_mul_of_nonneg_left (Xi_bounds (lamOf_pos hΔ) _).1 (abs_nonneg _)
    _ ≤ densityNorm Δ hΔ f hb := by linarith
end

section
variable {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1) (f : ι → ℝ → ℝ)
/-- Norm convergence gives a uniform pointwise error bound tending to zero. -/
theorem tendsto_densityNorm_div (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f i (kMap (lamOf Δ) α)|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (f i) (hb i)) l (𝓝 0)) :
    Tendsto (fun i => densityNorm Δ hΔ (f i) (hb i) /
      (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))) l (𝓝 0) := by
  simpa using hlim.div_const
    (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))

/-- The lower-density part of the gap repair, under norm convergence alone. -/
theorem eventually_density_ge_half (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i))
      l (𝓝 0)) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi, m / 2 ≤ f i x := by
  obtain ⟨m, hm, hmrho⟩ := rho_uniform_lower_bound hΔ
  refine ⟨m, hm, ?_⟩
  have hε := tendsto_densityNorm_div hΔ (fun i x => f i x - rho Δ x) hb hlim
  filter_upwards [hε.eventually (gt_mem_nhds (show (0 : ℝ) < m / 2 by positivity))]
    with i hi x hx
  have hpoint := abs_le_densityNorm_div hΔ (fun x => f i x - rho Δ x) (hb i) hx
  grind
end

end PottsDiscontinuity.Bethe
