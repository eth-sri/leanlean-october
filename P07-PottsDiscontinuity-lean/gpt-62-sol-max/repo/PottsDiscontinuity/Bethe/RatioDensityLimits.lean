module

public import PottsDiscontinuity.Bethe.AsymptoticNorm

/-! # Density consequences used in the source-family specialization -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem ratio_densityNorm_tendsto_of_rate {ι : Type*} {l : Filter ι} {Δ K : ℝ}
    (N : ι → ℕ) (hN : Tendsto (fun i => (N i : ℝ)) l atTop)
    (f : ι → ℝ → ℝ) (hrate : ∀ᶠ i in l, densityNorm Δ (f i) ≤ K / N i) :
    Tendsto (fun i => densityNorm Δ (f i)) l (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun i => densityNorm_nonneg (f i)) hrate
    (tendsto_const_nhds.div_atTop hN)

/-- The weighted rate gives the unweighted rate used by the geometric lemmas. -/
theorem ratio_density_error_of_rate {ι : Type*} {l : Filter ι} {Δ K : ℝ} (hΔ : Δ < -1)
    (N : ι → ℕ) (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (densityValues Δ (fun x => f i x - rho Δ x)))
    (hrate : ∀ᶠ i in l, densityNorm Δ (fun x => f i x - rho Δ x) ≤ K / N i) :
    ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |f i x - rho Δ x| ≤
        (K / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))) / N i := by
  have hw := (density_weight_lower_pos hΔ).le
  filter_upwards [hrate] with i hi x hx
  calc
    _ ≤ densityNorm Δ (fun x => f i x - rho Δ x) /
        (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)) :=
      abs_le_densityNorm_div hΔ (fun x => f i x - rho Δ x) (hb i) hx
    _ ≤ (K / (N i : ℝ)) / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)) :=
      div_le_div_of_nonneg_right hi hw
    _ = _ := by ring

end PottsDiscontinuity.Bethe
