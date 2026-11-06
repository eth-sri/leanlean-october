module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23Density

/-!
# Density control of cyclic root gaps

These are consequences of a weighted density error bound.  They isolate the
gap estimate used in the source's regularity consequences without assuming
that the discrete and continuous densities have matching total mass.
-/

public section

open Set

namespace PottsDiscontinuity.Bethe

section
variable {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) {mXi : ℝ} (hmXi : 0 < mXi) (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α) (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi => |Xi (lamOf Δ) α * (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|)) {E : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀) (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E)
include Δ₀ Δ hΔ₀ hΔ hp hmXi hXi hbdd hE
/-- A weighted density norm error gives an unweighted pointwise error on the
physical interval. -/
theorem densityNorm_rootStepDensity_pointwise {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |rootStepDensity N n p hp hn hs x - rho Δ x| ≤
      E / mXi :=
  densityNorm_x_pointwise_le hΔ₀ hΔ
    (fun y => rootStepDensity N n p hp hn hs y - rho Δ y)
    hbdd E mXi hmXi (hXi Δ hΔ) hE hx

/-- If the density error is at most half the uniform lower bound for `ρ`,
then the step density has a positive lower bound on every physical root cell. -/
theorem rootStepDensity_lower_of_densityNorm (mρ : ℝ) (_hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hsmall : E / mXi ≤ mρ / 2) :
    ∀ x ∈ Icc (-Real.pi) Real.pi,
      mρ / 2 ≤ rootStepDensity N n p hp hn hs x := by
  have herr (x : ℝ) (hx : x ∈ Icc (-Real.pi) Real.pi) :=
    densityNorm_x_pointwise_le hΔ₀ hΔ
      (fun y => rootStepDensity N n p hp hn hs y - rho Δ y)
      hbdd E mXi hmXi (hXi Δ hΔ) hE hx
  grind

/-- A norm error small compared with the uniform density lower bound forces
an upper bound on every cyclic root gap. -/
theorem rootPartition_gap_upper_of_densityNorm (mρ : ℝ) (hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hsmall : E / mXi ≤ mρ / 2)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      2 * rootGapMultiplicity N n hs j / (mρ * (N : ℝ)) := by
  have hlower : ∀ x ∈ Icc (-Real.pi) Real.pi,
      mρ / 2 ≤ rootStepDensity N n p hp hn hs x := by
    grind [rootStepDensity_lower_of_densityNorm]
  exact rootPartition_gap_le_of_density_lower hp hn hs hmρ hlower j
end

/-- The source's upper root-gap estimate, derived from a `K/N` density error.
The explicit smallness condition is the finite-`N` requirement that the
unweighted error be at most half the uniform lower bound for `ρ`. -/
theorem rootPartition_gap_upper_of_norm_le {Δ₀ Δ : ℝ}
    (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (mρ : ℝ) (hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ}
    (hNorm : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ K / N)
    (hsmall : K / ((N : ℝ) * mXi) ≤ mρ / 2)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      2 * rootGapMultiplicity N n hs j / (mρ * (N : ℝ)) := by
  have hsmall' : (K / (N : ℝ)) / mXi ≤ mρ / 2 := by
    have heq : (K / (N : ℝ)) / mXi = K / ((N : ℝ) * mXi) := by
      field_simp
    linarith
  exact rootPartition_gap_upper_of_densityNorm hΔ₀ hΔ p hp hn hs
    hmXi hXi hbdd hNorm mρ hmρ hρ hsmall' j

section
variable {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) {mXi : ℝ} (hmXi : 0 < mXi) (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α) (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi => |Xi (lamOf Δ) α * (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|)) {E M : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀) (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E) (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ x : ℝ, rho Δ' x ≤ M)
include Δ₀ Δ hΔ₀ hΔ hp hmXi hXi hbdd hE hρ
/-- The same pointwise estimate gives an upper bound for the step density when
the continuous density has a uniform upper bound. -/
theorem rootStepDensity_upper_of_densityNorm {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    rootStepDensity N n p hp hn hs x ≤ M + E / mXi := by
  have herr :=
    densityNorm_rootStepDensity_pointwise hΔ₀ hΔ p hp hn hs hmXi hXi
      hbdd hE hx
  grind

/-- An upper bound on `ρ_p` gives a lower bound for each cyclic root gap. -/
theorem rootPartition_gap_lower_of_densityNorm (hbound : 0 < M + E / mXi) (j : Fin (n + 1)) :
    rootGapMultiplicity N n hs j /
        ((N : ℝ) * (M + E / mXi)) ≤
      rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc := by
  have hNnat : 0 < N := by omega
  have hgap :=
    rootPartition_gap_pos hp hn j
  obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp hn j
  have hρp := rootStepDensity_upper_of_densityNorm hΔ₀ hΔ p hp hn hs
    hmXi hXi hbdd hE hρ hx
  rw [rootStepDensity_on_cell hp hn hs j hcell] at hρp
  have hmul := (div_le_iff₀ (by positivity)).mp hρp
  apply (div_le_iff₀ (mul_pos (by positivity) hbound)).2
  linarith
end

end PottsDiscontinuity.Bethe
