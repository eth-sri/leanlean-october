module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23Density

/-!
# Density control of cyclic root gaps

These are consequences of a weighted density error bound.  They isolate the
gap estimate used in the source's regularity consequences without assuming
that the discrete and continuous densities have matching total mass.
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

variable {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (hn : 0 < n) (hs : 2 * n ≤ N) {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
      (rootStepDensity N p hn (kMap (lamOf Δ) α) -
      rho Δ (kMap (lamOf Δ) α))|)) {E : ℝ}
    (hE : densityNorm Δ
      (fun x => rootStepDensity N p hn x - rho Δ x) ≤ E) (mρ : ℝ) (hmρ : 0 < mρ)
    (_hmρ : 0 < mρ) (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hsmall : E / mXi ≤ mρ / 2) (j : Fin (n + 1))

include hbdd hn hp hs hΔ hΔ₀ in
include hmXi hXi hE in
/-- A weighted density norm error gives an unweighted pointwise error on the
physical interval. -/
theorem densityNorm_rootStepDensity_pointwise
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |rootStepDensity N p hn x - rho Δ x| ≤
      E / mXi := densityNorm_x_pointwise_le hΔ₀ hΔ
    hbdd E mXi hmXi (hXi Δ hΔ) hE hx

include hbdd hn hp hs hΔ hΔ₀ in
include hmXi hXi hE _hmρ hρ hsmall in
/-- If the density error is at most half the uniform lower bound for `ρ`,
then the step density has a positive lower bound on every physical root cell. -/
theorem rootStepDensity_lower_of_densityNorm :
    ∀ x ∈ Icc (-Real.pi) Real.pi,
      mρ / 2 ≤ rootStepDensity N p hn x := by
  have herr (x : ℝ) (hx : x ∈ Icc (-Real.pi) Real.pi) :=
    densityNorm_x_pointwise_le hΔ₀ hΔ
      hbdd E mXi hmXi (hXi Δ hΔ) hE hx
  grind

include hbdd hn hp hs hΔ hΔ₀ in
include hmXi hXi hE hmρ hρ hsmall in
/-- A norm error small compared with the uniform density lower bound forces
an upper bound on every cyclic root gap. -/
theorem rootPartition_gap_upper_of_densityNorm :
    rootPartitionPoint p hn j.succ - rootPartitionPoint p hn j.castSucc ≤
      2 * rootGapMultiplicity N n j / (mρ * (N : ℝ)) := by
  have hlower : ∀ x ∈ Icc (-Real.pi) Real.pi,
      mρ / 2 ≤ rootStepDensity N p hn x := by
    apply rootStepDensity_lower_of_densityNorm hΔ₀ hΔ p hp hn hs hmXi hXi hbdd hE
      mρ hmρ hρ
    exact hsmall
  exact rootPartition_gap_le_of_density_lower (hp := hp) (hs := hs) hmρ hlower j

include hp hΔ hΔ₀ in
/-- The source's upper root-gap estimate, derived from a `K/N` density error.
The explicit smallness condition is the finite-`N` requirement that the
unweighted error be at most half the uniform lower bound for `ρ`. -/
theorem rootPartition_gap_upper_of_norm_le {hn : 0 < n} (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (mρ : ℝ) (hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N p hn (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ}
    (hNorm : densityNorm Δ
      (fun x => rootStepDensity N p hn x - rho Δ x) ≤ K / N)
    (hsmall : K / (N * mXi) ≤ mρ / 2)
    (j : Fin (n + 1)) :
    rootPartitionPoint p hn j.succ - rootPartitionPoint p hn j.castSucc ≤
      2 * rootGapMultiplicity N n j / (mρ * (N : ℝ)) := by
  have hNnat : 0 < N := by omega
  have hsmall' : (K / (N : ℝ)) / mXi ≤ mρ / 2 := by
    have heq : (K / (N : ℝ)) / mXi = K / ((N : ℝ) * mXi) := by
      field_simp
    grind
  apply_rules [rootPartition_gap_upper_of_densityNorm]

include hbdd hn hp hs hΔ hΔ₀ in
include hmXi hXi in
/-- The same pointwise estimate gives an upper bound for the step density when
the continuous density has a uniform upper bound. -/
theorem rootStepDensity_upper_of_densityNorm
    {E M : ℝ} (hE : densityNorm Δ
      (fun x => rootStepDensity N p hn x - rho Δ x) ≤ E)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ x : ℝ, rho Δ' x ≤ M)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    rootStepDensity N p hn x ≤ M + E / mXi := by
  have herr :=
    densityNorm_rootStepDensity_pointwise hΔ₀ hΔ p hp hn hs hmXi hXi
      hbdd hE hx
  grind

include hp hΔ hΔ₀ in
/-- An upper bound on `ρ_p` gives a lower bound for each cyclic root gap. -/
theorem rootPartition_gap_lower_of_densityNorm {hn : 0 < n} (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N p hn (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {E M : ℝ} (hE : densityNorm Δ
      (fun x => rootStepDensity N p hn x - rho Δ x) ≤ E)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ x : ℝ, rho Δ' x ≤ M)
    (hbound : 0 < M + E / mXi) (j : Fin (n + 1)) :
    rootGapMultiplicity N n j /
        ((N : ℝ) * (M + E / mXi)) ≤
      rootPartitionPoint p hn j.succ - rootPartitionPoint p hn j.castSucc := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hgap :=
    rootPartition_gap_pos hp hn j
  obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp hn j
  have hρp := rootStepDensity_upper_of_densityNorm hΔ₀ hΔ p hp hn hs
    hmXi hXi hbdd hE hρ hx
  rw [rootStepDensity_on_cell hp hs hcell] at hρp
  have hden :=
    mul_pos hN (rootPartition_gap_pos hp hn j)
  have hmul := (div_le_iff₀ hden).mp hρp
  apply (div_le_iff₀ (mul_pos hN hbound)).2
  grind

end PottsDiscontinuity.Bethe
