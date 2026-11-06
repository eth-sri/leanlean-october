import RequestProject.CrowellFinsupp
import RequestProject.UniversalCoefficients


/-! Integral first homology and its torsion test for arbitrarily many cells. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal] (ρ : J → FreeGroup α)





/-- The prime-by-prime lifting condition excludes torsion in the covering subgroup's
abelianization, with arbitrary cell-index sets. -/
theorem fs_mem_relComm_of_pow_mem (hρ : ∀ j, ρ j ∈ N)
    (hmod : ∀ p, p.Prime →
      LiftsMod (coverSecondBoundary N ρ).toAddMonoidHom p)
    {w} (hw : w ∈ N) {n} (hn : n ≠ 0)
    (hpow : w ^ n ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) :
    w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have he : coverFoxGradient N (w ^ n) = n • coverFoxGradient N w := by
    simpa using coverFoxGradient_zpow N hw (n : ℤ)
  cases' (coverFoxGradient_mem_range_iff N ρ hρ (N.pow_mem hw n)).mpr hpow with c hc
  have hr : n • coverFoxGradient N w ∈ (coverSecondBoundary N ρ).toAddMonoidHom.range :=
    by aesop
  have hmem := mem_range_of_nsmul_mem_range _
    hmod n hn _ hr
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mp hmem
