module

public import RequestProject.CrowellFinsupp
public import RequestProject.UniversalCoefficients

@[expose] public section

/-! Integral first homology and its torsion test for arbitrarily many cells. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal] (ρ : J → FreeGroup α)

noncomputable def fsCoverCycles : AddSubgroup (α →₀ CoverRing N) :=
  (coverFirstBoundary N).toAddMonoidHom.ker

noncomputable def fsCoverBoundaries : AddSubgroup (α →₀ CoverRing N) :=
  (coverSecondBoundary N ρ).toAddMonoidHom.range

def FSCoverH1 :=
  fsCoverCycles N ⧸ (fsCoverBoundaries N ρ).addSubgroupOf (fsCoverCycles N)

noncomputable instance fsCoverH1_addCommGroup : AddCommGroup (FSCoverH1 N ρ) :=
  inferInstanceAs (AddCommGroup
    (fsCoverCycles N ⧸ (fsCoverBoundaries N ρ).addSubgroupOf (fsCoverCycles N)))

/-- The prime-by-prime lifting condition excludes torsion in the covering subgroup's
abelianization, with arbitrary cell-index sets. -/
theorem fs_mem_relComm_of_pow_mem (hρ : ∀ j, ρ j ∈ N)
    (hmod : ∀ p : ℕ, p.Prime →
      LiftsMod (coverSecondBoundary N ρ).toAddMonoidHom p)
    {w : FreeGroup α} (hw : w ∈ N) {n : ℕ} (hn : n ≠ 0)
    (hpow : w ^ n ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) :
    w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have he : coverFoxGradient N (w ^ n) = n • coverFoxGradient N w := by
    simpa using coverFoxGradient_zpow N hw (n : ℤ)
  obtain ⟨c, hc⟩ := (coverFoxGradient_mem_range_iff N ρ hρ (N.pow_mem hw n)).mpr hpow
  have hr : n • coverFoxGradient N w ∈ (coverSecondBoundary N ρ).toAddMonoidHom.range :=
    ⟨c, hc.trans he⟩
  have hmem := mem_range_of_nsmul_mem_range (coverSecondBoundary N ρ).toAddMonoidHom
    hmod n hn (coverFoxGradient N w) hr
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mp hmem

end FiniteChains
