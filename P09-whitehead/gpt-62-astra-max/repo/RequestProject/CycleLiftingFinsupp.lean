module

public import RequestProject.CycleLifting
public import RequestProject.CrowellFinsupp

@[expose] public section

/-! Cycle lifting in the universal cover, without finiteness assumptions on cells. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α] (ρ : J → FreeGroup α)

theorem fs_coverSecondBoundary_apply (u : J →₀ CoverRing _) (i : α) :
    coverSecondBoundary _ ρ u i =
      ∑ j ∈ u.support, u j * foxMatrixPres ρ i j := by
  classical
  rw [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum_apply] <;> rfl

/-- A finitely supported chain whose boundary is divisible by `m` differs from a cycle
by `m` times a finitely supported chain. -/
theorem fs_exists_cycle_of_boundary_nsmul (m : ℕ)
    (u : J →₀ CoverRing _)
    (hu : ∀ i, ∃ w, coverSecondBoundary _ ρ u i = m • w) :
    ∃ u' : J →₀ CoverRing _,
      coverSecondBoundary _ ρ u' = 0 ∧
      ∃ z : J →₀ CoverRing (relSub ρ), u = u' + m • z := by
  classical
  let d := coverSecondBoundary (relSub ρ) ρ
  have hρ := rel_mem_relSub' ρ
  by_cases hm : m = 0
  · refine ⟨u, ?_, 0, by simp⟩
    apply Finsupp.ext <;> simp_all
  choose w hw using hu
  have hs : (Function.support w).Finite := by
    apply (d u).support.finite_toSet.subset
    intro i hi
    by_contra hn
    have he := (hw i).symm.trans (by simpa using hn)
    exact hi ((nsmul_eq_zero_iff_of_ne m hm (w i)).mp he)
  let wf := Finsupp.ofSupportFinite w hs
  have hd : d u = m • wf := by
    apply Finsupp.ext
    assumption
  have hwc : coverFirstBoundary _ wf = 0 := by
    have hz := coverFirstBoundary_coverSecondBoundary _ ρ hρ u
    rw [hd, map_nsmul] at hz; exact (nsmul_eq_zero_iff_of_ne m hm _).mp hz
  obtain ⟨z, hz⟩ := exists_coverSecondBoundary_preimage
    _ ρ hρ le_sup_left wf hwc
  refine ⟨u - m • z, ?_, z, by abel⟩
  rw [map_sub, map_nsmul, hz, hd, sub_self]

end FiniteChains
