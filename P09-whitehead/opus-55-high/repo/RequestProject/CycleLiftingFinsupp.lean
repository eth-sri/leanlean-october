import RequestProject.CycleLifting
import RequestProject.CrowellFinsupp


/-! Cycle lifting in the universal cover, without finiteness assumptions on cells. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α] (ρ : J → FreeGroup α)

theorem fs_coverSecondBoundary_apply u i :
    coverSecondBoundary (relSub ρ) ρ u i =
      ∑ j ∈ u.support, u j * foxMatrixPres ρ i j := by
  classical
  rw [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  rfl

/-- A finitely supported chain whose boundary is divisible by `m` differs from a cycle
by `m` times a finitely supported chain. -/
theorem fs_exists_cycle_of_boundary_nsmul (m : ℕ)
    u
    (hu : ∀ i, ∃ w, coverSecondBoundary (relSub ρ) ρ u i = m • w) :
    ∃ u',
      coverSecondBoundary (relSub ρ) ρ u' = 0 ∧
      ∃ z, u = u' + m • z := by
  classical
  let d := coverSecondBoundary (relSub ρ) ρ
  have hρ : ∀ j, ρ j ∈ relSub ρ := rel_mem_relSub' ρ
  by_cases hm : m = 0
  · aesop
  choose w hw using hu
  have hs : w.support.Finite := by
    apply (d u).support.finite_toSet.subset
    intro i hi
    by_contra hn
    have he : m • w i = 0 := by grind
    exact hi ((nsmul_eq_zero_iff_of_ne m hm _).mp he)
  let wf := Finsupp.ofSupportFinite w hs
  have hd : d u = m • wf := by
    aesop
  have hwc : coverFirstBoundary _ wf = 0 := by
    have hz := coverFirstBoundary_coverSecondBoundary _ ρ hρ u
    rw [hd, map_nsmul] at hz
    exact (nsmul_eq_zero_iff_of_ne m hm _).mp hz
  obtain ⟨z, hz⟩ := exists_coverSecondBoundary_preimage
    _ ρ hρ le_sup_left wf hwc
  refine ⟨u - m • z, ?_, z, by abel⟩
  grind
