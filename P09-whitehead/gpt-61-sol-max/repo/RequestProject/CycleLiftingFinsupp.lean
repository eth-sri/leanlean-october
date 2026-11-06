import Mathlib.Tactic

import RequestProject.CycleLifting
import RequestProject.CrowellFinsupp

/-! Cycle lifting in the universal cover, without finiteness assumptions on cells. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α] (ρ : J → FreeGroup α)

theorem fs_coverSecondBoundary_apply (u : J →₀ CoverRing (relSub ρ)) (i : α) :
    coverSecondBoundary (relSub ρ) ρ u i =
      ∑ j ∈ u.support, u j * foxMatrixPres ρ i j := by
  aesop (add simp [coverSecondBoundary, Finsupp.linearCombination_apply])

/-- A finitely supported chain whose boundary is divisible by `m` differs from a cycle
by `m` times a finitely supported chain. -/
theorem fs_exists_cycle_of_boundary_nsmul (m : ℕ)
    (u : J →₀ CoverRing (relSub ρ))
    (hu : ∀ i, ∃ w, coverSecondBoundary (relSub ρ) ρ u i = m • w) :
    ∃ u' : J →₀ CoverRing (relSub ρ),
      coverSecondBoundary (relSub ρ) ρ u' = 0 ∧
      ∃ z : J →₀ CoverRing (relSub ρ), u = u' + m • z := by
  classical
  let d := coverSecondBoundary (relSub ρ) ρ
  have hρ  := rel_mem_relSub' ρ
  by_cases hm : m = 0
  · aesop
  choose w hw using hu
  have hs : (Function.support w).Finite := by
    apply (d u).support.finite_toSet.subset
    intro i hi
    by_contra hn
    have hz : d u i = 0 := by simpa using hn
    have he  := (hw i).symm.trans hz
    exact hi ((nsmul_eq_zero_iff_of_ne m hm (w i)).mp he)
  let wf  := Finsupp.ofSupportFinite w hs
  have hd : d u = m • wf := by
    apply Finsupp.ext
    intro i
    simpa [wf] using hw i
  have hwc : coverFirstBoundary (relSub ρ) wf = 0 := by
    have hz := coverFirstBoundary_coverSecondBoundary (relSub ρ) ρ hρ u
    change coverFirstBoundary (relSub ρ) (d u) = 0 at hz
    rw [hd, map_nsmul] at hz
    exact (nsmul_eq_zero_iff_of_ne m hm _).mp hz
  obtain ⟨z, hz⟩ := exists_coverSecondBoundary_preimage
    (relSub ρ) ρ hρ le_sup_left wf hwc
  refine ⟨u - m • z, ?_, z, by abel⟩
  change d (u - m • z) = 0
  rw [map_sub, map_nsmul, hz, hd, sub_self]

end FiniteChains
