import Mathlib.Tactic

import RequestProject.GenusNormalizedReferenceTransport
import RequestProject.GenusPolygonCoefficientGeneration

/-! B2 for the actual finite genus spine, and its arbitrary-family
finite-support consequence. All geometric reference hypotheses are discharged
by the explicitly constructed pre-substitution degree-one polygon.

This file does not assert the original topological MainClaim.
-/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

include hrho in
/-- Actual single-block B2. The only premise on the arbitrary vector is
the original internal Fox-boundary equation, over the original substituted
group ring. No receiver, degree, comparison, or reference assumption remains. -/
theorem finiteSpineActualB2
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * singleFiniteSpineReference ρ q u m := by
  obtain ⟨y, hy, hreference⟩ := singleFiniteSpineReference_corrected_geometry ρ q u hrho
  exact finiteSpine_polygon_reference_generates q ρ u hrho
    (singleFiniteSpineReference ρ q u) (singleFiniteSpineReference_internal ρ q u hrho)
    (transportedUniversalPolygonAttachingChain ρ q u)
    (transportedUniversalPolygonAttachingChain_mem_inc ρ q u)
    (transportedUniversalPolygonAttachingChain_degree ρ q u)
    y hy hreference (transportedUniversalPolygonPole ρ q u)
    (transportedUniversalPolygonAttachingChain_normalized ρ q u) β hβ

variable {S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (qs : S → ℕ) [∀ s, NeZero (qs s)]
  (us : ∀ s, Fin (qs s) × Bool → FreeGroup α)
  (hσ : ∀ s, σ (Sum.inr s) = commWord (us s) (finitePairs (qs s)))

include hσ in
/-- The concrete individual input required by the already constructed
arbitrary-family base-change theorem, now with every geometric input proved. -/
theorem finiteSpineIndividualB2_actual : FiniteSpineIndividualB2 σ qs us := by
  solve_by_elim [FiniteChains.Davis.Genus.finiteSpineActualB2]

/-- Actual finite-support cycle generation for simultaneous substitution.
The former individual-B2 assumption is discharged by the genus geometry. -/
abbrev finiteSpineFamily_fsGenerates_actual
    (x : (Jr ⊕ (Σ s, NamedSpineRel (qs s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF σ (familyFiniteSpineWordBlock qs us))))
    (hx : coverSecondBoundary (relSub (substPresF σ (familyFiniteSpineWordBlock qs us)))
      (substPresF σ (familyFiniteSpineWordBlock qs us)) x = 0)  :=
  finiteSpineFamily_fsGenerates σ qs us hσ (finiteSpineIndividualB2_actual σ qs us hσ) x hx

end FiniteChains.Davis.Genus
