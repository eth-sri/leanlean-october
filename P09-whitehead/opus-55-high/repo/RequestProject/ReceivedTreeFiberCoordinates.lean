import RequestProject.ReceivedTreeComparison


/-! Exact sheet coordinates over each cell when the geometric receiver is
surjective. This applies before substitution to the spine/old-block group
equivalence; no surjectivity of a substituted group map is assumed.
Pending final Lean verification.
-/

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (ψ : G →* Pi1 Y (f.onV T.root))

/-- Every actual lift of the image of a vertex has a receiving-group sheet. -/
theorem receiverVertex_fiber_surjective (hψ : Function.Surjective ψ)
    a v (hv : endV v = f.onV a) :
    ∃ g, receiverVertex T f ψ g a = v := by
  have he :=
    (mappedTreeReference_end T f a).trans hv.symm
  obtain ⟨d, hd, _⟩ := (isRegular_univProj (X := Y) (x₀ := f.onV T.root)).simply_transitive
    _ v he
  obtain ⟨g, rfl⟩ := hψ d
  tauto

theorem receiverVertex_fiber_injective (hψ : Function.Injective ψ) a :
    Function.Injective (receiverVertex T f ψ · a) := by
  intro g h hgh
  apply hψ
  obtain ⟨d, _, hd⟩ := (isRegular_univProj (X := Y) (x₀ := f.onV T.root)).simply_transitive
    _ _
    ((mappedTreeReference_end T f a).trans (receiverVertex_end T f ψ g a).symm)
  exact (hd _ rfl).trans (hd _ hgh.symm).symm

/-- The based-face coordinate is also exact, not merely a homology class. -/
theorem receiverFace_fiber_surjective (hψ : Function.Surjective ψ)
    t v (hv : v.1.2 = f.onF t) :
    ∃ g, receiverFace T f ψ g t = v := by
  have he :=
    v.2.trans ((congrArg Y.base hv).trans (f.base_onF t))
  cases' receiverVertex_fiber_surjective T f ψ hψ _ v.1.1 he with g hg
  refine ⟨g, Subtype.ext ?_⟩
  aesop
