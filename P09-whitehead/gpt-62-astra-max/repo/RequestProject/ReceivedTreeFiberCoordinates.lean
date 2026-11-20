module

public import RequestProject.ReceivedTreeComparison

@[expose] public section

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
    (a : K.V) (v : UV Y _) (hv : endV v = f.onV a) :
    ∃ g : G, receiverVertex T f ψ g a = v := by
  obtain ⟨d, hd, _⟩ := (isRegular_univProj).simply_transitive
    _ v ((mappedTreeReference_end T f a).trans hv.symm)
  obtain ⟨g, rfl⟩ := hψ d <;> aesop

theorem receiverVertex_fiber_injective (hψ : Function.Injective ψ) (a : K.V) :
    Function.Injective (fun g : G => receiverVertex T f ψ g a) := by
  intro g h hgh
  apply hψ
  obtain ⟨d, _, hd⟩ := (isRegular_univProj).simply_transitive
    _ _
    ((mappedTreeReference_end T f a).trans (receiverVertex_end T f ψ g a).symm)
  exact (hd _ rfl).trans (hd (ψ h) hgh.symm).symm

/-- The based-face coordinate is also exact, not merely a homology class. -/
theorem receiverFace_fiber_surjective (hψ : Function.Surjective ψ)
    (t : K.F) (v : UF Y _) (hv : v.1.2 = f.onF t) :
    ∃ g : G, receiverFace T f ψ g t = v := by
  obtain ⟨g, hg⟩ := receiverVertex_fiber_surjective T f ψ hψ _ _ (v.2.trans ((congrArg Y.base hv).trans (f.base_onF t)))
  refine ⟨g, Subtype.ext ?_⟩
  exact Prod.ext hg hv.symm

end FiniteChains.Comb.ReceivedTree
