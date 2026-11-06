module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ExplicitRelativeAttachment
public import RequestProject.BallHomotopyExtension

@[expose] public section

/-! Homotopy extension for the literal old subspace of an attachment.
Currying in the compact time coordinate proves joint continuity on the
quotient attachment even when infinitely many cells are adjoined. -/

noncomputable section

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D X : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace X]

/-- The ordinary homotopy extension property, retaining both equations as
equalities of actual continuous maps. -/
def HasHomotopyExtension (i : A → D) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] (f : C(D, Z)) (H : C(I × A, Z)),
    (∀ a, H (0, a) = f (i a)) →
    ∃ G : C(I × D, Z), (∀ d, G (0, d) = f d) ∧
      ∀ t a, G (t, i a) = H (t, a)

theorem HasHomotopyExtension.homeomorph {A' D' : Type u}
    [TopologicalSpace A'] [TopologicalSpace D'] {i : A → D}
    (h : HasHomotopyExtension i) (e : A ≃ₜ A') (d : D ≃ₜ D')
    (j : A' → D') (hsq : ∀ a, j (e a) = d (i a)) : HasHomotopyExtension j := by
  intro Z _ f H h₀
  let f' : C(D, Z) := f.comp d.toContinuousMap
  let H' : C(I × A, Z) := H.comp
    ⟨fun ta => (ta.1, e ta.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
  have h'₀ : ∀ a, H' (0, a) = f' (i a) := by
    intro a
    change H (0, e a) = f (d (i a))
    rw [h₀, hsq]
  obtain ⟨G, hG₀, hGA⟩ := h Z f' H' h'₀
  refine ⟨G.comp ⟨fun td => (td.1, d.symm td.2),
    continuous_fst.prodMk (d.symm.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro z
    change G (0, d.symm z) = f z
    rw [hG₀]
    exact congrArg f (d.apply_symm_apply z)
  · intro t a
    have hs : d.symm (j a) = i (e.symm a) := by
      apply d.injective
      rw [d.apply_symm_apply, ← hsq, e.apply_symm_apply]
    change G (t, d.symm (j a)) = H (t, a)
    rw [hs, hGA]
    exact congrArg (fun b => H (t, b)) (e.apply_symm_apply a)

/-- The boundary of a real normed unit ball has homotopy extension by the
explicit radial cylinder retraction. -/
theorem unitBoundary_hasHomotopyExtension (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    HasHomotopyExtension (unitBoundaryInclusion E) := by
  intro Z _ f H h₀
  exact ⟨ballHomotopyExtension f H h₀,
    ballHomotopyExtension_zero f H h₀, ballHomotopyExtension_boundary f H h₀⟩
