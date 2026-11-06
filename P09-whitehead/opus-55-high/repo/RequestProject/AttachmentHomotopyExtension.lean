import RequestProject.HomeomorphContinuousMap
import RequestProject.ExplicitRelativeAttachment
import RequestProject.BallHomotopyExtension


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
def HasHomotopyExtension (i : A → D) :=
  ∀ (Z : Type u) [TopologicalSpace Z] (f : C(D, Z)) (H : C(I × A, Z)),
    (∀ a, H (0, a) = f (i a)) →
    ∃ G : C(I × D, Z), (∀ d, G (0, d) = f d) ∧
      ∀ t a, G (t, i a) = H (t, a)

theorem HasHomotopyExtension.homeomorph {A' D' : Type u}
    [TopologicalSpace A'] [TopologicalSpace D'] {i}
    (h : HasHomotopyExtension i) (e : A ≃ₜ A') (d : D ≃ₜ D')
    j (hsq : ∀ a, j (e a) = d (i a)) : HasHomotopyExtension j := by
  intro Z _ f H h₀
  let f' := f.comp d.toContinuousMap
  let H' : C(I × A, Z) := H.comp
    ⟨fun ta => (ta.1, e ta.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
  have h'₀ : ∀ a, H' (0, a) = f' (i a) := by
    aesop
  obtain ⟨G, hG₀, hGA⟩ := h Z f' H' h'₀
  refine ⟨G.comp ⟨fun td => (td.1, d.symm td.2),
    continuous_fst.prodMk (d.symm.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · aesop
  · intro t a
    have hs : d.symm (j a) = i (e.symm a) := by
      apply d.injective
      rw [d.apply_symm_apply, ← hsq, e.apply_symm_apply]
    change G (t, d.symm (j a)) = H (t, a)
    rw [hs, hGA]
    aesop

/-- The boundary of a real normed unit ball has homotopy extension by the
explicit radial cylinder retraction. -/
theorem unitBoundary_hasHomotopyExtension E
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    HasHomotopyExtension (unitBoundaryInclusion E) := by
  intro Z _ f H h₀
  exact ⟨ballHomotopyExtension f H h₀,
    ballHomotopyExtension_zero f H h₀, ballHomotopyExtension_boundary f H h₀⟩
