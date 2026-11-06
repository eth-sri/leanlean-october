import RequestProject.SimpleLoopBoundaryHomeomorph
import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic


/-! Nonempty finite concatenation without an inserted constant initial or
terminal segment. It preserves injectivity when different arcs only meet
at consecutive endpoints. This is the parameter used for actual finite
circle homeomorphisms. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

namespace FiniteChains.RelativeAttachment

variable {X : Type} [TopologicalSpace X]

/-- `n+1` arcs, with no artificial stationary part. -/
def arcConcat : (n : ℕ) → (v : Fin (n + 2) → X) →
    (∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) → Path (v 0) (v (Fin.last (n + 1)))
  | 0, _, F => F 0
  | n + 1, v, F =>
      (arcConcat n (v ∘ Fin.castSucc) (F ·.castSucc)).trans (F (Fin.last (n + 1)))

theorem arcConcat_homotopic_concat n (v : Fin (n + 2) → X)
    F :
    (arcConcat n v F).Homotopic (Path.concat v F) := by
  induction n with
  | zero =>
    rw [Path.concat_succ, Path.concat_zero]
    exact (Path.Homotopic.refl_trans _).symm
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih _ _).hcomp
      (by aesop)

theorem arcConcat_range n v
    F (x : X) :
    x ∈ Set.range (arcConcat n v F) ↔ ∃ i, x ∈ Set.range (F i) := by
  induction n with
  | zero =>
    aesop
  | succ n ih =>
    change x ∈ Set.range
      ((arcConcat n (v ∘ Fin.castSucc) (F ·.castSucc)).trans (F _)) ↔ _
    rw [Path.trans_range, Set.mem_union, ih]
    constructor
    · tauto
    · rintro ⟨i, hi⟩
      refine Fin.lastCases Or.inr
        (fun j hj => Or.inl ⟨j, hj⟩) i hi

theorem arcConcat_injective n (v : Fin (n + 2) → X)
    F
    (hF : ∀ i, Function.Injective (F i))
    (hmeet : ∀ i j, i < j → ∀ s t,
      F i s = F j t → s = 1 ∧ t = 0) : Function.Injective (arcConcat n v F) := by
  induction n with
  | zero => exact hF 0
  | succ n ih =>
    apply path_trans_injective
    · exact ih _ _
        (by tauto)
        (hmeet ·.castSucc ·.castSucc · · · ·)
    · tauto
    · intro s t h
      obtain ⟨i, u, hu⟩ := (arcConcat_range n (v ∘ Fin.castSucc)
        _ _).mp ⟨s, rfl⟩
      have ht := (hmeet i.castSucc _
        i.castSucc_lt_last u t (hu.trans h)).2
      rwa [ht, (F _).source] at h
