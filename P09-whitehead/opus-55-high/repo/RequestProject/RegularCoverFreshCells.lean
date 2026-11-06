import RequestProject.RegularCoverAcyclicChains
import RequestProject.FreshLoopTreeStrictness


/-! The actual descended chains have stronger strictness than a generic
cellular chain: a fresh loop or a fresh face at every step. Thus tree
collapse cannot erase their strict inclusions. Pending final Lean check. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
universe u

namespace RelativeCellChain
variable {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelativeCellChain c n)
  {K : Complex2.{u}} (p : Hom (c 0) K)

theorem descInc_freshLoopOrFace i (h : FreshLoopOrFace (R.inc i)) :
    FreshLoopOrFace (R.descInc p i) := by
  rcases h with ⟨e, hloop, he⟩ | ⟨f, hf⟩
  · left
    cases i with
    | zero =>
        have hoff : ∀ d, (inclFrom c R.inc 1).onE d ≠ e := by
          tauto
        let w : OffE (inclFrom c R.inc 1) := by tauto
        refine ⟨Sum.inr w, ?_, ?_⟩
        · change pushV p _ ((c 1).src e) =
            pushV p _ ((c 1).tgt e)
          simp_all
        · rintro ⟨d, hd⟩
          exact Sum.inl_ne_inr hd
    | succ i =>
        have hoff : ∀ d, (inclFrom c R.inc _).onE d ≠ e := by
          intro d hd
          exact he ⟨(inclFrom c R.inc _).onE d, hd⟩
        let w : OffE (inclFrom c R.inc _) := by tauto
        refine ⟨Sum.inr w, ?_, ?_⟩
        · change pushV p _ ((c (i + 2)).src e) =
            pushV p _ ((c (i + 2)).tgt e)
          simp_all
        · rintro ⟨d, hd⟩
          cases d with
          | inl d => exact Sum.inl_ne_inr hd
          | inr d =>
              exact he ⟨d.val, pushE_eq_inr_imp p _ (R.inclE _)
                _ w hd⟩
  · right
    cases i with
    | zero =>
        have hoff : ∀ d, (inclFrom c R.inc 1).onF d ≠ f := by
          tauto
        refine ⟨Sum.inr ⟨f, hoff⟩, ?_⟩
        rintro ⟨d, hd⟩
        exact Sum.inl_ne_inr hd
    | succ i =>
        have hoff : ∀ d, (inclFrom c R.inc _).onF d ≠ f := by
          intro d hd
          exact hf ⟨(inclFrom c R.inc _).onF d, hd⟩
        let w : OffF (inclFrom c R.inc _) := by tauto
        refine ⟨Sum.inr w, ?_⟩
        rintro ⟨d, hd⟩
        cases d with
        | inl d => exact Sum.inl_ne_inr hd
        | inr d =>
            exact hf ⟨d.val, pushF_eq_inr_imp p _ (R.inclF _)
              _ w hd⟩

end RelativeCellChain

namespace RelativeTreeAmbientChain
open SpanningTree RelativeNormalForm
variable {D : Complex2} (T : SpanningTree D) {n : ℕ}
  (c : AmbientChain (treeRel T) n)

theorem inclusions_freshLoopOrFace i (hi : i < n + 1) :
    FreshLoopOrFace (inclusions T c i) := by
  cases i with
  | zero =>
      left
      refine ⟨Sum.inr c.fresh, rfl, ?_⟩
      rintro ⟨d, hd⟩
      exact Sum.inl_ne_inr hd
  | succ i =>
      rcases c.chain_proper _ hi with ⟨a, ha⟩ | ⟨f, hf⟩
      · tauto
      tauto

end RelativeTreeAmbientChain

theorem regularCoverChain_freshLoopOrFace
    T hD (p : Hom D K)
    n i (hi : i < n + 1) :
    FreshLoopOrFace (regularCoverChainInclusion T hD p n i) :=
  (acyclicRelativeCellChain T hD n).descInc_freshLoopOrFace p i
    (RelativeTreeAmbientChain.inclusions_freshLoopOrFace T
      _ i hi)
