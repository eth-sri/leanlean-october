/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomain
public import VaughtConjecture.Knight.ProjectedChartComparison
public import VaughtConjecture.Knight.ClassPresentation
public import InfinitaryLogic.ModelTheory.MorleyCounting

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower FirstOrder Language KnightRealization Cardinal StoppingRankFiltration

/-- Any two models at one stage have a common chart of the empty tuple: both label it, and
there is only one label of the empty tuple. -/
theorem hasCommonChart_elim0 {α : LimitStage} {M N : Type}
    {W : KnightRealization α M} {V : KnightRealization α N} (hW : W.IsModel)
    (hV : V.IsModel) :
    HasCommonChart W V (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  obtain ⟨p, hp⟩ := exists_eval_empty_at hW
  obtain ⟨p', hp'⟩ := exists_eval_empty_at hV
  refine ⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, Fin.elim0, p, hp, ?_,
    funext fun i => i.elim0, funext fun i => i.elim0⟩
  rw [hp', Subsingleton.elim p' p]

/-- **Back-and-forth equivalence on an expansion domain.**  Two counted models whose classes
lie in `domain η` are back-and-forth equivalent at level `η` on the empty tuple, by comparison of their expansions. -/
theorem bfEquiv_of_mem_domain {η : Ordinal.{0}} {R S : KnightNatModel}
    (hR : Quotient.mk knightModelSetoid R ∈ domain η)
    (hS : Quotient.mk knightModelSetoid S ∈ domain η) :
    @BFEquiv knightLang ℕ (structureOf R.1) ℕ (structureOf S.1) η 0 Fin.elim0 Fin.elim0 := by
  obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hR
  obtain ⟨V, hVm, hVr⟩ := exists_model_of_mem_domain hS
  have h := bfEquiv_of_commonChart η W V hWm hVm
    (hasCommonChart_elim0 hWm hVm)
  rwa [reduct_omegaStage_eq hWr, reduct_omegaStage_eq hVr] at h

/-- **The library relation on a domain**: coded `ℕ`-models of `knightSentence` whose classes
lie in `domain η` are related by `bfEquivSetoid knightSentence η`. -/
theorem bfEquivSetoid_r_of_mem_domain {η : Ordinal.{0}} {c d : ModelsOf knightSentence}
    (hc : modelClass c ∈ domain η) (hd : modelClass d ∈ domain η) :
    (bfEquivSetoid knightSentence η).r c d := by
  have h := bfEquiv_of_mem_domain (R := realizationOfCode c) (S := realizationOfCode d) hc hd
  let realised (c : ModelsOf knightSentence) := structureOf (realizationOfCode c).1
  have transport (c : ModelsOf knightSentence) :
      @BFEquiv knightLang ℕ (realised c) ℕ c.1.toStructure η 0 Fin.elim0 Fin.elim0 := by
    simpa only [comp_fin_elim0] using @equiv_implies_BFEquiv knightLang ℕ ℕ (realised c)
      c.1.toStructure (isKnightModel_of_mem c).structureOfToRealizationEquiv η 0 Fin.elim0
  have h' := @BFEquiv.trans knightLang ℕ c.1.toStructure ℕ (realised c) 0 ℕ (realised d) η _ _ _
    (@BFEquiv.symm knightLang ℕ (realised c) ℕ c.1.toStructure 0 η _ _ (transport c)) h
  exact @BFEquiv.trans knightLang ℕ c.1.toStructure ℕ (realised d) 0 ℕ d.1.toStructure η _ _ _ h' (transport d)

/-- **Countably many `≡_η`-classes**: for every countable `η`, the library's quotient of the
coded `ℕ`-models of `knightSentence` by back-and-forth equivalence at level `η` is countable.
The classes outside `domain η` are countable, and the classes inside it project to at most one
`≡_η`-class. -/
theorem countable_bfEquivSetoid_quotient (hct : CountableTerminalFibres)
    {η : Ordinal.{0}} (hη : η < Ordinal.omega 1) :
    Countable (Quotient (bfEquivSetoid knightSentence η)) := by
  let π : Classes → Quotient (bfEquivSetoid knightSentence η) :=
    fun q => bfProj knightSentence η (isoClassEquiv.symm q)
  have hπ (c : ModelsOf knightSentence) : π (modelClass c) = Quotient.mk _ c := by
    change bfProj knightSentence η (isoClassEquiv.symm (isoClassEquiv _)) = _
    rw [Equiv.symm_apply_apply, bfProj_mk]
  have hcover : (Set.univ : Set (Quotient (bfEquivSetoid knightSentence η))) ⊆
      π '' (domain η)ᶜ ∪ π '' domain η := by
    rintro x -
    induction x using Quotient.inductionOn with
    | h c =>
      grind
  have hsub : (π '' domain η).Subsingleton := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨s, hs, rfl⟩
    obtain ⟨c, rfl⟩ := modelClass_surjective q
    obtain ⟨d, rfl⟩ := modelClass_surjective s
    rw [hπ, hπ]
    exact Quotient.sound (bfEquivSetoid_r_of_mem_domain hq hs)
  exact Set.countable_univ_iff.mp
    ((((compl_countable hct (by rwa [ord_aleph])).image π).union hsub.countable).mono hcover)

end VaughtConjecture.Knight.ExpansionDomain
