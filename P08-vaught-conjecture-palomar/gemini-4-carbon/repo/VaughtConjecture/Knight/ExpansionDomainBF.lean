/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomain
public import VaughtConjecture.Knight.OrdinaryFiniteCutReceiving
public import VaughtConjecture.Knight.ChartLanguage
public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.ClassPresentation
public import InfinitaryLogic.ModelTheory.MorleyCounting
public import InfinitaryLogic.Scott.BackAndForth

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain
open TypeTower FirstOrder Language Structure KnightRealization StageType Value ExtOrd
open Cardinal StoppingRankFiltration
noncomputable section
universe w

private theorem lowerChart {α β : LimitStage} (h : β ≤ α) {M N : Type w}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart (W.reduct h) (W'.reduct h) a b := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  exact ⟨k, ta, tb, σ, reduceType β.2 h p,
    by rw [Realization.reduct_eval, hta]; rfl,
    by rw [Realization.reduct_eval, htb]; rfl, ha, hb⟩

private theorem reverseChart {α : LimitStage} {M N : Type w}
    {W : KnightRealization α M} {W' : KnightRealization α N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hc : HasCommonChart W W' a b) :
    HasCommonChart W' W b a := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  exact ⟨k, tb, ta, σ, p, htb, hta, hb, ha⟩

private theorem extend_commonChart (α : Ordinal.{0}) {M N : Type w}
    (W : KnightRealization (blockStage (α + 1)) M)
    (W' : KnightRealization (blockStage (α + 1)) N)
    (hc : W.IsExactParentConsistent) (hcover : W.IsCovering)
    (hc' : W'.IsExactParentConsistent) (hr' : FiniteCutReceiving W')
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (seed : HasCommonChart W W' a b) (x : M) :
    ∃ y : N, HasCommonChart (W.reduct (blockStage_le_succ α))
      (W'.reduct (blockStage_le_succ α)) (Fin.snoc a x) (Fin.snoc b y) := by
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := seed
  by_cases hmem : x ∈ Set.range ta
  · obtain ⟨j, hj⟩ := hmem
    exact ⟨tb j, lowerChart (blockStage_le_succ α) ⟨k, ta, tb, Fin.snoc σ j, p, hta, htb,
      by rw [Fin.comp_snoc, ha, hj], by rw [Fin.comp_snoc, hb]⟩⟩
  · obtain ⟨l, s, f, hfs, hsome⟩ := hcover (snoc ta x hmem)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
    let g : Fin k ↪ Fin l := Fin.castSuccEmb.trans f
    have hseg : g.trans s = ta := by
      change (Fin.castSuccEmb.trans f).trans s = ta
      rw [Function.Embedding.trans_assoc, hfs, castSuccEmb_trans_snoc]
    have hface : typeMap g P = some p := by
      have he := hc s P g hP; rw [hseg, hta] at he; exact he.symm
    have hlt : (blockStage α).1 < (blockStage (α + 1)).1 :=
      Subtype.coe_lt_coe.mpr (blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl))
    obtain ⟨ub, Q, hroot, hub, hs, hagree⟩ :=
      FiniteCoverReceiving.finiteCoverReceiving_of_receiving hc' hr' P g tb p hface htb
        (ofOrd (blockStage α).1) (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr hlt)
    have hred : reduceType (blockStage α).2 (blockStage_le_succ α) Q =
        reduceType (blockStage α).2 (blockStage_le_succ α) P :=
      ext_of_scheme_label hs fun d => min_eq_min_iff_truncExt_eq.mp (hagree d)
    have hx : s (f (Fin.last k)) = x := by
      simpa only [Function.Embedding.trans_apply, snoc_apply_last] using
        congrArg (fun t : Fin (k + 1) ↪ M => t (Fin.last k)) hfs
    have hsource : (s : Fin l → M) ∘ (fun i => g (σ i)) = a :=
      funext fun i => (congrArg (fun t : Fin k ↪ M => t (σ i)) hseg).trans (congrFun ha i)
    have htarget : (ub : Fin l → N) ∘ (fun i => g (σ i)) = b :=
      funext fun i => (congrArg (fun t : Fin k ↪ N => t (σ i)) hroot).trans (congrFun hb i)
    exact ⟨ub (f (Fin.last k)), l, s, ub, Fin.snoc (fun i => g (σ i)) (f (Fin.last k)),
      reduceType (blockStage α).2 (blockStage_le_succ α) P,
      by rw [Realization.reduct_eval, hP]; rfl,
      by rw [Realization.reduct_eval, hub, ← hred]; rfl,
      by rw [Fin.comp_snoc, hsource, hx], by rw [Fin.comp_snoc, htarget]⟩

private theorem bfEquiv_of_commonChart_projected (α : Ordinal.{0}) {M N : Type w}
    (W : KnightRealization (blockStage α) M) (W' : KnightRealization (blockStage α) N)
    (hW : W.IsModel) (hW' : W'.IsModel) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hc : HasCommonChart W W' a b) :
    @BFEquiv (stageLang (blockStage 0)) M (stageStructureOf (W.reduct (blockStage_zero_le α)))
      N (stageStructureOf (W'.reduct (blockStage_zero_le α))) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    letI : (stageLang (blockStage 0)).Structure M := stageStructureOf (W.reduct (blockStage_zero_le 0))
    letI : (stageLang (blockStage 0)).Structure N := stageStructureOf (W'.reduct (blockStage_zero_le 0))
    exact (BFEquiv.zero a b).2 (sameAtomicType_of_commonChart
      (hW.consistent_reduct (blockStage_zero_le 0))
      (hW'.consistent_reduct (blockStage_zero_le 0))
      (lowerChart (blockStage_zero_le 0) hc))
  | add_one β ih =>
    letI : (stageLang (blockStage 0)).Structure M :=
      stageStructureOf (W.reduct (blockStage_zero_le (β + 1)))
    letI : (stageLang (blockStage 0)).Structure N :=
      stageStructureOf (W'.reduct (blockStage_zero_le (β + 1)))
    have hMβ : stageStructureOf ((W.reduct (blockStage_le_succ β)).reduct (blockStage_zero_le β)) =
        stageStructureOf (W.reduct (blockStage_zero_le (β + 1))) := by rw [Realization.reduct_reduct]
    have hNβ : stageStructureOf ((W'.reduct (blockStage_le_succ β)).reduct (blockStage_zero_le β)) =
        stageStructureOf (W'.reduct (blockStage_zero_le (β + 1))) := by rw [Realization.reduct_reduct]
    have hsucc := BFEquiv.succ (L := stageLang (blockStage 0)) β a b
    rw [Order.succ_eq_add_one] at hsucc
    refine hsucc.2 ⟨?_, fun x => ?_, fun y => ?_⟩
    · have h := ih (W.reduct (blockStage_le_succ β)) (W'.reduct (blockStage_le_succ β))
        (hW.reduct _) (hW'.reduct _) (lowerChart (blockStage_le_succ β) hc)
      rwa [hMβ, hNβ] at h
    · obtain ⟨y, hc'⟩ := extend_commonChart β W W' hW.consistent hW.isCovering
        hW'.consistent (OrdinaryModelReceiving.finiteCutReceiving hW') hc x
      refine ⟨y, ?_⟩
      have h := ih (W.reduct (blockStage_le_succ β)) (W'.reduct (blockStage_le_succ β))
        (hW.reduct _) (hW'.reduct _) hc'
      rwa [hMβ, hNβ] at h
    · obtain ⟨x, hc'⟩ := extend_commonChart β W' W hW'.consistent hW'.isCovering
        hW.consistent (OrdinaryModelReceiving.finiteCutReceiving hW) (reverseChart hc) y
      refine ⟨x, ?_⟩
      have h := ih (W.reduct (blockStage_le_succ β)) (W'.reduct (blockStage_le_succ β))
        (hW.reduct _) (hW'.reduct _) (reverseChart hc')
      rwa [hMβ, hNβ] at h
  | limit β hβ ih =>
    letI : (stageLang (blockStage 0)).Structure M :=
      stageStructureOf (W.reduct (blockStage_zero_le β))
    letI : (stageLang (blockStage 0)).Structure N :=
      stageStructureOf (W'.reduct (blockStage_zero_le β))
    refine (BFEquiv.limit β hβ a b).2 fun γ hγ => ?_
    have h := ih γ hγ (W.reduct (blockStage_mono hγ.le)) (W'.reduct (blockStage_mono hγ.le))
      (hW.reduct _) (hW'.reduct _) (lowerChart _ hc)
    rwa [Realization.reduct_reduct, Realization.reduct_reduct] at h

theorem bfEquiv_of_mem_domain {η : Ordinal.{0}} {R S : KnightNatModel}
    (hR : Quotient.mk knightModelSetoid R ∈ domain η)
    (hS : Quotient.mk knightModelSetoid S ∈ domain η) :
    @BFEquiv knightLang ℕ (structureOf R.1) ℕ (structureOf S.1) η 0 Fin.elim0 Fin.elim0 := by
  obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hR
  obtain ⟨V, hVm, hVr⟩ := exists_model_of_mem_domain hS
  obtain ⟨p, hp⟩ := exists_eval_empty_at hWm
  obtain ⟨p', hp'⟩ := exists_eval_empty_at hVm
  have hc : HasCommonChart W V (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → ℕ) :=
    ⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, Fin.elim0, p, hp,
      by rw [hp', Subsingleton.elim p' p], funext fun i => i.elim0, funext fun i => i.elim0⟩
  have htr : ∀ {δ ε : LimitStage}, δ = ε → ∀ (hδ : δ ≤ blockStage η) (hε : ε ≤ blockStage η),
      @BFEquiv (stageLang δ) ℕ (stageStructureOf (W.reduct hδ)) ℕ (stageStructureOf (V.reduct hδ))
        η 0 Fin.elim0 Fin.elim0 ↔
      @BFEquiv (stageLang ε) ℕ (stageStructureOf (W.reduct hε)) ℕ (stageStructureOf (V.reduct hε))
        η 0 Fin.elim0 Fin.elim0
    | _, _, rfl, _, _ => Iff.rfl
  have h := (htr blockStage_zero (blockStage_zero_le η) (omegaStage_le _)).mp
    (bfEquiv_of_commonChart_projected η W V hWm hVm hc)
  change @BFEquiv knightLang ℕ (structureOf (W.reduct (omegaStage_le _)))
    ℕ (structureOf (V.reduct (omegaStage_le _))) η 0 Fin.elim0 Fin.elim0 at h
  rwa [reduct_omegaStage_eq hWr, reduct_omegaStage_eq hVr] at h

theorem mk_bfEquivSetoid_quotient_le_aleph0 (hct : CountableTerminalFibres)
    {η : Ordinal.{0}} (hη : η < (aleph 1).ord) :
    #(Quotient (bfEquivSetoid knightSentence η)) ≤ ℵ₀ := by
  let π : Classes → Quotient (bfEquivSetoid knightSentence η) :=
    fun q => bfProj knightSentence η (isoClassEquiv.symm q)
  have hπ (c : ModelsOf knightSentence) : π (modelClass c) = Quotient.mk _ c := by
    change bfProj knightSentence η (isoClassEquiv.symm (isoClassEquiv _)) = _
    rw [Equiv.symm_apply_apply, bfProj_mk]
  have hcover : (Set.univ : Set (Quotient (bfEquivSetoid knightSentence η))) ⊆
      π '' (domain η)ᶜ ∪ π '' domain η := by
    rintro x -; induction x using Quotient.inductionOn with
    | h c =>
      by_cases hc : modelClass c ∈ domain η
      · exact Or.inr ⟨_, hc, hπ c⟩
      · exact Or.inl ⟨_, hc, hπ c⟩
  have hsub : (π '' domain η).Subsingleton := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨s, hs, rfl⟩
    obtain ⟨c, rfl⟩ := modelClass_surjective q
    obtain ⟨d, rfl⟩ := modelClass_surjective s
    rw [hπ, hπ]; apply Quotient.sound
    have h := bfEquiv_of_mem_domain (R := realizationOfCode c) (S := realizationOfCode d) hq hs
    have hc' := @equiv_implies_BFEquiv knightLang ℕ ℕ c.1.toStructure
      (structureOf (realizationOfCode c).1)
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf (realizationOfCode c).1)
        c.1.toStructure (isKnightModel_of_mem c).structureOfToRealizationEquiv) η 0 Fin.elim0
    have hd' := @equiv_implies_BFEquiv knightLang ℕ ℕ (structureOf (realizationOfCode d).1)
      d.1.toStructure (isKnightModel_of_mem d).structureOfToRealizationEquiv η 0 Fin.elim0
    rw [comp_fin_elim0] at hc' hd'
    exact @BFEquiv.trans knightLang ℕ c.1.toStructure ℕ (structureOf (realizationOfCode d).1)
      ℕ d.1.toStructure (n := 0) (α := η) (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0)
      (@BFEquiv.trans knightLang ℕ c.1.toStructure ℕ (structureOf (realizationOfCode c).1)
        ℕ (structureOf (realizationOfCode d).1) (n := 0) (α := η)
        (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0) hc' h) hd'
  exact mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp
    ((((compl_countable hct hη).image π).union hsub.countable).mono hcover))

end
end VaughtConjecture.Knight.ExpansionDomain
