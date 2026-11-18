/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.BFScattered
public import InfinitaryLogic.Descriptive.ScottDefinability
public import VaughtConjecture.CountableLoss
public import VaughtConjecture.Knight.ClassPresentation
public import VaughtConjecture.Knight.ExpansionDomainBF
public import VaughtConjecture.Knight.ConstructedTerminalCountability
public import VaughtConjecture.Knight.ConstructedTerminalLoss

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomainEndpoint

open FirstOrder Language Cardinal Set TypeTower KnightRealization Spectrum
open StoppingRankFiltration ExpansionDomain

theorem isThinOnNatModels : knightSentence.IsThinOnNatModels := by
  apply FirstOrder.Language.isThinOn_of_countable_bfObservations (ModelsOf knightSentence)
    (fun η => Quotient.mk (bfEquivSetoid knightSentence η))
  · intro η hη
    have : Countable (Quotient (bfEquivSetoid knightSentence η)) :=
      mk_le_aleph0_iff.mp (mk_bfEquivSetoid_quotient_le_aleph0
        ConstructedSpectrumEndpoint.countableTerminalFibres (by rwa [ord_aleph]))
    exact Set.to_countable _
  · exact fun _ _ _ _ h => Quotient.exact h

private theorem aleph_one_le_mk_of_cofinal (T : Set Ordinal.{0})
    (hT : ∀ ξ ∈ T, ξ < (aleph 1).ord)
    (hcof : ∀ η, η < (aleph 1).ord → ∃ ξ ∈ T, η ≤ ξ) : aleph 1 ≤ #T := by
  by_contra h
  have hcount : Countable T :=
    Cardinal.mk_le_aleph0_iff.mp (Cardinal.lt_aleph_one_iff.mp (not_le.mp h))
  have hlim := Cardinal.isSuccLimit_ord (aleph0_le_aleph 1)
  obtain ⟨ξ₀, hξ₀, -⟩ := hcof 0 hlim.pos
  have : Nonempty T := ⟨⟨ξ₀, hξ₀⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat T
  have hsup : iSup (fun n => (e n).1) < (aleph 1).ord :=
    Ordinal.iSup_lt_of_lt_cof
      (by rw [Cardinal.mk_nat, Cardinal.isRegular_aleph_one.cof_ord]; exact aleph0_lt_aleph_one)
      fun n => hT _ (e n).2
  obtain ⟨ξ, hξT, hle⟩ := hcof _ (hlim.succ_lt hsup)
  obtain ⟨n, hn⟩ := he ⟨ξ, hξT⟩
  have hbdd : BddAbove (Set.range fun n => (e n).1) :=
    ⟨(aleph 1).ord, by rintro _ ⟨m, rfl⟩; exact (hT _ (e m).2).le⟩
  have hle' : (e n).1 ≤ iSup fun n => (e n).1 := le_ciSup hbdd n
  rw [hn] at hle'
  exact absurd (hle.trans hle') (not_le.mpr (Order.lt_succ _))

theorem natModelSpectrum_eq_aleph_one : natModelSpectrum knightSentence = aleph 1 := by
  rw [natModelSpectrum_knightSentence]
  have hct := ConstructedSpectrumEndpoint.countableTerminalFibres
  have hcompl : ∀ β < (aleph 1).ord, (domain β)ᶜ.Countable := fun β hβ =>
    CountableLoss.compl_countable_of_loss domain domain_zero (fun _ h => loss_countable hct h)
      (fun _ hl h => iInter_subset_domain hl h) β hβ
  have hcore : (⋂ β < (aleph 1).ord, domain β).Countable := by
    apply Set.Subsingleton.countable
    intro p hp q hq
    obtain ⟨φ, hφ⟩ := isolatedPresentation_of_surjective (fun c : ModelsOf knightSentence => c.1)
      modelClass modelClass_surjective (fun _ _ h => modelClass_eq_of_iso h)
      realizes realizes_modelClass p
    have hqrank := qrank_lt_ord_aleph_one φ
    have hp' := Set.mem_iInter₂.mp hp φ.qrank hqrank
    have hq' := Set.mem_iInter₂.mp hq φ.qrank hqrank
    have hhom : realizes φ p ↔ realizes φ q := by
      revert hp' hq'
      refine Quotient.inductionOn₂ p q fun R S hR hS => ?_
      have key := @BFEquiv_implies_agreeQR knightLang ℕ inferInstance ℕ ℕ
        (structureOf R.1) (structureOf S.1) φ.qrank 0 Fin.elim0 Fin.elim0
        (bfEquiv_of_mem_domain hR hS) (φ.relabelFree (Empty.elim : Empty → Fin 0))
        (by rw [BoundedFormulaInf.qrank_relabelFree])
      have he : (Fin.elim0 : Fin 0 → ℕ) ∘ (Empty.elim : Empty → Fin 0) = Empty.elim :=
        funext fun e => e.elim
      simp only [FormulaInf.Realize, BoundedFormulaInf.realize_relabelFree, he] at key
      exact key
    exact ((hφ q).mp (hhom.mp ((hφ p).mpr rfl))).symm
  apply le_antisymm
  · have hcov : (Set.univ : Set Classes) = (⋂ β < (aleph 1).ord, domain β) ∪
        ⋃ β ∈ Set.Iio (aleph 1).ord, (domain β)ᶜ := by
      ext x
      simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_iInter, Set.mem_iUnion,
        Set.mem_compl_iff, Set.mem_Iio]
      by_cases h : ∀ β < (aleph 1).ord, x ∈ domain β
      · exact Or.inl h
      · push Not at h; obtain ⟨β, hβ, hx⟩ := h; exact Or.inr ⟨β, hβ, hx⟩
    calc #Classes = #(Set.univ : Set Classes) := Cardinal.mk_univ.symm
      _ ≤ #(⋂ β < (aleph 1).ord, domain β : Set Classes) +
          #(⋃ β ∈ Set.Iio (aleph 1).ord, (domain β)ᶜ : Set Classes) := by
            rw [hcov]; exact Cardinal.mk_union_le _ _
      _ ≤ aleph 1 + aleph 1 := by
          gcongr
          · exact (Cardinal.le_aleph0_iff_set_countable.mpr hcore).trans aleph0_lt_aleph_one.le
          · calc #(⋃ β ∈ Set.Iio (aleph 1).ord, (domain β)ᶜ : Set Classes)
                ≤ #(Set.Iio (aleph 1).ord) *
                    ⨆ β : Set.Iio (aleph 1).ord, #((domain β.1)ᶜ : Set Classes) :=
                  Cardinal.mk_biUnion_le _ _
              _ ≤ aleph 1 * aleph 1 := by
                  rw [CountableLoss.mk_Iio_ord_aleph_one]
                  gcongr
                  exact ciSup_le' fun β =>
                    (Cardinal.le_aleph0_iff_set_countable.mpr (hcompl β.1 β.2)).trans
                      aleph0_lt_aleph_one.le
              _ = aleph 1 := by simp only [Cardinal.aleph_mul_aleph, max_self]
      _ = aleph 1 := by simp only [Cardinal.aleph_add_aleph, max_self]
  · classical
    let T : Set Ordinal.{0} := {ξ | ξ < (aleph 1).ord ∧ (domain ξ \ domain (ξ + 1)).Nonempty}
    let pick : T → Classes := fun ξ => ξ.2.2.some
    have hpick : ∀ ξ : T, pick ξ ∈ domain ξ.1 \ domain (ξ.1 + 1) := fun ξ => ξ.2.2.some_mem
    have hinj : Function.Injective pick := fun ξ ζ hξζ => by
      by_contra hne
      rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hne) with hlt | hlt
      · exact (hpick ξ).2 (hξζ ▸ domain_antitone (Order.add_one_le_iff.mpr hlt) (hpick ζ).1)
      · exact (hpick ζ).2 (hξζ.symm ▸ domain_antitone (Order.add_one_le_iff.mpr hlt) (hpick ξ).1)
    exact (aleph_one_le_mk_of_cofinal T (fun _ h => h.1) fun η hη => by
      obtain ⟨ξ, hηξ, hξ, hne⟩ := cofinal_losses η hη
      exact ⟨ξ, ⟨hξ, hne⟩, hηξ⟩).trans (Cardinal.mk_le_of_injective hinj)

end VaughtConjecture.Knight.ExpansionDomainEndpoint
