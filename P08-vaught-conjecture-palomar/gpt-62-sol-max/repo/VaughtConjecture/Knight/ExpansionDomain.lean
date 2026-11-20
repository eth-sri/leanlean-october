/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.OrdinalCountability
public import VaughtConjecture.Knight.LimitExpansion
public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.CountableTerminalFibres
public import VaughtConjecture.Knight.ClassTruth
public import VaughtConjecture.Knight.OneBlockComparison

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomain

open TypeTower FirstOrder Language KnightRealization Cardinal StoppingRankFiltration

/-- **The expansion domain at block `ξ`**: the counted classes admitting a model expansion
to `blockStage ξ` (up to isomorphism; on the counted carrier by normalization). -/
def domain (ξ : Ordinal.{0}) : Set Classes :=
  {q | Quotient.lift
    (fun R : KnightNatModel => R.atBlockZero.ProlongsToIn IsModelClass (blockStage_zero_le ξ))
    (fun _ _ h => propext (Realization.prolongsToIn_iff_of_iso
      (KnightNatModel.iso_atBlockZero (knightModelSetoid_r_iff.mp h)) _)) q}

/-- Membership normalizes to an actual model on the counted carrier. -/
theorem exists_model_of_mem_domain {ξ : Ordinal.{0}} {R : KnightNatModel}
    (h : Quotient.mk knightModelSetoid R ∈ domain ξ) :
    ∃ W : KnightRealization (blockStage ξ) ℕ,
      W.IsModel ∧ W.reduct (blockStage_zero_le ξ) = R.atBlockZero :=
  (prolongsToIn_isModelClass_iff_on _ _).mp h

theorem mem_domain_of_model {ξ : Ordinal.{0}} {R : KnightNatModel}
    {W : KnightRealization (blockStage ξ) ℕ} (hW : W.IsModel)
    (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
    Quotient.mk knightModelSetoid R ∈ domain ξ :=
  Realization.ProlongsToOnIn.prolongsToIn ⟨W, hW, hWr⟩

/-- Every class expands to block `0`. -/
theorem domain_zero : domain 0 = Set.univ := by
  ext q
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  induction q using Quotient.inductionOn with
  | h R =>
    exact mem_domain_of_model (R := R) (R.2.reduct blockStage_zero_le_omegaStage)
      (Realization.reduct_refl _)

/-- **Expansion domains decrease**: an expansion to a higher block reduces to a lower one. -/
theorem domain_antitone : Antitone domain := by
  intro ξ η hξη q hq
  induction q using Quotient.inductionOn with
  | h R =>
    exact Realization.ProlongsToIn.mono isModelClass_reduct (blockStage_mono hξη) hq

/-- A class lost at the next block is the class of a terminal model at this block. -/
theorem loss_subset_range (ξ : Ordinal.{0}) :
    domain ξ \ domain (ξ + 1) ⊆ Set.range (terminalToClass ξ) := by
  rintro q ⟨hq, hq'⟩
  induction q using Quotient.inductionOn with
  | h R =>
    obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
    have hterm : W.NoProlongationToIn IsModelClass (blockStage_le_succ ξ) := by
      intro hprol
      obtain ⟨V, hVm, hVr⟩ :=
        (prolongsToIn_isModelClass_iff_on W (blockStage_le_succ ξ)).mp hprol
      refine hq' (mem_domain_of_model hVm ?_)
      rw [← Realization.reduct_reduct (blockStage_zero_le ξ) (blockStage_le_succ ξ) V, hVr,
        hWr]
    refine ⟨Quotient.mk _ ⟨W, hWm, hterm⟩, ?_⟩
    change Quotient.mk knightModelSetoid (TerminalModel.toNatModel ⟨W, hWm, hterm⟩) =
      Quotient.mk knightModelSetoid R
    congr 1
    apply Subtype.ext
    change liftBlockZero (W.reduct (blockStage_zero_le ξ)) = R.1
    rw [hWr]
    exact liftBlockZero_reduct R.1

/-- **Successor losses are countable**, given countable terminal fibres. -/
theorem loss_countable (hct : CountableTerminalFibres) {ξ : Ordinal.{0}}
    (hξ : ξ < (aleph 1).ord) : (domain ξ \ domain (ξ + 1)).Countable :=
  have : Countable (TerminalClass ξ) := Cardinal.mk_le_aleph0_iff.mp (hct ξ hξ)
  (Set.countable_range _).mono (loss_subset_range ξ)

/-- **No loss at a countable limit**: the countable-limit expansion theorem. -/
theorem iInter_subset_domain {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hlω : l < (aleph 1).ord) : (⋂ ξ < l, domain ξ) ⊆ domain l := by
  intro q hq
  induction q using Quotient.inductionOn with
  | h R =>
    obtain ⟨W, hWm, hWr⟩ := exists_model_at_limit_of_forall_lt hl hlω (R := R.atBlockZero)
      fun ξ hξ => exists_model_of_mem_domain (Set.mem_iInter₂.mp hq ξ hξ)
    exact mem_domain_of_model hWm hWr

/-- **Fixed-stage complements are countable.** -/
theorem compl_countable (hct : CountableTerminalFibres) {β : Ordinal.{0}}
    (hβ : β < (aleph 1).ord) : (domain β)ᶜ.Countable :=
  InfinitaryLogic.compl_countable_of_loss domain domain_zero
    (fun _ hξ => loss_countable hct hξ) (fun _ hl hlω => iInter_subset_domain hl hlω) β hβ

theorem reduct_omegaStage_eq {ξ : Ordinal.{0}} {R : KnightNatModel}
    {W : KnightRealization (blockStage ξ) ℕ}
    (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
    W.reduct (omegaStage_le _) = R.1 := by
  rw [← Realization.reduct_reduct omegaStage_le_blockStage_zero (blockStage_zero_le ξ) W, hWr]
  exact liftBlockZero_reduct R.1

end VaughtConjecture.Knight.ExpansionDomain
