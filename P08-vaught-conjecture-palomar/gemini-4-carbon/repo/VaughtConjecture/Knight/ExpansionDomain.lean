/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.CountableLoss
public import VaughtConjecture.Knight.Rank
public import VaughtConjecture.Knight.LimitOfChain
public import VaughtConjecture.Knight.ExpansionInjectivity
public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.CountableTerminalFibres
public import VaughtConjecture.Knight.ClassTruth
public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.ModelEmpty
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.Sentence
public import VaughtConjecture.Knight.VisibleFaceOneStep
public import InfinitaryLogic.Lomega1omega.QuantifierRank
public import PalomarProof.Infinitary.QuantifierRank

@[expose] public section

namespace FirstOrder.Language.BoundedFormulaInf
universe u v u' u'' uι w
variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {β : Type u''}

def relabelFree (g : α → β) : ∀ {n : ℕ}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf ι β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map g id)) (t₂.relabel (Sum.map g id))
  | _, .rel R ts => .rel R fun i => (ts i).relabel (Sum.map g id)
  | _, .imp φ ψ => .imp (relabelFree g φ) (relabelFree g ψ)
  | _, .all φ => .all (relabelFree g φ)
  | _, .iSup φs => .iSup fun i => relabelFree g (φs i)
  | _, .iInf φs => .iInf fun i => relabelFree g (φs i)

theorem realize_relabelFree {M : Type w} [L.Structure M] (g : α → β) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (v : β → M) (xs : Fin n → M),
      (relabelFree g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    change (t₁.relabel _).realize _ = (t₂.relabel _).realize _ ↔ t₁.realize _ = t₂.realize _
    rw [Term.realize_relabel, Term.realize_relabel, Sum.elim_comp_map]; rfl
  | rel R ts =>
    intro v xs
    change Structure.RelMap R (fun i => ((ts i).relabel _).realize _) ↔ Structure.RelMap R _
    simp only [Term.realize_relabel, Sum.elim_comp_map]; rfl
  | imp _ _ ihφ ihψ => exact fun v xs => imp_congr (ihφ v xs) (ihψ v xs)
  | all _ ih => exact fun v xs => forall_congr' fun y => ih v (Fin.snoc xs y)
  | iSup _ ih => exact fun v xs => exists_congr fun i => ih i v xs
  | iInf _ ih => exact fun v xs => forall_congr' fun i => ih i v xs

theorem qrank_relabelFree (g : α → β) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ι α n), (relabelFree g φ).qrank = φ.qrank := by
  intro n φ
  induction φ with
  | falsum | equal _ _ | rel _ _ => rfl
  | imp _ _ ihφ ihψ => change max _ _ = max _ _; rw [ihφ, ihψ]
  | all _ ih => change Order.succ _ = Order.succ _; rw [ih]
  | iSup _ ih | iInf _ ih => exact iSup_congr ih
end FirstOrder.Language.BoundedFormulaInf

namespace VaughtConjecture.Knight
open TypeTower FirstOrder Language Cardinal KnightRealization StoppingRankFiltration
universe w u v u'

theorem qrank_lt_ord_aleph_one {L : Language.{u, v}} {γ : Type u'} :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ℕ γ n), φ.qrank < (aleph 1).ord :=
  fun φ => by simpa only [Cardinal.ord_aleph] using BoundedFormulaω.qrank_lt_omega1 φ

private noncomputable def cofSeq (g : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | n + 1 => max (cofSeq g n) (g n)

private theorem exists_model_at_limit_of_forall_lt {M : Type w} {l : Ordinal.{0}}
    (hlim : Order.IsSuccLimit l) (hl : l < (aleph 1).ord)
    {R : KnightRealization (blockStage 0) M}
    (h : ∀ ξ, ξ < l → ∃ W : KnightRealization (blockStage ξ) M,
      W.IsModel ∧ W.reduct (blockStage_zero_le ξ) = R) :
    ∃ W : KnightRealization (blockStage l) M,
      W.IsModel ∧ W.reduct (blockStage_zero_le l) = R := by
  have h0 : (0 : Ordinal.{0}) < l := hlim.pos
  have hmk : Cardinal.mk (Set.Iio l) ≤ Cardinal.aleph0 := by
    rw [Cardinal.mk_Iio_ordinal]
    exact Cardinal.lift_le_aleph0.mpr (Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_ord.mp hl))
  haveI : Countable (Set.Iio l) := Cardinal.mk_le_aleph0_iff.mp hmk
  haveI : Nonempty (Set.Iio l) := ⟨⟨0, h0⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (Set.Iio l)
  let g (n : ℕ) : Ordinal.{0} := (f n).1
  have hcs_lt (n : ℕ) : cofSeq g n < l := by
    induction n with
    | zero => exact h0
    | succ n ih => exact max_lt ih (f n).2
  have hmono : Monotone (cofSeq g) := monotone_nat_of_le_succ fun _ => le_max_left _ _
  let W (n : ℕ) : KnightRealization (blockStage (cofSeq g n)) M := (h _ (hcs_lt n)).choose
  have hWm (n : ℕ) : (W n).IsModel := (h _ (hcs_lt n)).choose_spec.1
  have hWr (n : ℕ) : (W n).reduct (blockStage_zero_le (cofSeq g n)) = R :=
    (h _ (hcs_lt n)).choose_spec.2
  have hc : Monotone fun n => blockStage (cofSeq g n) := fun _ _ hij => blockStage_mono (hmono hij)
  have hchain : IsReductChain hc W := fun i j hij =>
    eq_of_reduct_eq_of_le (cofSeq g i) 0 zero_le _ _ ((hWm j).reduct _) (hWm i)
      (by rw [Realization.reduct_reduct, hWr j, hWr i])
  have hδ (i : ℕ) : blockStage (cofSeq g i) ≤ blockStage l := blockStage_mono (hcs_lt i).le
  have hcof (γ : Ordinal.{0}) (hγ : γ < (blockStage l).1) :
      ∃ i, γ < (blockStage (cofSeq g i)).1 := by
    by_cases hω : γ < Ordinal.omega0
    · exact ⟨0, hω.trans_le (le_add_right le_rfl)⟩
    · have hsub : Ordinal.omega0 + (γ - Ordinal.omega0) = γ :=
        Ordinal.add_sub_cancel_of_le (not_lt.mp hω)
      obtain ⟨x, hx, hltx⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hlim).mp
        ((add_lt_add_iff_left _).mp (hsub.symm ▸ hγ))
      have hx1 : x + 1 < l := Order.succ_eq_add_one x ▸ hlim.succ_lt hx
      obtain ⟨n, hn⟩ := hf ⟨x + 1, hx1⟩
      have hgn : g n = x + 1 := congrArg Subtype.val hn
      have hxn : x < cofSeq g (n + 1) :=
        lt_of_lt_of_le (lt_add_one x) (hgn ▸ le_max_right (cofSeq g n) (g n))
      exact ⟨n + 1, hsub ▸ (add_lt_add_iff_left _).mpr
        (hltx.trans_le (mul_le_mul_right hxn.le Ordinal.omega0))⟩
  refine ⟨limitOfChain hc W hchain (blockStage l) hδ,
    IsModel.limitOfChain hc hchain hWm (blockStage l) hδ hcof, ?_⟩
  rw [← Realization.reduct_reduct (blockStage_zero_le (cofSeq g 0)) (hδ 0),
    reduct_limitOfChain, hWr 0]

namespace ExpansionDomain

def domain (ξ : Ordinal.{0}) : Set Classes :=
  {q | Quotient.lift
    (fun R : KnightNatModel => R.atBlockZero.ProlongsToIn IsModelClass (blockStage_zero_le ξ))
    (fun _ _ h => propext (Realization.prolongsToIn_iff_of_iso
      (KnightNatModel.iso_atBlockZero (knightModelSetoid_r_iff.mp h)) _)) q}

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

theorem domain_zero : domain 0 = Set.univ := by
  ext q; refine ⟨fun _ => trivial, fun _ => ?_⟩
  induction q using Quotient.inductionOn with
  | h R =>
    exact mem_domain_of_model (R := R) (R.2.reduct blockStage_zero_le_omegaStage)
      (Realization.reduct_refl _)

theorem domain_antitone : Antitone domain := by
  intro ξ η hξη q hq
  induction q using Quotient.inductionOn with
  | h _ => exact Realization.ProlongsToIn.mono isModelClass_reduct (blockStage_mono hξη) hq

theorem loss_subset_range (ξ : Ordinal.{0}) :
    domain ξ \ domain (ξ + 1) ⊆ Set.range (terminalToClass ξ) := by
  rintro q ⟨hq, hq'⟩
  induction q using Quotient.inductionOn with
  | h R =>
    obtain ⟨W, hWm, hWr⟩ := exists_model_of_mem_domain hq
    have hterm : W.NoProlongationToIn IsModelClass (blockStage_le_succ ξ) := fun hprol => by
      obtain ⟨V, hVm, hVr⟩ := (prolongsToIn_isModelClass_iff_on W (blockStage_le_succ ξ)).mp hprol
      exact hq' (mem_domain_of_model hVm
        (by rw [← Realization.reduct_reduct (blockStage_zero_le ξ) (blockStage_le_succ ξ) V, hVr, hWr]))
    refine ⟨Quotient.mk _ ⟨W, hWm, hterm⟩, congrArg (Quotient.mk knightModelSetoid) (Subtype.ext ?_)⟩
    change liftBlockZero (W.reduct (blockStage_zero_le ξ)) = R.1
    rw [hWr]; exact liftBlockZero_reduct R.1

theorem loss_countable (hct : CountableTerminalFibres) {ξ : Ordinal.{0}}
    (hξ : ξ < (aleph 1).ord) : (domain ξ \ domain (ξ + 1)).Countable :=
  have : Countable (TerminalClass ξ) := Cardinal.mk_le_aleph0_iff.mp (hct ξ hξ)
  (Set.countable_range _).mono (loss_subset_range ξ)

theorem iInter_subset_domain {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hlω : l < (aleph 1).ord) : (⋂ ξ < l, domain ξ) ⊆ domain l := by
  intro q hq
  induction q using Quotient.inductionOn with
  | h R =>
    obtain ⟨W, hWm, hWr⟩ := exists_model_at_limit_of_forall_lt hl hlω (R := R.atBlockZero)
      fun ξ hξ => exists_model_of_mem_domain (Set.mem_iInter₂.mp hq ξ hξ)
    exact mem_domain_of_model hWm hWr

theorem compl_countable (hct : CountableTerminalFibres) {β : Ordinal.{0}}
    (hβ : β < (aleph 1).ord) : (domain β)ᶜ.Countable :=
  CountableLoss.compl_countable_of_loss domain domain_zero
    (fun _ hξ => loss_countable hct hξ) (fun _ hl hlω => iInter_subset_domain hl hlω) β hβ

theorem reduct_omegaStage_eq {ξ : Ordinal.{0}} {R : KnightNatModel}
    {W : KnightRealization (blockStage ξ) ℕ}
    (hWr : W.reduct (blockStage_zero_le ξ) = R.atBlockZero) :
    W.reduct (omegaStage_le _) = R.1 := by
  rw [← Realization.reduct_reduct omegaStage_le_blockStage_zero (blockStage_zero_le ξ) W, hWr]
  exact liftBlockZero_reduct R.1

end ExpansionDomain
end VaughtConjecture.Knight
