/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryRawScope
public import VaughtConjecture.Knight.OrderedScopeObligations

/-! # Coherent iteration of ordinary proper scopes

The state records already completed targets. The successor derives the raw
local producer's premises from those targets, constructs its rows, and installs
them in the same ambient inventory. No local operator is an input to the step.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.OrdinaryScopeIteration
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension SourcePrefixRows OrbitPrefixSupport
section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}
  (sem₀ : Semantics D₀) (F₀ : Finset (Finset ι)) (N : ℕ)
  (G : Finset ExtOrd) (θ : ExtOrd)

/-- An actual partial carrier, its completed-target ledger, and its renderer.
`initial`, `step`, and finite iteration below construct these records. -/
structure State (F : Finset (Finset ι)) where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = D₀.plan
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  original : Cell D₀ ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = D₀.cell d
  row : ∀ (c : Cell D₀) (d : D₀.below (D₀.cell c)),
    rows.E (original c) ⟨original d.1, by rw [index, index]; exact d.2⟩ = sem₀.E c d
  exhaustive : ∀ d, carrier.scope d ∈ F₀ → ∃ c, original c = d
  occupied : ∀ d, carrier.scope d ∈ F
  initial_le : F₀ ⊆ F
  scopes : F ⊆ D₀.plan
  proper : A ∉ F
  closed : ∀ B ∈ F, ∀ C ∈ D₀.plan, C ⊆ B → C ∈ F
  complete : ∀ J ∈ Plan.gradedPlan D₀.plan, J.1 ∈ F → ∃ d, carrier.cell d = J
  lifts : ∀ I J, I ∈ Plan.gradedPlan D₀.plan → J ∈ Plan.gradedPlan D₀.plan → J.1 ∈ F →
    (h : GradedLe I J) → CappedLift rows h
  classification : OrderedScopeRelocation.OwnerClassification rows original
  mute : ∀ c, carrier.grade c = (carrier.scope c).card → carrier.scope c ∉ F₀ →
    rows.E c ⟨c, GradedLe.refl _⟩ = ⊥
  render : ∀ {p : Cell D₀ → ExtOrd}, RespectsSemantics sem₀ p → (∀ d, p d ≤ θ) →
    Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) d,
    render hp hb (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ),
    RespectsSemantics rows (render hp hb)
  bound : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) d, render hp hb d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) d,
    Supported N (G : Set ExtOrd) p (render hp hb d)
  agreement : ∀ {p q} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ)
    (hq : RespectsSemantics sem₀ q) (hqb : ∀ d, q d ≤ θ) {γ}, γ ∈ G → γ ≤ θ →
    Agree p q γ → Agree (render hp hb) (render hq hqb) γ

end

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (F₀ : Finset (Finset ι)) (N : ℕ) (G : Finset ExtOrd) (θ : ExtOrd)

def initial (hs : sem.IsConsistent) (hc : sem.IsCoded)
    (hocc : ∀ d, D.scope d ∈ F₀) (hscopes : F₀ ⊆ D.plan) (hproper : A ∉ F₀)
    (hclosed : ∀ B ∈ F₀, ∀ C ∈ D.plan, C ⊆ B → C ∈ F₀)
    (hcomplete : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ∈ F₀ → ∃ d, D.cell d = J)
    (hlift : ∀ I J, I ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan → J.1 ∈ F₀ →
      (h : GradedLe I J) → CappedLift sem h) : State sem F₀ N G θ F₀ where
  carrier := D
  rows := sem
  plan := rfl
  consistent := hs
  coded := hc
  original := (OrderIso.refl (Cell D)).toOrderEmbedding
  index _ := rfl
  row _ _ := rfl
  exhaustive d _ := ⟨d, rfl⟩
  occupied := hocc
  initial_le := Finset.Subset.refl _
  scopes := hscopes
  proper := hproper
  closed := hclosed
  complete := hcomplete
  lifts := hlift
  classification := OrderedScopeRelocation.ownerClassification_initial sem
  mute c _ hn := (hn (hocc c)).elim
  render {p} _ _ := p
  readback _ _ _ := rfl
  lawful hp _ := hp
  bound _ hb := hb
  support _ _ := supported_field N (G : Set ExtOrd) _
  agreement := by intro _ _ _ _ _ _ _ _ _ he; exact he

variable {sem F₀ N G θ}

open OrderedScopeRelocation in
theorem exists_completed
    (hN : ∀ B ∈ D.plan, B ≠ A → B.card ≤ N)
    (hsmall : ∀ B ∈ D.plan, B.card ≤ 1 → B ∈ F₀)
    (hG : ∀ z ∈ G, SelfVis N z) (hθ : SelfVis N θ) (htθ : θ ≠ ⊤) (hθG : θ ∈ G)
    {F : Finset (Finset ι)} (X : State sem F₀ N G θ F) :
    ∃ F', Nonempty (State sem F₀ N G θ F') ∧ ∀ B ∈ D.plan, B ≠ A → B ∈ F' := by
  classical
  suffices ∀ n (F : Finset (Finset ι)), (D.plan \ insert A F).card = n →
      State sem F₀ N G θ F →
      ∃ F', Nonempty (State sem F₀ N G θ F') ∧ ∀ B ∈ D.plan, B ≠ A → B ∈ F' from
    this _ F rfl X
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn X
    by_cases hempty : (D.plan \ insert A F).Nonempty
    · obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image (D.plan \ insert A F) Finset.card hempty
      have hBp := (Finset.mem_sdiff.mp hB).1
      have hBA : B ≠ A := fun he => (Finset.mem_sdiff.mp hB).2 (he ▸ Finset.mem_insert_self A F)
      have hnew : B ∉ F := fun hf => (Finset.mem_sdiff.mp hB).2 (Finset.mem_insert_of_mem hf)
      have hready (C) (hC : C ∈ D.plan) (hCB : C ⊂ B) : C ∈ F := by
        by_contra hc
        have hCA : C ≠ A := fun he => by
          have := Finset.card_lt_card hCB
          have := Finset.card_le_card (D.isPlan.subset_of_mem hBp)
          subst C; omega
        exact (not_le_of_gt (Finset.card_lt_card hCB))
          (hmin C (Finset.mem_sdiff.mpr ⟨hC, by simp only [Finset.mem_insert, not_or]; exact ⟨hCA, hc⟩⟩))
      have htwo : 2 ≤ B.card := by
        by_contra hh; exact hnew (X.initial_le (hsmall B hBp (by omega)))
      let k := B.card - 1
      have hk : 0 < k := by dsimp [k]; omega
      have hcard : B.card = k + 1 := by dsimp [k]; omega
      have hBN : k + 1 ≤ N := hcard ▸ hN B hBp hBA
      have hBX : B ∈ X.carrier.plan := X.plan.symm ▸ hBp
      have sep : Separated (D := X.carrier) (B := B) :=
        fun d hd => hnew (X.closed _ (X.occupied d) B hBp hd)
      let rRows := ScopeBoundary.rows X.carrier B hBX X.rows
      have hrdy : OrdinaryRawScope.Ready rRows := {
        proper := fun d he => sep (ScopeBoundary.toCell X.carrier B hBX d) (subset_of_eq he.symm)
        consistent := ScopeBoundary.consistent _ _ _ _ X.consistent
        coded := ScopeBoundary.coded _ _ _ _ X.coded
        complete := fun J hJ hJB => by
          have hm := Plan.mem_gradedPlan.mp hJ
          have hmem : J.1 ∈ D.plan := X.plan ▸ (Finset.mem_inter.mp hm.1).1
          have hsub := Finset.mem_powerset.mp (Finset.mem_inter.mp hm.1).2
          obtain ⟨d, hd⟩ := X.complete J (Plan.mem_gradedPlan.mpr ⟨hmem, hm.2⟩)
            (hready J.1 hmem (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJB⟩))
          obtain ⟨e, he⟩ := ScopeBoundary.exhaustive X.carrier B hBX
            (by change (X.carrier.cell d).1 ⊆ B; rwa [hd])
          exact ⟨e, (congrArg X.carrier.cell he).trans hd⟩
        lifts := fun I J hI hJ hJB h => by
          have hm := Plan.mem_gradedPlan.mp hJ
          have hmem : J.1 ∈ D.plan := X.plan ▸ (Finset.mem_inter.mp hm.1).1
          have hsub := Finset.mem_powerset.mp (Finset.mem_inter.mp hm.1).2
          have hi := Plan.mem_gradedPlan.mp hI
          have hb := X.lifts I J (Plan.mem_gradedPlan.mpr ⟨X.plan ▸ (Finset.mem_inter.mp hi.1).1, hi.2⟩)
            (Plan.mem_gradedPlan.mpr ⟨hmem, hm.2⟩)
            (hready J.1 hmem (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJB⟩)) h
          exact bountiful_of_equiv h h
            (ScopeBoundary.belowEquiv X.carrier B hBX J hsub)
            (ScopeBoundary.belowEquiv X.carrier B hBX I (h.1.trans hsub))
            (fun _ => rfl) (ScopeBoundary.respects_iff _ _ _ _ _ _)
            (ScopeBoundary.respects_iff _ _ _ _ _ _) hb rfl }
      let raw := OrdinaryRawScope.build _ hrdy k hk hcard
      let L := raw.finish hk hcard
      let K := carrier X.rows hBX L
      let l := old X.rows hBX L
      let r := localCell X.rows hBX L
      have hg : ∀ z ∈ G, SelfVis (k + 1) z := fun z hz => selfVis_mono (hG z hz) hBN
      have hθ' : SelfVis (k + 1) θ := selfVis_mono hθ hBN
      have hlt : (D.plan \ insert A (insert B F)).card < n := by
        rw [← hn]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun C hC => ?_, fun he => ?_⟩)
        · simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hC ⊢
          exact ⟨hC.1, hC.2.1, hC.2.2.2⟩
        · have hm := he.symm ▸ hB
          simp only [Finset.mem_sdiff, Finset.mem_insert, true_or, or_true, not_true_eq_false,
            and_false] at hm
      refine ih _ hlt _ rfl {
        carrier := K
        rows := rows X.rows hBX L sep
        plan := X.plan
        consistent := consistent X.rows hBX L sep X.consistent
        coded := coded X.rows hBX L sep X.coded
        original := X.original.trans (OrderEmbedding.ofStrictMono l (old_order X.rows hBX L))
        index := fun d => (old_index X.rows hBX L _).trans (X.index d)
        row := fun c d => (row_old X.rows hBX L sep (X.original c)
          ⟨X.original d.1, by rw [X.index, X.index]; exact d.2⟩).trans (X.row c d)
        exhaustive := fun z hz => by
          rcases classify X.rows hBX L z with ⟨d, rfl⟩ | hd
          · obtain ⟨e, rfl⟩ := X.exhaustive d
              (by simpa only [K, CellScheme.scope, old_index X.rows hBX L] using hz)
            exact ⟨e, rfl⟩
          · exact False.elim (hnew (X.initial_le (hd ▸ hz)))
        occupied := fun z => by
          rcases classify X.rows hBX L z with ⟨d, rfl⟩ | hd
          · simpa only [K, CellScheme.scope, old_index X.rows hBX L] using
              (Finset.mem_insert_of_mem (X.occupied d) : X.carrier.scope d ∈ insert B F)
          · exact hd ▸ Finset.mem_insert_self B F
        initial_le := fun _ h => Finset.mem_insert_of_mem (X.initial_le h)
        scopes := fun C hC => by
          rcases Finset.mem_insert.mp hC with rfl | hC
          · exact hBp
          · exact X.scopes hC
        proper := by simpa only [Finset.mem_insert, not_or] using And.intro hBA.symm X.proper
        closed := fun C hC T hT hTC => by
          rcases Finset.mem_insert.mp hC with hCB | hC
          · rw [hCB] at hTC
            by_cases he : T = B
            · exact he ▸ Finset.mem_insert_self B F
            · exact Finset.mem_insert_of_mem
                (hready T hT (Finset.ssubset_iff_subset_ne.mpr ⟨hTC, he⟩))
          · exact Finset.mem_insert_of_mem (X.closed C hC T hT hTC)
        complete := fun J hJ hJF => by
          rcases Finset.mem_insert.mp hJF with hJB | hJF
          · have hm := Plan.mem_gradedPlan.mp hJ
            obtain ⟨d, hd⟩ := raw.finish_complete hk hcard J (by
              rw [L.plan]
              exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr
                ⟨X.plan.symm ▸ hm.1, Finset.mem_powerset.mpr (subset_of_eq hJB)⟩, hm.2⟩)
            exact ⟨r d, (local_index X.rows hBX L d).trans hd⟩
          · obtain ⟨d, hd⟩ := X.complete J hJ hJF
            exact ⟨l d, (old_index X.rows hBX L d).trans hd⟩
        lifts := fun I J hI hJ hJF h => by
          rcases Finset.mem_insert.mp hJF with hJB | hJF
          · exact local_lift X.rows hBX L sep h
              (X.plan.symm ▸ hI) (X.plan.symm ▸ hJ) (subset_of_eq hJB)
          · exact old_lift X.rows hBX L sep h
              (fun hBJ => hnew (X.closed _ hJF B hBp hBJ)) (X.lifts I J hI hJ hJF h)
        classification := ownerClassification X.rows hBX L sep X.original X.classification
        mute := fun z hz hn => by
          rcases classify X.rows hBX L z with ⟨c, rfl⟩ | hc
          · exact (row_old X.rows hBX L sep c ⟨c, GradedLe.refl _⟩).trans
              (X.mute c
                (by simpa only [K, CellScheme.scope, CellScheme.grade, old_index X.rows hBX L] using hz)
                (by simpa only [K, CellScheme.scope, old_index X.rows hBX L] using hn))
          · obtain ⟨c, rfl⟩ := local_exhaustive X.rows hBX L z (subset_of_eq hc)
            exact (row_local X.rows hBX L sep c ⟨c, GradedLe.refl _⟩).trans
              (OrdinaryRawScope.completed_highest_row raw hk hcard c
                (by simpa only [K, CellScheme.grade, local_index X.rows hBX L, hcard] using
                  hz.trans (congrArg Finset.card hc)) _)
        render := fun {p} hp hb =>
          render X.rows hBX L (X.lawful hp hb)
            (fun d => ne_top_of_le_ne_top htθ (X.bound hp hb d)) G θ
        readback := fun hp hb d =>
          (render_old X.rows hBX L (X.lawful hp hb) _ _).trans (X.readback hp hb d)
        lawful := fun hp hb => render_lawful X.rows hBX L sep (X.lawful hp hb) _ hg hθ'
        bound := fun hp hb => render_bound X.rows hBX L (X.lawful hp hb) _ hg hθ' (X.bound hp hb)
        support := fun hp hb =>
          render_supported X.rows hBX L (X.lawful hp hb) _ hBN hG hθ' hθG (X.support hp hb)
        agreement := by
          intro p q hp hb hq hqb γ hγ hγθ he
          exact render_agreement X.rows hBX L (X.lawful hp hb) _ (X.lawful hq hqb) _ hg hθ' hγ hγθ
            (X.agreement hp hb hq hqb hγ hγθ he) }
    · refine ⟨F, ⟨X⟩, fun B hB hBA => ?_⟩
      by_contra hf
      exact hempty ⟨B, Finset.mem_sdiff.mpr
        ⟨hB, by simp only [Finset.mem_insert, not_or]; exact ⟨hBA, hf⟩⟩⟩
