/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrbitPrefixSupport
public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.MaximalFullLayer
public import VaughtConjecture.Knight.CanonicalOneCoatom
public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
public import VaughtConjecture.Knight.CanonicalRecursiveInitialized
public import VaughtConjecture.Knight.CanonicalRecursiveCoding
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.GradeCutBoundary

@[expose] public section

namespace VaughtConjecture.Knight.OrbitPrefixSupport
open Transform Value ExtOrd

theorem Supported.replace {X : Type*} {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd}
    {x : ExtOrd} (hx : Supported K G p x) (hG : ∀ z ∈ G, SelfVis K z)
    {j : ℕ} (hj : j ≤ K) : Supported K G p (extVisibilityReplace x K j) := by
  rcases hx with rfl | hx | ⟨d, i, hi, rfl⟩
  · exact Or.inl (extVisibilityReplace_bot _ _)
  · have hfix : extVisibilityReplace x K j = x := by
      rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
      · exact extVisibilityReplace_bot _ _
      · exact extVisibilityReplace_top _ _
      · exact extVisibilityReplace_of_le_finitePart (selfVis_ofOrd_iff.mp (hG _ hx)) j
    rw [hfix]; exact Or.inr (Or.inl hx)
  · have hcomp : extVisibilityReplace (extVisibilityReplace (p d) K i) K j =
        extVisibilityReplace (p d) K (if i < K then j else i) := by
      rcases ExtOrd.cases (p d) with he | he | ⟨a, he⟩ <;> rw [he]
      · simp only [extVisibilityReplace_bot]
      · simp only [extVisibilityReplace_top]
      · simp only [extVisibilityReplace_ofOrd, ofOrd_inj]
        rw [visReplace_eq (visibilityReplace a K i), limitPart_visibilityReplace,
          finitePart_visibilityReplace, visReplace_eq a K]
        split_ifs <;> simp_all
    rw [hcomp]; exact Or.inr (Or.inr ⟨d, _, by split_ifs <;> assumption, rfl⟩)

theorem Supported.substitute {X Y : Type*} {K : ℕ} {G : Set ExtOrd}
    {p : X → ExtOrd} {q : Y → ExtOrd} {x : ExtOrd}
    (hx : Supported K G q x) (hG : ∀ z ∈ G, SelfVis K z)
    (hq : ∀ d, Supported K G p (q d)) : Supported K G p x := by
  rcases hx with hx | hx | ⟨d, i, hi, rfl⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact (hq d).replace hG hi

theorem supported_field {X : Type*} (K : ℕ) (G : Set ExtOrd) (p : X → ExtOrd) (d : X) :
    Supported K G p (p d) := by
  rcases ExtOrd.cases (p d) with he | he | ⟨a, he⟩
  · exact Or.inl he
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [he, extVisibilityReplace_top]⟩)
  · refine Or.inr (Or.inr ⟨d, min (finitePart a) K, min_le_right _ _, ?_⟩)
    rw [he, extVisibilityReplace_ofOrd, ofOrd_inj, visibilityReplace]
    split_ifs with h
    · rw [min_eq_left h.le]; exact (decomposition a).symm
    · rfl
end VaughtConjecture.Knight.OrbitPrefixSupport

namespace VaughtConjecture.Knight.WholeDonorOrdinarySections
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
  {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

theorem covered (d : Cell I.boundary) :
    (∃ c, I.leftFace.map c = d) ∨ ∃ c, I.rightFace.map c = d :=
  OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le d

theorem paste_bound {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    {θ : ExtOrd} (hp : ∀ d, p d ≤ θ) (hq : ∀ d, q d ≤ θ)
    (hroot : ∀ i, p (I.shared.f i) = q (I.shared.g i)) (d : Cell I.boundary) :
    I.paste p q d ≤ θ := by
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (I.paste_left p q c) ▸ hp c
  · exact (I.paste_right p q hroot c) ▸ hq c

theorem paste_agreement {p p' : Cell I.left.scheme → ExtOrd}
    {q q' : Cell I.right.scheme → ExtOrd} {h : ExtOrd}
    (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
    (hr' : ∀ i, p' (I.shared.f i) = q' (I.shared.g i))
    (hp : Agree p p' h) (hq : Agree q q' h) : Agree (I.paste p q) (I.paste p' q') h := fun d => by
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (congrArg (fun v => min v h) (I.paste_left p q c)).trans
      ((hp c).trans (congrArg (fun v => min v h) (I.paste_left p' q' c)).symm)
  · exact (congrArg (fun v => min v h) (I.paste_right p q hr c)).trans
      ((hq c).trans (congrArg (fun v => min v h) (I.paste_right p' q' hr' c)).symm)
end
end VaughtConjecture.Knight.WholeDonorOrdinarySections

namespace VaughtConjecture.Knight
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open SourceLayerCarrier SourcePrefixRows OrbitPrefixSupport GradeTailRestoration
noncomputable section

private theorem exists_zero_tail {ι : Type*} [DecidableEq ι] {A : Finset ι}
    (D : CellScheme A) (Q : Type*) [Fintype Q] (l : ℕ) (hl : 0 < l) (hlA : l ≤ A.card)
    (K : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K) (hKl : K < l)
    (sem : Semantics D) (out : Semantics (scheme D Q l hl hlA))
    (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
      out.E (HighLayerBountiful.old D Q l hl hlA c)
        (SeparatedSourceLayerCarrier.ownerEquiv D Q l hl hlA
          (HighLayerBountiful.separated D l K hK hKl) c d) = sem.E c d)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ r : Cell (scheme D Q l hl hlA) → ExtOrd,
      RespectsSemantics out r ∧ (∀ d, r (HighLayerBountiful.old D Q l hl hlA d) = p d) ∧
      ∀ q : Q, r (SourceLayerCarrier.controller D Q l hl hlA q).1 = ⊥ := by
  let e := HighLayerBountiful.equiv D Q l hl hlA (A, K) (fun h => (not_le_of_gt hKl) h.2)
  let v : (scheme D Q l hl hlA).below (A, K) → ExtOrd := fun d => p (e.symm d).1
  have hv : RespectsSemanticsBelow out (A, K) v :=
    (HighLayerBountiful.respects_iff D Q l hl hlA K hK hKl sem out hrow (A, K)
      (fun h => (not_le_of_gt hKl) h.2) _).mp (hp.toBelow _)
  let u : (scheme D Q l hl hlA).below (A, l) → ExtOrd := fun _ => ⊥
  have hs : RespectsSemanticsBelow out (A, l) (splice u v) :=
    splice_respects hKl.le (bottomSection out (A, l) (A, l)).left_lawful hv (M := ⊥)
      (fun _ _ => le_rfl) (fun _ => by simp only [u, min_bot_right])
  have hall (d : Cell (scheme D Q l hl hlA)) :
      GradedLe ((scheme D Q l hl hlA).cell d) (A, l) := by
    refine ⟨(scheme D Q l hl hlA).isPlan.subset_of_mem
      ((scheme D Q l hl hlA).scope_mem_plan d), ?_⟩
    rw [cell_eq]; cases toOcc D Q l hl hlA d with
    | inl x => exact (hK x).trans hKl.le
    | inr _ => exact le_rfl
  refine ⟨fun d => splice u v ⟨d, hall d⟩, hs.toRespects hall, fun d => ?_, fun q => ?_⟩
  · have hd : (scheme D Q l hl hlA).grade (HighLayerBountiful.old D Q l hl hlA d) ≤ K := by
      simpa only [CellScheme.grade, HighLayerBountiful.old, cell_toCell, index] using hK d
    refine (splice_low u v ⟨HighLayerBountiful.old D Q l hl hlA d, hall _⟩ hd).trans ?_
    let d₀ : D.below (A, K) := ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hK d⟩
    change p (e.symm (e d₀)).1 = p d; rw [Equiv.symm_apply_apply]
  · refine splice_high u v _ ?_
    change ¬ ((scheme D Q l hl hlA).cell (SourceLayerCarrier.controller D Q l hl hlA q).1).2 ≤ K
    rw [(SourceLayerCarrier.controller D Q l hl hlA q).2]; exact not_le_of_gt hKl

namespace OrdinaryScopeMute
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
  (sem : Semantics D) (K l : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K)
  (hKl : K < l) (hlA : l ≤ A.card)

abbrev carrier := MaximalFullLayer.scheme D K l hKl hlA
abbrev old := MaximalFullLayer.old D K l hKl hlA
abbrev apex := MaximalFullLayer.apex D K l hKl hlA
abbrev rows := MaximalFullLayer.base D sem K l hK hKl hlA

def render (p : Cell D → ExtOrd) : Cell (carrier D K l hKl hlA) → ExtOrd :=
  fun d => Sum.elim p (fun _ => ⊥) (toOcc D Unit l (MaximalFullLayer.positive K l hKl) hlA d)

theorem render_old (p : Cell D → ExtOrd) (d : Cell D) :
    render D K l hKl hlA p (old D K l hKl hlA d) = p d := by
  simp only [render, old, MaximalFullLayer.old, toOcc_toCell, Sum.elim_inl]

theorem render_apex (p : Cell D → ExtOrd) :
    render D K l hKl hlA p (apex D K l hKl hlA) = ⊥ := by
  simp only [render, apex, MaximalFullLayer.apex, toOcc_toCell, Sum.elim_inr]

theorem covered (d : Cell (carrier D K l hKl hlA)) :
    (∃ c, d = old D K l hKl hlA c) ∨ d = apex D K l hKl hlA := by
  obtain ⟨x, rfl⟩ := (enumeration D Unit l (MaximalFullLayer.positive K l hKl) hlA).surjective d
  rcases x with c | ⟨⟩; exact Or.inl ⟨c, rfl⟩; exact Or.inr rfl

theorem render_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows D sem K l hK hKl hlA) (render D K l hKl hlA p) := by
  obtain ⟨r, hr, hold, hnew⟩ := exists_zero_tail D Unit l
    (MaximalFullLayer.positive K l hKl) hlA K hK hKl sem
    (rows D sem K l hK hKl hlA) (MaximalFullLayer.inherited_row D sem K l hK hKl hlA) hp
  have he : render D K l hKl hlA p = r := funext fun d => by
    rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
    · exact (render_old D K l hKl hlA p c).trans (hold c).symm
    · exact (render_apex D K l hKl hlA p).trans (hnew ()).symm
  exact he.symm ▸ hr

theorem render_bound {p : Cell D → ExtOrd} {θ : ExtOrd} (hp : ∀ d, p d ≤ θ)
    (d : Cell (carrier D K l hKl hlA)) : render D K l hKl hlA p d ≤ θ := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact bot_le

theorem render_agreement {p q : Cell D → ExtOrd} {γ : ExtOrd} (hpq : Agree p q γ) :
    Agree (render D K l hKl hlA p) (render D K l hKl hlA q) γ := fun d => by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · simp only [render_old]; exact hpq c
  · simp only [render_apex]

theorem render_supported {X : Type*} {v : X → ExtOrd} {k : ℕ} {G : Set ExtOrd}
    {p : Cell D → ExtOrd} (hp : ∀ d, Supported k G v (p d))
    (d : Cell (carrier D K l hKl hlA)) : Supported k G v (render D K l hKl hlA p d) := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact Or.inl rfl

theorem apex_row (d : (carrier D K l hKl hlA).below
    ((carrier D K l hKl hlA).cell (apex D K l hKl hlA))) :
    (rows D sem K l hK hKl hlA).E (apex D K l hKl hlA) d = ⊥ := by
  simp only [rows, MaximalFullLayer.base, apex, MaximalFullLayer.apex,
    SeparatedSourceLayerCarrier.base, toOcc_toCell, SeparatedSourceLayerCarrier.oldTable]

theorem inherited_short (c : Cell D)
    (hc : ∀ d : D.below (D.cell c), SharpWitnessComposition.Short (D.grade c) (sem.E c d))
    (d : (carrier D K l hKl hlA).below
      ((carrier D K l hKl hlA).cell (old D K l hKl hlA c))) :
    SharpWitnessComposition.Short ((carrier D K l hKl hlA).grade (old D K l hKl hlA c))
      ((rows D sem K l hK hKl hlA).E (old D K l hKl hlA c) d) := by
  obtain ⟨e, rfl⟩ := (MaximalFullLayer.ownerEquiv D K l hK hKl hlA c).surjective d
  rw [MaximalFullLayer.inherited_row]
  simpa only [CellScheme.grade, old, MaximalFullLayer.old, cell_toCell, index] using hc e

theorem complete_last (hcard : A.card = l) (hnext : l = K + 1)
    (hs : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ K → ∃ d, D.cell d = J) :
    (carrier D K l hKl hlA).IsComplete := by
  refine MaximalFullLayer.complete D K l hKl hlA fun J hJ hne => hs J hJ ?_
  obtain ⟨hmem, _, hgrade⟩ := Plan.mem_gradedPlan.mp hJ
  have hsub := D.isPlan.subset_of_mem hmem
  have hc := Finset.card_le_card hsub
  by_contra hn
  have hj : J.2 = l := by omega
  have he : J.1 = A := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hne (Prod.ext he hj)
end OrdinaryScopeMute

namespace OrdinaryScopeOperator
structure Core {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = D.plan
  original : Cell D ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = D.cell d
  coverage : ∀ d, (∃ c, original c = d) ∨ carrier.scope d = A
  row : ∀ (c : Cell D) (d : D.below (D.cell c)),
    rows.E (original c) ⟨original d.1, by rw [index, index]; exact d.2⟩ = sem.E c d
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  bountiful : rows.IsBountiful
  grade : ∀ d, carrier.grade d ≤ k
  complete : ∀ J ∈ Plan.gradedPlan carrier.plan, J.2 ≤ k → ∃ d, carrier.cell d = J
  short : ∀ c, carrier.scope c = A → ∀ d,
    SharpWitnessComposition.Short (carrier.grade c) (rows.E c d)
  render : ∀ {p : Cell D → ExtOrd}, RespectsSemantics sem p → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, (∀ z ∈ G, SelfVis k z) → SelfVis k θ → ∀ d, render hp ht G θ (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, (∀ z ∈ G, SelfVis k z) → SelfVis k θ → RespectsSemantics rows (render hp ht G θ)
  bound : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, SelfVis k θ → (∀ d, p d ≤ θ) → ∀ d, render hp ht G θ d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} {K : ℕ}, k ≤ K → θ ∈ G → ∀ d,
    Supported K (G : Set ExtOrd) p (render hp ht G θ d)
  agreement : ∀ {p q} (hp : RespectsSemantics sem p) (htp : ∀ d, p d ≠ ⊤)
    (hq : RespectsSemantics sem q) (htq : ∀ d, q d ≠ ⊤) {G θ γ},
    (∀ z ∈ G, SelfVis k z) → SelfVis k θ → γ ∈ G → γ ≤ θ → Agree p q γ →
    Agree (render hp htp G θ) (render hq htq G θ) γ

def Core.finish {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {k : ℕ} (S : Core sem k) (hk : 0 < k) (hcard : A.card = k + 1) :
    Core sem (k + 1) where
  carrier := OrdinaryScopeMute.carrier S.carrier k (k + 1) (by omega) hcard.ge
  rows := OrdinaryScopeMute.rows S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge
  plan := S.plan
  original := S.original.trans (OrderEmbedding.ofStrictMono
    (OrdinaryScopeMute.old S.carrier k (k + 1) (by omega) hcard.ge)
    (SourceLayerCarrier.old_order _ _ _ _ _))
  index d := (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge
    (S.original d)).trans (S.index d)
  coverage d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge d with ⟨c, rfl⟩ | rfl
    · rcases S.coverage c with ⟨a, rfl⟩ | ha
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ((congrArg Prod.fst
          (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).trans ha)
    · exact Or.inr (congrArg Prod.fst
        (MaximalFullLayer.apex_index S.carrier k (k + 1) (by omega) hcard.ge))
  row c d := (MaximalFullLayer.inherited_row S.carrier S.rows k (k + 1) S.grade
    (by omega) hcard.ge (S.original c)
      ⟨S.original d.1, by rw [S.index, S.index]; exact d.2⟩).trans (S.row c d)
  consistent := MaximalFullLayer.consistent _ _ _ _ _ _ _ S.consistent
  coded := MaximalFullLayer.coded _ _ _ _ _ _ _ S.coded
  bountiful := MaximalFullLayer.bountiful _ _ _ _ _ _ _ hk S.bountiful
  grade d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge d with ⟨c, rfl⟩ | rfl
    · exact (congrArg Prod.snd
        (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).le.trans
          ((S.grade c).trans (Nat.le_succ k))
    · exact (congrArg Prod.snd
        (MaximalFullLayer.apex_index S.carrier k (k + 1) (by omega) hcard.ge)).le
  complete J hJ _ := OrdinaryScopeMute.complete_last S.carrier k (k + 1) (by omega)
    hcard.ge hcard rfl S.complete J hJ
  short c hc d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge c with ⟨c, rfl⟩ | rfl
    · exact OrdinaryScopeMute.inherited_short S.carrier S.rows k (k + 1) S.grade
        (by omega) hcard.ge c (S.short c ((congrArg Prod.fst
          (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).symm.trans hc)) d
    · have h : SharpWitnessComposition.Short (k + 1)
          ((OrdinaryScopeMute.rows S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge).E
            (OrdinaryScopeMute.apex S.carrier k (k + 1) (by omega) hcard.ge) d) := by
        rw [OrdinaryScopeMute.apex_row]; exact Or.inl rfl
      exact (congrArg (fun j => SharpWitnessComposition.Short j _)
        (congrArg Prod.snd (MaximalFullLayer.apex_index S.carrier k (k + 1)
          (by omega) hcard.ge))).mpr h
  render := fun hp ht G θ => OrdinaryScopeMute.render S.carrier k (k + 1)
    (by omega) hcard.ge (S.render hp ht G θ)
  readback := by
    intro p hp ht G θ hG hθ d
    exact (OrdinaryScopeMute.render_old S.carrier k (k + 1) (by omega) hcard.ge _ _).trans
      (S.readback hp ht (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)) d)
  lawful := by
    intro p hp ht G θ hG hθ
    exact OrdinaryScopeMute.render_lawful S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge
      (S.lawful hp ht (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)))
  bound := by
    intro p hp ht G θ hθ hb
    exact OrdinaryScopeMute.render_bound S.carrier k (k + 1)
      (by omega) hcard.ge (S.bound hp ht (selfVis_mono hθ (Nat.le_succ k)) hb)
  support := by
    intro p hp ht G θ K hK hθ
    exact OrdinaryScopeMute.render_supported S.carrier k (k + 1)
      (by omega) hcard.ge (S.support hp ht ((Nat.le_succ k).trans hK) hθ)
  agreement := by
    intro p q hp ht hq htq G θ γ hG hθ hγ hγθ hag
    exact OrdinaryScopeMute.render_agreement S.carrier k (k + 1) (by omega) hcard.ge
      (S.agreement hp ht hq htq (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)) hγ hγθ hag)

theorem Core.finish_complete {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {k : ℕ} (S : Core sem k) (hk : 0 < k) (hcard : A.card = k + 1) :
    (S.finish hk hcard).carrier.IsComplete :=
  OrdinaryScopeMute.complete_last S.carrier k (k + 1) (by omega) hcard.ge hcard rfl S.complete
end OrdinaryScopeOperator

namespace ScopeBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B : Finset ι) (hB : B ∈ D.plan)

def inventory : Finset (Cell D) := Finset.univ.filter fun d => D.scope d ⊆ B

def scheme : CellScheme B where
  plan := Plan.restrictPlan D.plan B
  isPlan := Plan.restrict_isPlan D.isPlan hB
  card := (inventory D B).card
  cell c := D.cell ((inventory D B).orderEmbOfFin rfl c)
  cell_mem c := by
    obtain ⟨hs, hk, hc⟩ := Plan.mem_gradedPlan.mp
      (D.cell_mem ((inventory D B).orderEmbOfFin rfl c))
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr
      ⟨hs, Finset.mem_powerset.mpr
        (Finset.mem_filter.mp ((inventory D B).orderEmbOfFin_mem rfl c)).2⟩, hk, hc⟩

def toCell : Cell (scheme D B hB) ↪o Cell D := (inventory D B).orderEmbOfFin rfl
theorem cell_eq (d : Cell (scheme D B hB)) :
    (scheme D B hB).cell d = D.cell (toCell D B hB d) := rfl
theorem scope_bound (d : Cell (scheme D B hB)) : D.scope (toCell D B hB d) ⊆ B :=
  (Finset.mem_filter.mp ((inventory D B).orderEmbOfFin_mem rfl d)).2

theorem exhaustive {d : Cell D} (hd : D.scope d ⊆ B) : ∃ c, toCell D B hB c = d := by
  have hm : d ∈ Set.range ((inventory D B).orderEmbOfFin (k := (inventory D B).card) rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  exact hm

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.1 ⊆ B) :
    (scheme D B hB).below BJ ≃ D.below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell D B hB d.1, d.2⟩) ⟨fun _ _ hab =>
    Subtype.ext ((toCell D B hB).injective (congrArg (fun z : D.below BJ => z.1) hab)), fun d => by
      obtain ⟨c, hc⟩ := exhaustive D B hB (d.2.1.trans hBJ)
      exact ⟨⟨c, by simpa only [cell_eq, hc] using d.2⟩, Subtype.ext hc⟩⟩

def rows (sem : Semantics D) : Semantics (scheme D B hB) where
  E c d := sem.E (toCell D B hB c)
    (belowEquiv D B hB ((scheme D B hB).cell c) (scope_bound D B hB c) d)
  orderly c _ := sem.orderly (toCell D B hB c) _

theorem respects_iff (sem : Semantics D) (BJ : Finset ι × ℕ) (hBJ : BJ.1 ⊆ B)
    (p : (scheme D B hB).below BJ → ExtOrd) :
    RespectsSemanticsBelow (rows D B hB sem) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D B hB BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D B hB BJ hBJ) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

theorem consistent (sem : Semantics D) (hs : sem.IsConsistent) : (rows D B hB sem).IsConsistent :=
  fun c => (respects_iff D B hB sem ((scheme D B hB).cell c) (scope_bound D B hB c) _).mpr <| by
    have h : ((rows D B hB sem).E c ∘ (belowEquiv D B hB ((scheme D B hB).cell c)
        (scope_bound D B hB c)).symm) = sem.E (toCell D B hB c) :=
      funext fun x => congrArg _ (Equiv.apply_symm_apply _ x)
    rw [h]; exact hs (toCell D B hB c)

theorem coded (sem : Semantics D) (hs : sem.IsCoded) : (rows D B hB sem).IsCoded :=
  fun _ _ => hs _ _
end ScopeBoundary

namespace OrderedScopeRelocation
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
  {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
  (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)

abbrev shared := ScopeBoundary.scheme D B hB
abbrev leftMap := (ScopeBoundary.toCell D B hB).toEmbedding
abbrev rightMap := S.original.toEmbedding
abbrev Occ := ProfileFaceUnion.Carrier (X := Cell D) (rightMap sem hB S)

def enumeration : Occ sem hB S ≃ Fin (Fintype.card (Occ sem hB S)) :=
  ProfileBoundaryOrder.enumeration (leftMap hB) (rightMap sem hB S)
    (ScopeBoundary.toCell D B hB).strictMono S.original.strictMono

def index : Occ sem hB S → Finset ι × ℕ :=
  ProfileFaceUnion.paste (rightMap sem hB S) D.cell S.carrier.cell

theorem index_right (d : Cell S.carrier) :
    index sem hB S (ProfileFaceUnion.right (leftMap hB) (rightMap sem hB S) d) =
      S.carrier.cell d :=
  ProfileFaceUnion.paste_right _ _ (fun c => (S.index c).symm) d

def carrier : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := Fintype.card (Occ sem hB S)
  cell c := index sem hB S ((enumeration sem hB S).symm c)
  cell_mem c := by
    rcases ProfileFaceUnion.covered (leftMap hB) (rightMap sem hB S)
      ((enumeration sem hB S).symm c) with ⟨d, hd⟩ | ⟨d, hd⟩
    · rw [← hd]; exact D.cell_mem d
    · rw [← hd, index_right]
      obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp (S.carrier.cell_mem d)
      rw [S.plan] at hp
      exact Plan.mem_gradedPlan.mpr ⟨(Finset.mem_inter.mp hp).1, hg, hc⟩

def old (d : Cell D) : Cell (carrier sem hB S) :=
  enumeration sem hB S (ProfileFaceUnion.left (rightMap sem hB S) d)
def localCell (d : Cell S.carrier) : Cell (carrier sem hB S) :=
  enumeration sem hB S (ProfileFaceUnion.right (leftMap hB) (rightMap sem hB S) d)

theorem old_index (d : Cell D) : (carrier sem hB S).cell (old sem hB S d) = D.cell d := by
  change index sem hB S ((enumeration sem hB S).symm (enumeration sem hB S _)) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem local_index (d : Cell S.carrier) :
    (carrier sem hB S).cell (localCell sem hB S d) = S.carrier.cell d := by
  change index sem hB S ((enumeration sem hB S).symm (enumeration sem hB S _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem old_order : StrictMono (old sem hB S) := ProfileBoundaryOrder.enumeration_left _ _ _ _
theorem local_order : StrictMono (localCell sem hB S) := ProfileBoundaryOrder.enumeration_right _ _ _ _

theorem shared_cell (c : Cell (shared hB)) :
    localCell sem hB S (S.original c) = old sem hB S (ScopeBoundary.toCell D B hB c) :=
  congrArg (enumeration sem hB S) (ProfileFaceUnion.right_shared _ _ c)

theorem covered (z : Cell (carrier sem hB S)) :
    (∃ d, old sem hB S d = z) ∨ ∃ e, localCell sem hB S e = z := by
  rcases ProfileFaceUnion.covered (leftMap hB) (rightMap sem hB S)
    ((enumeration sem hB S).symm z) with ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg (enumeration sem hB S) hd).trans
      ((enumeration sem hB S).apply_symm_apply z)⟩
  · exact Or.inr ⟨e, (congrArg (enumeration sem hB S) he).trans
      ((enumeration sem hB S).apply_symm_apply z)⟩

theorem classify (z : Cell (carrier sem hB S)) :
    (∃ d, old sem hB S d = z) ∨ (carrier sem hB S).scope z = B := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact Or.inl ⟨d, rfl⟩
  · rcases S.coverage e with ⟨c, rfl⟩ | hc
    · exact Or.inl ⟨ScopeBoundary.toCell D B hB c, (shared_cell sem hB S c).symm⟩
    · exact Or.inr ((congrArg Prod.fst (local_index sem hB S e)).trans hc)

theorem local_exhaustive (z : Cell (carrier sem hB S))
    (hz : (carrier sem hB S).scope z ⊆ B) : ∃ e, localCell sem hB S e = z := by
  rcases covered sem hB S z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · change ((carrier sem hB S).cell (old sem hB S d)).1 ⊆ B at hz; rw [old_index] at hz
    obtain ⟨c, rfl⟩ := ScopeBoundary.exhaustive D B hB hz
    exact ⟨S.original c, shared_cell sem hB S c⟩
  · exact ⟨e, rfl⟩

def Separated : Prop := ∀ d : Cell D, ¬ B ⊆ D.scope d
variable (hsep : Separated (D := D) (B := B))

include hsep in
theorem old_exhaustive (c : Cell D) (z : Cell (carrier sem hB S))
    (hz : (carrier sem hB S).scope z ⊆ D.scope c) : ∃ d, old sem hB S d = z :=
  (classify sem hB S z).elim id fun h => False.elim (hsep c (h ▸ hz))

def oldBelow (c : Cell D) :
    D.below (D.cell c) ≃ (carrier sem hB S).below ((carrier sem hB S).cell (old sem hB S c)) :=
  Equiv.ofBijective (fun d => ⟨old sem hB S d.1, by rw [old_index, old_index]; exact d.2⟩)
    ⟨fun _ _ h => Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)), fun z => by
      have hz := z.2.1; simp only [old_index] at hz
      obtain ⟨d, hd⟩ := old_exhaustive sem hB S hsep c z.1 hz
      exact ⟨⟨d, by simpa only [← hd, old_index] using z.2⟩, Subtype.ext hd⟩⟩

def localBelow (c : Cell S.carrier) :
    S.carrier.below (S.carrier.cell c) ≃
      (carrier sem hB S).below ((carrier sem hB S).cell (localCell sem hB S c)) :=
  Equiv.ofBijective (fun d => ⟨localCell sem hB S d.1, by rw [local_index, local_index]; exact d.2⟩)
    ⟨fun _ _ h => Subtype.ext ((local_order sem hB S).injective (congrArg Subtype.val h)), fun z => by
      have hz := z.2.1; simp only [local_index] at hz
      obtain ⟨d, hd⟩ := local_exhaustive sem hB S z.1
        (hz.trans (S.carrier.isPlan.subset_of_mem (S.carrier.scope_mem_plan c)))
      exact ⟨⟨d, by simpa only [← hd, local_index] using z.2⟩, Subtype.ext hd⟩⟩

open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

include hsep in
private theorem pushRow_shared (c : Cell (shared hB)) :
    pushRow (old sem hB S) sem (ScopeBoundary.toCell D B hB c) =
      pushRow (localCell sem hB S) S.rows (S.original c) := by
  classical
  funext z
  by_cases hz : GradedLe ((carrier sem hB S).cell z) (D.cell (ScopeBoundary.toCell D B hB c))
  · obtain ⟨d, hd⟩ := (oldBelow sem hB S hsep (ScopeBoundary.toCell D B hB c)).surjective
      ⟨z, by rw [old_index]; exact hz⟩
    have he : old sem hB S d.1 = z := congrArg Subtype.val hd
    obtain ⟨e, he'⟩ := ScopeBoundary.exhaustive D B hB
      (d.2.1.trans (ScopeBoundary.scope_bound D B hB c))
    rw [← he, ← he', pushRow_at _ (old_order sem hB S).injective,
      ← shared_cell, pushRow_at _ (local_order sem hB S).injective]
    by_cases hd' : GradedLe ((shared hB).cell e) ((shared hB).cell c)
    · exact (total_below sem (ScopeBoundary.toCell D B hB c) ⟨_, hd'⟩).trans
        ((S.row c ⟨e, hd'⟩).symm.trans (total_below S.rows (S.original c)
          ⟨S.original e, by rw [S.index, S.index]; exact hd'⟩).symm)
    · exact (AmalgamatedBoundaryRows.total_outside sem _ _ hd').trans
        (AmalgamatedBoundaryRows.total_outside S.rows _ _ (by simpa only [S.index] using hd')).symm
  · rw [pushRow_outside _ (old_order sem hB S).injective (old_index sem hB S) sem _ _ hz,
      pushRow_outside _ (local_order sem hB S).injective (local_index sem hB S) S.rows]
    simpa only [S.index, ScopeBoundary.cell_eq] using hz

def table (c : Cell (carrier sem hB S)) : Cell (carrier sem hB S) → ExtOrd :=
  ProfileFaceUnion.paste (rightMap sem hB S) (pushRow (old sem hB S) sem)
    (pushRow (localCell sem hB S) S.rows) ((enumeration sem hB S).symm c)

theorem table_old (c d : Cell D) :
    table sem hB S (old sem hB S c) (old sem hB S d) = total sem c d := by
  change ProfileFaceUnion.paste _ (pushRow (old sem hB S) sem) (pushRow (localCell sem hB S) S.rows)
    ((enumeration sem hB S).symm (enumeration sem hB S (ProfileFaceUnion.left _ c)))
    (old sem hB S d) = _
  rw [Equiv.symm_apply_apply]; exact pushRow_at _ (old_order sem hB S).injective sem c d

include hsep in
theorem table_local (c d : Cell S.carrier) :
    table sem hB S (localCell sem hB S c) (localCell sem hB S d) = total S.rows c d := by
  change ProfileFaceUnion.paste _ (pushRow (old sem hB S) sem) (pushRow (localCell sem hB S) S.rows)
    ((enumeration sem hB S).symm (enumeration sem hB S (ProfileFaceUnion.right (leftMap hB) _ c)))
    (localCell sem hB S d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right _ _ (pushRow_shared sem hB S hsep)]
  exact pushRow_at _ (local_order sem hB S).injective S.rows c d

include hsep in
theorem table_orderly (c : Cell (carrier sem hB S))
    (d : (carrier sem hB S).below ((carrier sem hB S).cell c)) :
    table sem hB S c d.1 = extVisibilityReplace (table sem hB S c d.1)
      ((carrier sem hB S).grade d.1) ((carrier sem hB S).grade d.1) := by
  rcases covered sem hB S c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
    change table sem hB S (old sem hB S c) (old sem hB S e.1) =
      extVisibilityReplace (table sem hB S (old sem hB S c) (old sem hB S e.1))
        ((carrier sem hB S).cell (old sem hB S e.1)).2
        ((carrier sem hB S).cell (old sem hB S e.1)).2
    rw [table_old, total_below, old_index]; exact sem.orderly c e
  · obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
    change table sem hB S (localCell sem hB S c) (localCell sem hB S e.1) =
      extVisibilityReplace (table sem hB S (localCell sem hB S c) (localCell sem hB S e.1))
        ((carrier sem hB S).cell (localCell sem hB S e.1)).2
        ((carrier sem hB S).cell (localCell sem hB S e.1)).2
    rw [table_local sem hB S hsep, total_below, local_index]; exact S.rows.orderly c e

def rows : Semantics (carrier sem hB S) where
  E c d := table sem hB S c d.1
  orderly := table_orderly sem hB S hsep

theorem row_old (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem hB S hsep).E (old sem hB S c) (oldBelow sem hB S hsep c d) = sem.E c d :=
  (table_old sem hB S c d.1).trans (total_below sem c d)

theorem row_local (c : Cell S.carrier) (d : S.carrier.below (S.carrier.cell c)) :
    (rows sem hB S hsep).E (localCell sem hB S c) (localBelow sem hB S c d) = S.rows.E c d :=
  (table_local sem hB S hsep c d.1).trans (total_below S.rows c d)

def localFace : ExactSemanticFace S.rows (rows sem hB S hsep) where
  map := ⟨localCell sem hB S, (local_order sem hB S).injective⟩
  index := local_index sem hB S
  exhaustive := local_exhaustive sem hB S
  row := row_local sem hB S hsep

theorem consistent (hc : sem.IsConsistent) : (rows sem hB S hsep).IsConsistent := fun z => by
  rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have h := respects_iff_of_equiv (sem' := sem) (sem := rows sem hB S hsep)
      (oldBelow sem hB S hsep c) (fun d => (congrArg Prod.snd (old_index sem hB S d.1)).symm)
      (fun d e => by
        change D.scope d.1 ⊆ D.scope e.1 ↔
          ((carrier sem hB S).cell (old sem hB S d.1)).1 ⊆ ((carrier sem hB S).cell (old sem hB S e.1)).1
        rw [old_index, old_index]; rfl)
      (fun c d _ => (row_old sem hB S hsep c.1 d).symm) (sem.E c)
    have he : sem.E c ∘ (oldBelow sem hB S hsep c).symm =
        (rows sem hB S hsep).E (old sem hB S c) := funext fun d => by
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact (row_old sem hB S hsep c e).symm
    exact (he ▸ h).mp (hc c)
  · exact (localFace sem hB S hsep).consistent_at S.consistent c

theorem coded (hc : sem.IsCoded) : (rows sem hB S hsep).IsCoded := fun z d => by
  rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
    change IsCodedLabel ((carrier sem hB S).cell (old sem hB S c)).2 ((rows sem hB S hsep).E _ _)
    rw [row_old, old_index]; exact hc c e
  · exact (localFace sem hB S hsep).coded_at S.coded c d

def boundaryFace : ExactSemanticFace (ScopeBoundary.rows D B hB sem) sem where
  map := (ScopeBoundary.toCell D B hB).toEmbedding
  index _ := rfl
  exhaustive _ := ScopeBoundary.exhaustive D B hB
  row _ _ := rfl

def paste (p : Cell D → ExtOrd) (q : Cell S.carrier → ExtOrd) : Cell (carrier sem hB S) → ExtOrd :=
  fun z => ProfileFaceUnion.paste (rightMap sem hB S) p q ((enumeration sem hB S).symm z)

theorem paste_old (p : Cell D → ExtOrd) (q : Cell S.carrier → ExtOrd) (d : Cell D) :
    paste sem hB S p q (old sem hB S d) = p d := by
  unfold paste old; rw [Equiv.symm_apply_apply]; rfl

theorem paste_local {p : Cell D → ExtOrd} {q : Cell S.carrier → ExtOrd}
    (he : ∀ c, p (ScopeBoundary.toCell D B hB c) = q (S.original c)) (d : Cell S.carrier) :
    paste sem hB S p q (localCell sem hB S d) = q d := by
  unfold paste localCell; rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right _ _ he d

def render {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (G : Finset ExtOrd) (θ : ExtOrd) : Cell (carrier sem hB S) → ExtOrd :=
  paste sem hB S p (S.render ((boundaryFace sem hB).restrict hp)
    (fun c => ht (ScopeBoundary.toCell D B hB c)) G θ)

theorem render_old {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} (d : Cell D) :
    render sem hB S hp ht G θ (old sem hB S d) = p d := paste_old sem hB S _ _ d

theorem render_local {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    (d : Cell S.carrier) :
    render sem hB S hp ht G θ (localCell sem hB S d) =
      S.render ((boundaryFace sem hB).restrict hp)
        (fun c => ht (ScopeBoundary.toCell D B hB c)) G θ d :=
  paste_local sem hB S (fun c => (S.readback ((boundaryFace sem hB).restrict hp)
    (fun c => ht (ScopeBoundary.toCell D B hB c)) hG hθ c).symm) d

theorem render_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ) :
    RespectsSemantics (rows sem hB S hsep) (render sem hB S hp ht G θ) := by
  have hp' : RespectsSemantics sem (render sem hB S hp ht G θ ∘ old sem hB S) := by
    simpa only [Function.comp_def, render_old] using hp
  have hq' : RespectsSemantics S.rows (render sem hB S hp ht G θ ∘ localCell sem hB S) := by
    simpa only [Function.comp_def, render_local sem hB S hp ht hG hθ] using S.lawful _ _ hG hθ
  refine ⟨fun z => ?_, fun z => ?_, fun z c hs hg => ?_⟩
  · rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simpa only [Function.comp_apply, CellScheme.grade, old_index] using hp'.orderly c
    · simpa only [Function.comp_apply, CellScheme.grade, local_index] using hq'.orderly c
  · rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact TransformsTo.of_equiv (oldBelow sem hB S hsep c)
        (fun d => congrArg Prod.snd (old_index sem hB S d.1))
        (row_old sem hB S hsep c) (fun _ => rfl) (hp'.locality c)
    · exact (localFace sem hB S hsep).locality_of_restrict hq' c
  · rcases covered sem hB S c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have hz : (carrier sem hB S).scope z ⊆ D.scope c := by
        simpa only [CellScheme.scope, old_index] using hs
      obtain ⟨d, rfl⟩ := old_exhaustive sem hB S hsep c z hz
      obtain ⟨e, he, hv⟩ := hp'.availability d c
        (by simpa only [CellScheme.scope, old_index] using hs)
        (by simpa only [CellScheme.grade, old_index] using hg)
      exact ⟨old sem hB S e, (old_index sem hB S e).trans
        (he.trans (old_index sem hB S c).symm), hv⟩
    · exact (localFace sem hB S hsep).availability_at hq' z c hs hg

theorem render_bound {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    (hb : ∀ d, p d ≤ θ) (d : Cell (carrier sem hB S)) : render sem hB S hp ht G θ d ≤ θ := by
  rcases covered sem hB S d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old]; exact hb c
  · rw [render_local sem hB S hp ht hG hθ]; exact S.bound _ _ hθ (fun _ => hb _) c

theorem render_supported {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} {X : Type*} {v : X → ExtOrd} {L : ℕ} (hk : k ≤ L)
    (hG : ∀ z ∈ G, SelfVis L z) (hθ : SelfVis k θ) (hθG : θ ∈ G)
    (hv : ∀ d, Supported L (G : Set ExtOrd) v (p d)) (d : Cell (carrier sem hB S)) :
    Supported L (G : Set ExtOrd) v (render sem hB S hp ht G θ d) := by
  rcases covered sem hB S d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old]; exact hv c
  · rw [render_local sem hB S hp ht (fun z hz => selfVis_mono (hG z hz) hk) hθ]
    exact (S.support _ _ hk hθG c).substitute hG (fun _ => hv _)

theorem render_agreement {p q : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hq : RespectsSemantics sem q) (htq : ∀ d, q d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    {γ : ExtOrd} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render sem hB S hp ht G θ) (render sem hB S hq htq G θ) γ := fun d => by
  rcases covered sem hB S d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old, render_old]; exact he c
  · rw [render_local sem hB S hp ht hG hθ, render_local sem hB S hq htq hG hθ]
    exact S.agreement _ _ _ _ hG hθ hγ hγθ (fun _ => he _) c

def oldLower (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1) : D.below J ≃ (carrier sem hB S).below J :=
  Equiv.ofBijective (fun d => ⟨old sem hB S d.1, by rw [old_index]; exact d.2⟩)
    ⟨fun _ _ h => Subtype.ext ((old_order sem hB S).injective (congrArg Subtype.val h)), fun z => by
      rcases classify sem hB S z.1 with ⟨d, hd⟩ | hd
      · exact ⟨⟨d, by simpa only [← hd, old_index] using z.2⟩, Subtype.ext hd⟩
      · exact False.elim (hJ (hd ▸ z.2.1))⟩

theorem oldLower_pullback (J : Finset ι × ℕ) (hJ : ¬ B ⊆ J.1)
    (q : (carrier sem hB S).below J → ExtOrd) :
    RespectsSemanticsBelow (rows sem hB S hsep) J q ↔
      RespectsSemanticsBelow sem J (q ∘ oldLower sem hB S J hJ) := by
  have h := respects_iff_of_equiv (oldLower sem hB S J hJ)
    (fun d => (congrArg Prod.snd (old_index sem hB S d.1)).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔
        ((carrier sem hB S).cell (old sem hB S d.1)).1 ⊆ ((carrier sem hB S).cell (old sem hB S e.1)).1
      rw [old_index, old_index]; rfl)
    (fun c d _ => (row_old sem hB S hsep c.1 d).symm) (q ∘ oldLower sem hB S J hJ)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

theorem old_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ B ⊆ J.1)
    (hb : CappedLift sem h) : CappedLift (rows sem hB S hsep) h := by
  have hI : ¬ B ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  let eJ := oldLower sem hB S J hJ
  let eI := oldLower sem hB S I hI
  intro p q γ hp hq hγ hc
  refine bountiful_of_equiv (sem' := rows sem hB S hsep) (sem := sem)
    h h eJ.symm eI.symm (fun d => eJ.injective ?_)
    (oldLower_pullback sem hB S hsep J hJ) (oldLower_pullback sem hB S hsep I hI)
    hb rfl p q γ hp hq hγ hc
  rw [Equiv.apply_symm_apply]; exact Subtype.ext (congrArg Subtype.val (eI.apply_symm_apply d)).symm

theorem local_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan) (hJB : J.1 ⊆ B) :
    CappedLift (rows sem hB S hsep) h := by
  by_cases he : I = J
  · subst J; exact lift_refl
  · have memLocal : ∀ T ∈ Plan.gradedPlan D.plan, T.1 ⊆ B → T ∈ Plan.gradedPlan S.carrier.plan :=
      fun T hT hTB => by
        obtain ⟨hp, hg, hc⟩ := Plan.mem_gradedPlan.mp hT; rw [S.plan]
        exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr ⟨hp, Finset.mem_powerset.mpr hTB⟩, hg, hc⟩
    exact (localFace sem hB S hsep).lift hJB (memLocal I hI (h.1.trans hJB))
      (memLocal J hJ hJB) h he S.bountiful

def OwnerClassification {X : Type*} (original : X → Cell D) : Prop :=
  ∀ c : Cell D, (∀ d, SharpWitnessComposition.Short (D.grade c) (sem.E c d)) ∨
    ∀ d : D.below (D.cell c), ∃ x, original x = d.1

theorem ownerClassification {X : Type*} (original : X → Cell D)
    (hc : OwnerClassification sem original) :
    OwnerClassification (rows sem hB S hsep) (old sem hB S ∘ original) := fun z => by
  rcases classify sem hB S z with ⟨c, rfl⟩ | hz
  · rcases hc c with hshort | horiginal
    · refine Or.inl fun d => ?_
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      change SharpWitnessComposition.Short ((carrier sem hB S).cell (old sem hB S c)).2 _
      rw [row_old, old_index]; exact hshort e
    · refine Or.inr fun d => ?_
      obtain ⟨e, rfl⟩ := (oldBelow sem hB S hsep c).surjective d
      obtain ⟨x, hx⟩ := horiginal e
      exact ⟨x, congrArg (old sem hB S) hx⟩
  · obtain ⟨c, rfl⟩ := local_exhaustive sem hB S z (subset_of_eq hz)
    refine Or.inl fun d => ?_
    obtain ⟨e, rfl⟩ := (localBelow sem hB S c).surjective d
    change SharpWitnessComposition.Short ((carrier sem hB S).cell (localCell sem hB S c)).2 _
    rw [row_local, local_index]
    exact S.short c (by simpa only [CellScheme.scope, local_index] using hz) e
end OrderedScopeRelocation

namespace OrdinaryRawScope
open AmalgamatedBoundaryPlan

structure Ready {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) : Prop where
  proper : ∀ d : Cell D, D.scope d ≠ A
  consistent : sem.IsConsistent
  coded : sem.IsCoded
  lifts : CanonicalCoatomBountiful.OldLifts sem
  complete : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d, D.cell d = J

section StepHelpers
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)

theorem left_proper : A.erase s.a ≠ A := fun he => Finset.notMem_erase s.a A (he.symm ▸ s.ha)
theorem right_proper : A.erase s.b ≠ A := fun he => Finset.notMem_erase s.b A (he.symm ▸ s.hb)

theorem plan_coverage (T : Finset ι) (hT : T ∈ s.plan) (hTA : T ≠ A) :
    T ⊆ A.erase s.a ∨ T ⊆ A.erase s.b := by
  rcases Finset.mem_union.mp hT with hT | hT
  · rcases Finset.mem_union.mp hT with hT | hT
    · exact Or.inl (s.left_plan.subset_of_mem hT)
    · exact Or.inr (s.right_plan.subset_of_mem hT)
  · exact (hTA (Finset.mem_singleton.mp hT)).elim

theorem left_height {k : ℕ} (hcard : A.card = k + 1) : (A.erase s.a).card = k := by
  rw [Finset.card_erase_of_mem s.ha, hcard]; omega

theorem right_height {k : ℕ} (hcard : A.card = k + 1) : (A.erase s.b).card = k := by
  rw [Finset.card_erase_of_mem s.hb, hcard]; omega
end StepHelpers

section RawBuild
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (H : Ready sem) (s : Step A) (hplan : D.plan = s.plan)

include hplan in
theorem left_mem : A.erase s.a ∈ D.plan :=
  hplan ▸ Finset.mem_union_left _ (Finset.mem_union_left _ s.left_plan.domain_mem)

include hplan in
theorem right_mem : A.erase s.b ∈ D.plan :=
  hplan ▸ Finset.mem_union_left _ (Finset.mem_union_right _ s.right_plan.domain_mem)

include hplan in
theorem overlap_mem : A.erase s.a ∩ A.erase s.b ∈ D.plan := by
  rw [hplan, erased_inter]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.common_left)

include hplan in
theorem coverage (C : Finset ι) (hC : C ∈ D.plan) (hCA : C ≠ A) :
    C ⊆ A.erase s.a ∨ C ⊆ A.erase s.b := plan_coverage s C (hplan ▸ hC) hCA

private def bottomProfile (j : ℕ) : CanonicalFieldLayer.Profile sem j (Cell D) id :=
  ⟨fun _ => ⊥, ⟨fun _ => (extVisibilityReplace_bot _ _).symm,
    fun c => by simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot (sem.E c),
    fun _ b _ _ => ⟨b, rfl, le_rfl⟩⟩, rfl, fun _ => bot_ne_top⟩

def one (hA : 1 ≤ A.card) (hg : ∀ d : Cell D, D.grade d ≤ 1)
    (hL : 1 ≤ (A.erase s.a).card) (hR : 1 ≤ (A.erase s.b).card) :
    OrdinaryScopeOperator.Core sem 1 where
  carrier := CanonicalOneCoatom.scheme sem hA
  rows := CanonicalOneCoatom.rows sem hA H.proper hg
  plan := rfl
  original := OrderEmbedding.ofStrictMono (CanonicalOneCoatom.old sem hA)
    (SourceLayerCarrier.old_order _ _ _ _ _)
  index d := SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)
  coverage d := by
    obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration D
      (CanonicalFieldLayer.Profile sem 1 (Cell D) id) 1 (by decide) hA).surjective d
    rcases x with c | q
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst (SourceLayerCarrier.cell_toCell _ _ _ _ _ _))
  row := CanonicalFieldLayer.inherited_row sem 1 (Cell D) id (by decide) hA H.proper hg
  consistent := CanonicalFieldLayer.consistent sem 1 (Cell D) id (by decide) hA
    H.proper hg H.consistent
  coded := CanonicalSeedCoding.fieldLayer sem 1 (Cell D) id (by decide) hA H.proper hg H.coded
  bountiful := CanonicalOneCoatom.bountiful sem hA H.proper hg H.lifts
    (left_mem s hplan) (right_mem s hplan) (left_proper s) (right_proper s)
    hL hR (overlap_mem s hplan) (coverage s hplan)
    (fun C hC hCA hc => H.complete (C, 1) (Plan.mem_gradedPlan.mpr ⟨hC, Nat.zero_lt_one, hc⟩) hCA)
  grade := (CanonicalFieldLayer.data sem 1 (Cell D) id (by decide) hA H.proper hg).max_grade
  complete J hJ hj := by
    have hj1 : J.2 = 1 := by have := (Plan.mem_gradedPlan.mp hJ).2.1; omega
    by_cases hJA : J.1 = A
    · exact ⟨(CanonicalFieldLayer.controller sem 1 (Cell D) id (by decide) hA
        (bottomProfile sem 1)).1,
        (CanonicalFieldLayer.controller sem 1 (Cell D) id (by decide) hA
          (bottomProfile sem 1)).2.trans (Prod.ext hJA.symm hj1.symm)⟩
    · obtain ⟨d, hd⟩ := H.complete J hJ hJA
      exact ⟨CanonicalOneCoatom.old sem hA d,
        (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)).trans hd⟩
  short := CanonicalFieldLayer.full_source_short sem 1 (Cell D) id (by decide) hA H.proper hg
  render := CanonicalFieldLayer.sectionOf sem 1 (Cell D) id (by decide) hA H.proper hg
  readback := CanonicalFieldLayer.section_old sem 1 (Cell D) id (by decide) hA H.proper hg
  lawful := CanonicalFieldLayer.section_lawful sem 1 (Cell D) id (by decide) hA H.proper hg
  bound := CanonicalFieldLayer.section_bound sem 1 (Cell D) id (by decide) hA H.proper hg
  support := CanonicalFieldLayer.section_supported sem 1 (Cell D) id (by decide) hA H.proper hg
  agreement hp ht hq htq := CanonicalFieldLayer.section_agreement sem 1 (Cell D) id
    (by decide) hA H.proper hg hp ht hq htq

def higherAt (m : ℕ) (hA : m + 2 ≤ A.card) (hg : ∀ d : Cell D, D.grade d ≤ m + 2)
    (hL : m + 2 ≤ (A.erase s.a).card) (hR : m + 2 ≤ (A.erase s.b).card) :
    OrdinaryScopeOperator.Core sem (m + 2) where
  carrier := CanonicalRecursiveContract.carrierAt sem m hA
  rows := CanonicalRecursiveSemantics.rowsAt sem H.proper m hA
  plan := CanonicalRecursiveBoundaryTransport.plan_eq sem (m + 2) hA
  original := CanonicalRecursiveInventory.boundary sem (m + 2) hA
  index := CanonicalRecursiveInventory.boundary_cell sem (m + 2) hA
  coverage d := by
    rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem)
      (m + 2) hA d with ⟨c, rfl⟩ | ⟨_, _, _, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst he)
  row := CanonicalRecursiveLiteralRows.rowAt sem H.proper m hA
  consistent := CanonicalRecursiveSemantics.consistentAt sem H.proper H.consistent m hA
  coded := CanonicalRecursiveCoding.codedAt sem H.proper H.coded m hA
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound sem (m + 2) hA hg) (by omega : 0 < m + 2)
    intro C T j hC hT hj hCT
    rw [CanonicalRecursiveBoundaryTransport.plan_eq] at hC hT
    exact CanonicalRecursiveInitialized.liftAt sem H.proper H.consistent H.lifts
      (left_mem s hplan) (right_mem s hplan) (left_proper s) (right_proper s)
      (overlap_mem s hplan) (coverage s hplan) m hA hL hR
      (fun C hC hCA j hj hjC _ => H.complete (C, j) (Plan.mem_gradedPlan.mpr ⟨hC, hj, hjC⟩) hCA)
      hC hT ⟨hCT, le_rfl⟩ hj
  grade := CanonicalRecursiveCoverage.grade_bound sem (m + 2) hA hg
  complete := CanonicalRecursiveCoverage.complete_through sem (m + 2) hA H.complete
  short := (CanonicalRecursiveSemantics.stateAt sem H.proper m hA).full_short
  render := fun hp ht => (CanonicalRecursiveSemantics.stateAt sem H.proper m hA).sectionOf
    hA (hp.toBelow (A, A.card)) ht
  readback := fun hp ht => (CanonicalRecursiveSemantics.stateAt sem H.proper m hA).section_boundary
    hA (hp.toBelow (A, A.card)) ht
  lawful := by
    intro p hp ht G θ hG hθ
    exact ((CanonicalRecursiveSemantics.stateAt sem H.proper m hA).section_lawful
      hA (hp.toBelow (A, A.card)) ht hG hθ).toRespects fun d =>
      ⟨(CanonicalRecursiveContract.carrierAt sem m hA).isPlan.subset_of_mem
        ((CanonicalRecursiveContract.carrierAt sem m hA).scope_mem_plan d),
        (CanonicalRecursiveCoverage.grade_bound sem (m + 2) hA hg d).trans hA⟩
  bound := fun hp ht => (CanonicalRecursiveSemantics.stateAt sem H.proper m hA).section_bound
    hA (hp.toBelow (A, A.card)) ht
  support := fun hp ht => (CanonicalRecursiveSemantics.stateAt sem H.proper m hA).section_supported
    hA (hp.toBelow (A, A.card)) ht
  agreement := fun hp ht hq htq =>
    (CanonicalRecursiveSemantics.stateAt sem H.proper m hA).section_agreement
      hA (hp.toBelow (A, A.card)) ht (hq.toBelow (A, A.card)) htq

def build (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1) : OrdinaryScopeOperator.Core sem k := by
  let s := Classical.choose (exists_step D.isPlan (by omega : 2 ≤ A.card))
  have hplan := Classical.choose_spec (exists_step D.isPlan (by omega : 2 ≤ A.card))
  have hL := (left_height s hcard).ge
  have hR := (right_height s hcard).ge
  have hg (d : Cell D) : D.grade d ≤ k := by
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), H.proper d⟩)
    have := D.grade_le_card_scope d; omega
  rcases k with _ | _ | m
  · omega
  · exact one sem H s hplan.symm (by omega) hg hL hR
  · exact higherAt sem H s hplan.symm m (by omega) hg hL hR
end RawBuild

theorem completed_highest_row {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {k : ℕ} (S : OrdinaryScopeOperator.Core sem k)
    (hk : 0 < k) (hcard : A.card = k + 1)
    (c₀ : Cell (S.finish hk hcard).carrier)
    (hc : (S.finish hk hcard).carrier.grade c₀ = k + 1)
    (d : (S.finish hk hcard).carrier.below ((S.finish hk hcard).carrier.cell c₀)) :
    (S.finish hk hcard).rows.E c₀ d = ⊥ := by
  dsimp only [OrdinaryScopeOperator.Core.finish] at c₀ hc d ⊢
  rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c₀ with ⟨c, rfl⟩ | rfl
  · have hg : S.carrier.grade c = k + 1 := (congrArg Prod.snd
      (MaximalFullLayer.old_index S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c)).symm.trans hc
    have := S.grade c; omega
  · exact OrdinaryScopeMute.apex_row S.carrier S.rows k (k + 1) S.grade (Nat.lt_succ_self k) hcard.ge d
end OrdinaryRawScope

namespace OrdinaryScopeIteration
section Iter
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}
  (sem₀ : Semantics D₀) (F₀ : Finset (Finset ι)) (N : ℕ) (G : Finset ExtOrd) (θ : ExtOrd)

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

variable {sem₀ F₀ N G θ} {F : Finset (Finset ι)}

def step (X : State sem₀ F₀ N G θ F) {B : Finset ι} (hB : B ∈ D₀.plan) (hnew : B ∉ F)
    (hready : ∀ C ∈ D₀.plan, C ⊂ B → C ∈ F) (k : ℕ) (hk : 0 < k) (hcard : B.card = k + 1)
    (hBA : B ≠ A) (hN : k + 1 ≤ N)
    (hG : ∀ z ∈ G, SelfVis N z) (hθ : SelfVis N θ) (htθ : θ ≠ ⊤) (hθG : θ ∈ G) :
    State sem₀ F₀ N G θ (insert B F) := by
  classical
  have hBX : B ∈ X.carrier.plan := X.plan.symm ▸ hB
  have sep : OrderedScopeRelocation.Separated (D := X.carrier) (B := B) :=
    fun d hd => hnew (X.closed _ (X.occupied d) B hB hd)
  have hrdy : OrdinaryRawScope.Ready (ScopeBoundary.rows X.carrier B hBX X.rows) :=
    { proper := fun d he => sep (ScopeBoundary.toCell X.carrier B hBX d) (subset_of_eq he.symm)
      consistent := ScopeBoundary.consistent _ _ _ _ X.consistent
      coded := ScopeBoundary.coded _ _ _ _ X.coded
      complete := fun J hJ hJB => by
        have hm := Plan.mem_gradedPlan.mp hJ
        have hmem : J.1 ∈ D₀.plan := X.plan ▸ (Finset.mem_inter.mp hm.1).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_inter.mp hm.1).2
        obtain ⟨d, hd⟩ := X.complete J (Plan.mem_gradedPlan.mpr ⟨hmem, hm.2⟩)
          (hready J.1 hmem (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJB⟩))
        obtain ⟨e, he⟩ := ScopeBoundary.exhaustive X.carrier B hBX
          (by change (X.carrier.cell d).1 ⊆ B; rwa [hd])
        exact ⟨e, (congrArg X.carrier.cell he).trans hd⟩
      lifts := fun I J hI hJ hJB h => by
        have hm := Plan.mem_gradedPlan.mp hJ
        have hmem : J.1 ∈ D₀.plan := X.plan ▸ (Finset.mem_inter.mp hm.1).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_inter.mp hm.1).2
        have hi := Plan.mem_gradedPlan.mp hI
        have himem : I.1 ∈ D₀.plan := X.plan ▸ (Finset.mem_inter.mp hi.1).1
        have hb := X.lifts I J (Plan.mem_gradedPlan.mpr ⟨himem, hi.2⟩)
          (Plan.mem_gradedPlan.mpr ⟨hmem, hm.2⟩)
          (hready J.1 hmem (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJB⟩)) h
        intro p q γ hp hq hγ hc
        exact bountiful_of_equiv h h
          (ScopeBoundary.belowEquiv X.carrier B hBX J hsub)
          (ScopeBoundary.belowEquiv X.carrier B hBX I (h.1.trans hsub)) (fun _ => rfl)
          (ScopeBoundary.respects_iff _ _ _ _ _ _) (ScopeBoundary.respects_iff _ _ _ _ _ _)
          hb rfl p q γ hp hq hγ hc }
  let raw := OrdinaryRawScope.build _ hrdy k hk hcard
  let L := raw.finish hk hcard
  let K := OrderedScopeRelocation.carrier X.rows hBX L
  let ss := OrderedScopeRelocation.rows X.rows hBX L sep
  let l := OrderedScopeRelocation.old X.rows hBX L
  let r := OrderedScopeRelocation.localCell X.rows hBX L
  have hg : ∀ z ∈ G, SelfVis (k + 1) z := fun z hz => selfVis_mono (hG z hz) hN
  have hθ' : SelfVis (k + 1) θ := selfVis_mono hθ hN
  refine
    { carrier := K, rows := ss, plan := X.plan
      consistent := OrderedScopeRelocation.consistent X.rows hBX L sep X.consistent
      coded := OrderedScopeRelocation.coded X.rows hBX L sep X.coded
      original := X.original.trans (OrderEmbedding.ofStrictMono l
        (OrderedScopeRelocation.old_order X.rows hBX L))
      index := fun d => (OrderedScopeRelocation.old_index X.rows hBX L _).trans (X.index d)
      row := fun c d => (OrderedScopeRelocation.row_old X.rows hBX L sep (X.original c)
        ⟨X.original d.1, by rw [X.index, X.index]; exact d.2⟩).trans (X.row c d)
      exhaustive := fun z hz => by
        rcases OrderedScopeRelocation.classify X.rows hBX L z with ⟨d, rfl⟩ | hd
        · obtain ⟨e, rfl⟩ := X.exhaustive d
            (by simpa only [K, CellScheme.scope, OrderedScopeRelocation.old_index X.rows hBX L] using hz)
          exact ⟨e, rfl⟩
        · exact False.elim (hnew (X.initial_le (hd ▸ hz)))
      occupied := fun z => by
        rcases OrderedScopeRelocation.classify X.rows hBX L z with ⟨d, rfl⟩ | hd
        · change (OrderedScopeRelocation.carrier X.rows hBX L).scope _ ∈ insert B F
          simpa only [CellScheme.scope, OrderedScopeRelocation.old_index X.rows hBX L] using
            (Finset.mem_insert_of_mem (X.occupied d) : X.carrier.scope d ∈ insert B F)
        · exact hd ▸ Finset.mem_insert_self B F
      initial_le := fun _ h => Finset.mem_insert_of_mem (X.initial_le h)
      scopes := fun C hC => (Finset.mem_insert.mp hC).elim (fun h => h ▸ hB) (fun h => X.scopes h)
      proper := by simpa only [Finset.mem_insert, not_or] using And.intro hBA.symm X.proper
      closed := fun C hC T hT hTC => by
        rcases Finset.mem_insert.mp hC with rfl | hC
        · by_cases he : T = C
          · exact he ▸ Finset.mem_insert_self C F
          · exact Finset.mem_insert_of_mem (hready T hT (Finset.ssubset_iff_subset_ne.mpr ⟨hTC, he⟩))
        · exact Finset.mem_insert_of_mem (X.closed C hC T hT hTC)
      complete := fun J hJ hJF => by
        rcases Finset.mem_insert.mp hJF with hJB | hJF
        · have hm := Plan.mem_gradedPlan.mp hJ
          obtain ⟨d, hd⟩ := raw.finish_complete hk hcard J (by
            rw [L.plan]
            exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr
              ⟨X.plan.symm ▸ hm.1, Finset.mem_powerset.mpr (subset_of_eq hJB)⟩, hm.2⟩)
          exact ⟨r d, (OrderedScopeRelocation.local_index X.rows hBX L d).trans hd⟩
        · obtain ⟨d, hd⟩ := X.complete J hJ hJF
          exact ⟨l d, (OrderedScopeRelocation.old_index X.rows hBX L d).trans hd⟩
      lifts := fun I J hI hJ hJF h => by
        rcases Finset.mem_insert.mp hJF with hJB | hJF
        · exact OrderedScopeRelocation.local_lift X.rows hBX L sep h
            (X.plan.symm ▸ hI) (X.plan.symm ▸ hJ) (subset_of_eq hJB)
        · exact OrderedScopeRelocation.old_lift X.rows hBX L sep h
            (fun hBJ => hnew (X.closed _ hJF B hB hBJ)) (X.lifts I J hI hJ hJF h)
      classification := OrderedScopeRelocation.ownerClassification X.rows hBX L sep
        X.original X.classification
      mute := fun z hz hn => by
        rcases OrderedScopeRelocation.classify X.rows hBX L z with ⟨c, rfl⟩ | hc
        · exact (OrderedScopeRelocation.row_old X.rows hBX L sep c ⟨c, GradedLe.refl _⟩).trans
            (X.mute c
              (by simpa only [K, CellScheme.scope, CellScheme.grade,
                    OrderedScopeRelocation.old_index X.rows hBX L] using hz)
              (by simpa only [K, CellScheme.scope,
                    OrderedScopeRelocation.old_index X.rows hBX L] using hn))
        · obtain ⟨c, rfl⟩ := OrderedScopeRelocation.local_exhaustive X.rows hBX L z (subset_of_eq hc)
          have hg' : L.carrier.grade c = k + 1 := by
            simpa only [K, CellScheme.grade, OrderedScopeRelocation.local_index X.rows hBX L,
              hcard] using hz.trans (congrArg Finset.card hc)
          exact (OrderedScopeRelocation.row_local X.rows hBX L sep c ⟨c, GradedLe.refl _⟩).trans
            (OrdinaryRawScope.completed_highest_row raw hk hcard c hg' _)
      render := fun hp hb => OrderedScopeRelocation.render X.rows hBX L (X.lawful hp hb)
        (fun d => ne_top_of_le_ne_top htθ (X.bound hp hb d)) G θ
      readback := fun hp hb d =>
        (OrderedScopeRelocation.render_old X.rows hBX L (X.lawful hp hb) _ _).trans
          (X.readback hp hb d)
      lawful := fun hp hb => OrderedScopeRelocation.render_lawful X.rows hBX L sep
        (X.lawful hp hb) _ hg hθ'
      bound := fun hp hb => OrderedScopeRelocation.render_bound X.rows hBX L
        (X.lawful hp hb) _ hg hθ' (X.bound hp hb)
      support := fun hp hb => OrderedScopeRelocation.render_supported X.rows hBX L
        (X.lawful hp hb) _ hN hG hθ' hθG (X.support hp hb)
      agreement := by
        intro p q hp hb hq hqb γ hγ hγθ he
        exact OrderedScopeRelocation.render_agreement X.rows hBX L
          (X.lawful hp hb) _ (X.lawful hq hqb) _ hg hθ' hγ hγθ
          (X.agreement hp hb hq hqb hγ hγθ he) }

theorem exists_completed
    (hN : ∀ B ∈ D₀.plan, B ≠ A → B.card ≤ N)
    (hsmall : ∀ B ∈ D₀.plan, B.card ≤ 1 → B ∈ F₀)
    (hG : ∀ z ∈ G, SelfVis N z) (hθ : SelfVis N θ) (htθ : θ ≠ ⊤) (hθG : θ ∈ G)
    (X₀ : State sem₀ F₀ N G θ F₀) :
    ∃ F', Nonempty (State sem₀ F₀ N G θ F') ∧ ∀ B ∈ D₀.plan, B ≠ A → B ∈ F' := by
  classical
  suffices ∀ n, ∀ (F : Finset (Finset ι)), (D₀.plan \ insert A F).card = n →
      State sem₀ F₀ N G θ F →
      ∃ F', Nonempty (State sem₀ F₀ N G θ F') ∧ ∀ B ∈ D₀.plan, B ≠ A → B ∈ F' from
    this _ F₀ rfl X₀
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn X
    by_cases hempty : (D₀.plan \ insert A F).Nonempty
    · obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image (D₀.plan \ insert A F) Finset.card hempty
      have hBp := (Finset.mem_sdiff.mp hB).1
      have hBA : B ≠ A := fun he => (Finset.mem_sdiff.mp hB).2 (he ▸ Finset.mem_insert_self A F)
      have hnew : B ∉ F := fun hf => (Finset.mem_sdiff.mp hB).2 (Finset.mem_insert_of_mem hf)
      have hready : ∀ C ∈ D₀.plan, C ⊂ B → C ∈ F := fun C hC hCB => by
        by_contra hc
        have hCA : C ≠ A := fun he => by
          have := Finset.card_lt_card hCB
          have := Finset.card_le_card (D₀.isPlan.subset_of_mem hBp)
          subst C; omega
        exact (not_le_of_gt (Finset.card_lt_card hCB)) (hmin C (Finset.mem_sdiff.mpr
          ⟨hC, by simp only [Finset.mem_insert, not_or]; exact ⟨hCA, hc⟩⟩))
      have htwo : 2 ≤ B.card := by
        by_contra hh; exact hnew (X.initial_le (hsmall B hBp (by omega)))
      let Y := step X hBp hnew hready (B.card - 1) (by omega) (by omega) hBA
        (by have := hN B hBp hBA; omega) hG hθ htθ hθG
      have hlt : (D₀.plan \ insert A (insert B F)).card < n := by
        rw [← hn]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun C hC => ?_, fun he => ?_⟩)
        · simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hC ⊢
          exact ⟨hC.1, hC.2.1, hC.2.2.2⟩
        · have hm := he.symm ▸ hB
          simp only [Finset.mem_sdiff, Finset.mem_insert, true_or, or_true, not_true_eq_false,
            and_false] at hm
      exact ih _ hlt _ rfl Y
    · exact ⟨F, ⟨X⟩, fun B hB hBA => by
        by_contra hf
        exact hempty ⟨B, Finset.mem_sdiff.mpr
          ⟨hB, by simp only [Finset.mem_insert, not_or]; exact ⟨hBA, hf⟩⟩⟩⟩
end Iter
end OrdinaryScopeIteration

namespace OrdinaryPredecessorSupply
open CanonicalRecursiveContract

def recFace {ι : Type*} [DecidableEq ι] {A B : Finset ι}
    {D : CellScheme A} {E : CellScheme B} {sem : Semantics D} {old : Semantics E}
    (F : ExactSemanticFace old sem) (hB : ¬ A ⊆ B)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (n : ℕ) (hA : n + 3 ≤ A.card) :
    ExactSemanticFace old (CanonicalRecursiveSemantics.rows sem hp n hA) where
  map := F.map.trans (boundary sem n hA).toEmbedding
  index c := (CanonicalRecursiveInventory.boundary_cell sem (n + 3) hA (F.map c)).trans (F.index c)
  exhaustive z hz := by
    rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem)
      (n + 3) hA z with ⟨d, rfl⟩ | ⟨_, _, _, he⟩
    · obtain ⟨c, rfl⟩ := F.exhaustive d (by
        change (D.cell d).1 ⊆ B
        change ((carrier sem n hA).cell (boundary sem n hA d)).1 ⊆ B at hz
        simpa only [CanonicalRecursiveInventory.boundary_cell] using hz)
      exact ⟨c, rfl⟩
    · change ((carrier sem n hA).cell z).1 ⊆ B at hz; rw [he] at hz; exact (hB hz).elim
  row c d := (CanonicalRecursiveLiteralRows.row sem hp n hA (F.map c) (F.belowMap c d)).trans
    (F.row c d)

structure Output {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
    {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
    (N : ℕ) (G : Finset ExtOrd) (θ : ExtOrd) where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = R
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  original : Cell I.boundary ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = I.boundary.cell d
  leftFace : ExactSemanticFace I.leftRows rows
  rightFace : ExactSemanticFace I.rightRows rows
  left_map : ∀ d, leftFace.map d = original (I.leftFace.map d)
  right_map : ∀ d, rightFace.map d = original (I.rightFace.map d)
  left_order : StrictMono leftFace.map
  right_order : StrictMono rightFace.map
  grade_bound : ∀ d, carrier.grade d ≤ N
  full_below : ∀ d, carrier.scope d = A → carrier.grade d < N
  complete : ∀ J ∈ Plan.gradedPlan R, J.1 ≠ A ∨ J.2 < N → ∃ d, carrier.cell d = J
  proper_lift : ∀ CI BJ, CI ∈ Plan.gradedPlan R → BJ ∈ Plan.gradedPlan R →
    BJ.1 ≠ A → (h : GradedLe CI BJ) → CappedLift rows h
  lower_lift : ∀ CI BJ, CI ∈ Plan.gradedPlan R → BJ ∈ Plan.gradedPlan R →
    (h : GradedLe CI BJ) → BJ.2 < N → CappedLift rows h
  mute : ∀ d, carrier.grade d = N → carrier.scope d ≠ B →
    rows.E d ⟨d, GradedLe.refl _⟩ = ⊥
  classification : OrderedScopeRelocation.OwnerClassification rows original
  render : ∀ {p : Cell I.boundary → ExtOrd}, RespectsSemantics I.rows p → (∀ d, p d ≤ θ) →
    Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ) d,
    render hp hb (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ),
    RespectsSemantics rows (render hp hb)
  bound : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ) d, render hp hb d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ) d,
    Supported N (G : Set ExtOrd) p (render hp hb d)
  agreement : ∀ {p q} (hp : RespectsSemantics I.rows p) (hb : ∀ d, p d ≤ θ)
    (hq : RespectsSemantics I.rows q) (hqb : ∀ d, q d ≤ θ) {γ}, γ ∈ G → γ ≤ θ →
    Agree p q γ → Agree (render hp hb) (render hq hqb) γ

def build {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
    {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
    {G : Finset ExtOrd} {θ : ExtOrd} (n : ℕ)
    (hBA : B ≠ A) (hCA : C ≠ A) (hunion : A = B ∪ C)
    (hcard : A.card = n + 5) (hB : B.card = n + 4) (hC : C.card < n + 4)
    (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hθ : SelfVis (n + 4) θ)
    (htθ : θ ≠ ⊤) (hθG : θ ∈ G) : Output I (n + 4) G θ := by
  let F₀ : Finset (Finset ι) := I.boundary.plan.filter fun S => S ⊆ B ∨ S ⊆ C
  have hBmem : B ∈ I.boundary.plan := I.leftPlan_le I.leftScheme.isPlan.domain_mem
  have hCmem : C ∈ I.boundary.plan := I.rightPlan_le I.rightScheme.isPlan.domain_mem
  have hocc (d : Cell I.boundary) : I.boundary.scope d ∈ F₀ :=
    Finset.mem_filter.mpr ⟨I.boundary.scope_mem_plan d,
      (I.occupied_iff (I.boundary.cell_mem d)).mp ⟨d, rfl⟩⟩
  let seed : OrdinaryScopeIteration.State I.rows F₀ (n + 4) G θ F₀ :=
    { carrier := I.boundary, rows := I.rows, plan := rfl
      consistent := I.consistent, coded := I.coded
      original := (OrderIso.refl _).toOrderEmbedding
      index := fun _ => rfl, row := fun _ _ => rfl, exhaustive := fun d _ => ⟨d, rfl⟩
      occupied := hocc, initial_le := Finset.Subset.refl _
      scopes := fun _ h => (Finset.mem_filter.mp h).1
      proper := fun h => by
        rcases (Finset.mem_filter.mp h).2 with hb | hc
        · exact hBA (Finset.Subset.antisymm (I.isPlan.subset_of_mem hBmem) hb)
        · exact hCA (Finset.Subset.antisymm (I.isPlan.subset_of_mem hCmem) hc)
      closed := fun _ hS _ hT ht =>
        Finset.mem_filter.mpr ⟨hT, (Finset.mem_filter.mp hS).2.imp ht.trans ht.trans⟩
      complete := fun J hJ h => (I.occupied_iff hJ).mpr (Finset.mem_filter.mp h).2
      lifts := fun CI BJ hCI hBJ hscope h => by
        by_cases he : CI = BJ
        · subst BJ; exact lift_refl
        · exact I.inherited_lift hCI hBJ h he (Finset.mem_filter.mp hscope).2
      classification := fun _ => Or.inr fun d => ⟨d.1, rfl⟩
      mute := fun c _ hn => (hn (hocc c)).elim
      render := fun {p} _ _ => p, readback := fun _ _ _ => rfl
      lawful := fun hp _ => hp, bound := fun _ hb => hb
      support := fun _ _ => supported_field (n + 4) (G : Set ExtOrd) _
      agreement := by intro p q hp hb hq hqb γ hγ hγθ he; exact he }
  have hx := OrdinaryScopeIteration.exists_completed
    (fun S hS hSA => by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨I.isPlan.subset_of_mem hS, hSA⟩)
      omega)
    (fun S hS hc => Finset.mem_filter.mpr ⟨hS, by
      by_cases hs : S.Nonempty
      · obtain ⟨x, hx⟩ := hs
        have hxa := I.isPlan.subset_of_mem hS hx
        rw [hunion, Finset.mem_union] at hxa
        have he : ∀ y ∈ S, y = x := fun y hy => Finset.card_le_one.mp hc y hy x hx
        exact hxa.imp (fun h y hy => by rw [he y hy]; exact h)
          (fun h y hy => by rw [he y hy]; exact h)
      · exact Or.inl (by rw [Finset.not_nonempty_iff_eq_empty.mp hs]; exact Finset.empty_subset B)⟩)
    hG hθ htθ hθG seed
  let st := Classical.choice (Classical.choose_spec hx).1
  have hdone : ∀ S ∈ R, S ≠ A → S ∈ Classical.choose hx := (Classical.choose_spec hx).2
  have hprop (d : Cell st.carrier) : st.carrier.scope d ≠ A := fun he =>
    st.proper (by have h := st.occupied d; rwa [he] at h)
  have hcompP {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) (hJA : J.1 ≠ A) :
      ∃ d, st.carrier.cell d = J :=
    st.complete J hJ (hdone J.1 (Plan.mem_gradedPlan.mp hJ).1 hJA)
  have hliftsP : CanonicalCoatomBountiful.OldLifts st.rows := fun CI BJ hCI hBJ hJA h => by
    rw [st.plan] at hCI hBJ
    exact st.lifts CI BJ hCI hBJ (hdone BJ.1 (Plan.mem_gradedPlan.mp hBJ).1 hJA) h
  have ht : n + 3 ≤ A.card := by omega
  let C' := carrier st.rows n ht
  let R' := CanonicalRecursiveSemantics.rows st.rows hprop n ht
  let old := CanonicalRecursiveInventory.boundary st.rows (n + 3) ht
  let orig := st.original.trans old
  have hcov (d : Cell C') : (∃ c, old c = d) ∨ C'.scope d = A ∧ C'.grade d ≤ n + 3 := by
    rcases RecursiveSourceCarrier.classify st.carrier
        (CanonicalRecursiveInventory.Profile st.rows) (n + 3) ht d with ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · refine Or.inr ⟨congrArg Prod.fst he, ?_⟩
      change (C'.cell d).2 ≤ _; rw [he]; exact hj
  have hgbound (d : Cell C') : C'.grade d ≤ n + 4 := by
    rcases hcov d with ⟨c, rfl⟩ | ⟨_, hg⟩
    · change (C'.cell (old c)).2 ≤ _; rw [CanonicalRecursiveInventory.boundary_cell]
      have hs := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨st.carrier.isPlan.subset_of_mem (st.carrier.scope_mem_plan c), hprop c⟩)
      have := st.carrier.grade_le_card_scope c; change st.carrier.grade c ≤ _; omega
    · omega
  let initFace {T : Finset ι} {DT : CellScheme T} {semT : Semantics DT}
      (E : ExactSemanticFace semT I.rows) (hT : T ⊆ B ∨ T ⊆ C) :
      ExactSemanticFace semT st.rows :=
    { map := E.map.trans st.original.toEmbedding
      index := fun d => (st.index (E.map d)).trans (E.index d)
      exhaustive := fun d hd => by
        obtain ⟨e, rfl⟩ := st.exhaustive d (Finset.mem_filter.mpr
          ⟨by have hp := st.carrier.scope_mem_plan d; rwa [st.plan] at hp,
            hT.imp hd.trans hd.trans⟩)
        obtain ⟨c, rfl⟩ := E.exhaustive e (by simpa only [CellScheme.scope, st.index] using hd)
        exact ⟨c, rfl⟩
      row := fun c d => (st.row (E.map c) (E.belowMap c d)).trans (E.row c d) }
  have hbelow_old (c : Cell st.carrier) (d : C'.below (C'.cell (old c))) :
      ∃ e : st.carrier.below (st.carrier.cell c), old e.1 = d.1 := by
    rcases hcov d.1 with ⟨e, he⟩ | ⟨hs, _⟩
    · refine ⟨⟨e, ?_⟩, he⟩
      have hd := d.2
      rw [← he, CanonicalRecursiveInventory.boundary_cell,
        CanonicalRecursiveInventory.boundary_cell] at hd
      exact hd
    · have hd := d.2.1; change C'.scope d.1 ⊆ (C'.cell (old c)).1 at hd
      rw [hs, CanonicalRecursiveInventory.boundary_cell] at hd
      exact (hprop c (Finset.Subset.antisymm
        (st.carrier.isPlan.subset_of_mem (st.carrier.scope_mem_plan c)) hd)).elim
  let recSt := CanonicalRecursiveSemantics.state st.rows hprop n ht
  let renderFn {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p)
      (hb : ∀ d, p d ≤ θ) : Cell C' → ExtOrd :=
    recSt.sectionOf ht ((st.lawful hp hb).toBelow (A, A.card))
      (fun d => ne_top_of_le_ne_top htθ (st.bound hp hb d)) G θ
  exact
    { carrier := C', rows := R'
      plan := (CanonicalRecursiveBoundaryTransport.plan_eq _ _ _).trans st.plan
      consistent := CanonicalRecursiveSemantics.consistent _ hprop st.consistent n ht
      coded := CanonicalRecursiveCoding.coded _ hprop st.coded n ht
      original := orig
      index := fun d => (CanonicalRecursiveInventory.boundary_cell _ _ _ _).trans (st.index d)
      leftFace := recFace (initFace I.leftFace (Or.inl (Finset.Subset.refl B)))
        (fun h => hBA (Finset.Subset.antisymm (I.isPlan.subset_of_mem hBmem) h)) hprop n ht
      rightFace := recFace (initFace I.rightFace (Or.inr (Finset.Subset.refl C)))
        (fun h => hCA (Finset.Subset.antisymm (I.isPlan.subset_of_mem hCmem) h)) hprop n ht
      left_map := fun _ => rfl, right_map := fun _ => rfl
      left_order := old.strictMono.comp (st.original.strictMono.comp I.left_order)
      right_order := old.strictMono.comp (st.original.strictMono.comp I.right_order)
      grade_bound := hgbound
      full_below := fun d hd => by
        rcases hcov d with ⟨c, rfl⟩ | ⟨_, hg⟩
        · exact (hprop c ((congrArg Prod.fst
            (CanonicalRecursiveInventory.boundary_cell st.rows (n + 3) ht c)).symm.trans hd)).elim
        · omega
      complete := fun J hJ hs => by
        rcases hs with hJA | hj
        · obtain ⟨d, hd⟩ := hcompP hJ hJA
          exact ⟨old d, (CanonicalRecursiveInventory.boundary_cell _ _ _ _).trans hd⟩
        · exact CanonicalRecursiveCoverage.complete_through st.rows (n + 3) ht
            (fun _ hJ' hJA => hcompP (by rwa [st.plan] at hJ') hJA) J
            (by rwa [CanonicalRecursiveBoundaryTransport.plan_eq, st.plan]) (by omega)
      proper_lift := fun CI BJ hCI hBJ hJA h =>
        CanonicalRecursiveBoundaryTransport.proper_lift _ hprop n ht h
          (fun hs => hJA (Finset.Subset.antisymm
            (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBJ).1) hs))
          (hliftsP CI BJ (by rwa [st.plan]) (by rwa [st.plan]) hJA h)
      lower_lift := fun CI BJ hCI hBJ h hg => by
        obtain ⟨s, hs⟩ := AmalgamatedBoundaryPlan.exists_step st.carrier.isPlan (by omega)
        have hL := OrdinaryRawScope.left_height s (k := n + 4) hcard
        have hR := OrdinaryRawScope.right_height s (k := n + 4) hcard
        exact CanonicalRecursiveInitialized.lift st.rows hprop st.consistent hliftsP
          (OrdinaryRawScope.left_mem s hs.symm) (OrdinaryRawScope.right_mem s hs.symm)
          (OrdinaryRawScope.left_proper s) (OrdinaryRawScope.right_proper s)
          (OrdinaryRawScope.overlap_mem s hs.symm) (OrdinaryRawScope.coverage s hs.symm)
          n ht (by omega) (by omega)
          (fun S hS hSA j hj hjS _ => hcompP (Plan.mem_gradedPlan.mpr
            ⟨show S ∈ I.boundary.plan from st.plan ▸ hS, hj, hjS⟩) hSA)
          (by rwa [st.plan]) (by rwa [st.plan]) h (by omega)
      mute := fun d hg hd => by
        rcases hcov d with ⟨c, rfl⟩ | ⟨_, hb⟩
        · have hc : st.carrier.grade c = n + 4 :=
            (congrArg Prod.snd
              (CanonicalRecursiveInventory.boundary_cell st.rows (n + 3) ht c)).symm.trans hg
          have hscope : st.carrier.scope c ≠ B := fun hb' =>
            hd ((congrArg Prod.fst
              (CanonicalRecursiveInventory.boundary_cell st.rows (n + 3) ht c)).trans hb')
          refine (CanonicalRecursiveLiteralRows.row st.rows hprop n ht c ⟨c, GradedLe.refl _⟩).trans ?_
          have hs := st.carrier.isPlan.subset_of_mem (st.carrier.scope_mem_plan c)
          have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hprop c⟩)
          have := st.carrier.grade_le_card_scope c
          have hsize : (st.carrier.scope c).card = n + 4 := by omega
          exact st.mute c (hc.trans hsize.symm) fun hi => by
            rcases (Finset.mem_filter.mp hi).2 with hl | hr
            · exact hscope (Finset.eq_of_subset_of_card_le hl (hB.trans_le hsize.ge))
            · have := Finset.card_le_card hr; omega
        · omega
      classification := fun z => by
        rcases hcov z with ⟨c, rfl⟩ | ⟨hs, _⟩
        · rcases st.classification c with hshort | horig
          · refine Or.inl fun d => ?_
            obtain ⟨e, he⟩ := hbelow_old c d
            have hd : d = ⟨old e.1, by
              rw [CanonicalRecursiveInventory.boundary_cell,
                CanonicalRecursiveInventory.boundary_cell]; exact e.2⟩ := Subtype.ext he.symm
            rw [hd, CanonicalRecursiveLiteralRows.row]
            change SharpWitnessComposition.Short (C'.cell (old c)).2 _
            rw [CanonicalRecursiveInventory.boundary_cell]; exact hshort e
          · refine Or.inr fun d => ?_
            obtain ⟨e, he⟩ := hbelow_old c d
            obtain ⟨x, hx⟩ := horig e
            exact ⟨x, (congrArg old hx).trans he⟩
        · exact Or.inl (recSt.full_short z hs)
      render := renderFn
      readback := fun hp hb d =>
        (recSt.section_boundary ht _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
          (selfVis_mono hθ (by omega)) (st.original d)).trans (st.readback hp hb d)
      lawful := fun hp hb =>
        (recSt.section_lawful ht _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
          (selfVis_mono hθ (by omega))).toRespects fun d =>
            ⟨C'.isPlan.subset_of_mem (C'.scope_mem_plan d), (hgbound d).trans (by omega)⟩
      bound := fun hp hb d =>
        recSt.section_bound ht _ _ (selfVis_mono hθ (by omega)) (st.bound hp hb) d
      support := fun hp hb d =>
        (recSt.section_supported ht _ _ (by omega) hθG d).substitute hG (st.support hp hb)
      agreement := by
        intro p q hp hb hq hqb γ hγ hγθ he
        exact recSt.section_agreement ht _ _ _ _ (fun z hz => selfVis_mono (hG z hz) (by omega))
          (selfVis_mono hθ (by omega)) hγ hγθ (st.agreement hp hb hq hqb hγ hγθ he) }
end OrdinaryPredecessorSupply
end
end VaughtConjecture.Knight

