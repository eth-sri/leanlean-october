/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedExtension
public import VaughtConjecture.Knight.LowOnlyPaddedLegal
public import VaughtConjecture.Knight.WholeDonorAttachment
public import VaughtConjecture.Knight.ActualLabelling
public import VaughtConjecture.Knight.TopSupportReceiving

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedAllCutoff
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration CanonicalPairedInverse RelativeLadderLayer
open AmalgamationPlan CoatomBoundaryExtension PaddedFaceLift
noncomputable section

section LayerFaces
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k)

private def layerFace {S : Finset ι} {E : CellScheme S} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ S) :
    ExactSemanticFace oldRows P.rows :=
  let L := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1))
    1 Nat.one_pos (by omega)
    (RelativeLadderLayer.separated I.boundary (GrowthOrderedBase.proper I hB hC))
    I.rows (baseRows I X T hA hB hC)
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (field I) (GrowthHigherSources.fields X 1) (GrowthOrderedBase.proper I hB hC)) G hT
  { map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ S at hz; rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }

private def privateFace : ExactSemanticFace I.rightRows P.rows :=
  layerFace P I.rightFace hC.not_ge
private def donorFace : ExactSemanticFace I.leftRows P.rows :=
  layerFace P I.leftFace hB.not_ge

private theorem inherited_lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CappedLift P.rows h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hv with hb | hc
  · exact (donorFace P).lift hb (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace P).lift hc (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

private def fullEquiv {V : Finset ι} {a : ℕ}
    (S : SemScheme a) (e : Fin a ↪ ι) (he : Finset.univ.image e = V)
    (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) P.rows) (j : ℕ) :
    S.scheme.below (Finset.univ, j) ≃ P.carrier.below (V, j) :=
  (show S.scheme.below (Finset.univ, j) ≃
      (AmalgamatedBoundary.pointImage S.scheme e he).below (V, j) from
    { toFun := fun d => ⟨d.1, (Finset.image_subset_image (Finset.subset_univ _)).trans he.subset, d.2.2⟩
      invFun := fun d => ⟨d.1, Finset.subset_univ _, d.2.2⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }).trans
    (G.belowEquiv (V, j) (Finset.Subset.refl _))

private theorem full_respects_iff {V : Finset ι} {a : ℕ}
    (S : SemScheme a) (e : Fin a ↪ ι) (he : Finset.univ.image e = V)
    (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) P.rows)
    (j : ℕ) (q : P.carrier.below (V, j) → ExtOrd) :
    RespectsSemanticsBelow P.rows (V, j) q ↔
      RespectsSemanticsBelow S.rows (Finset.univ, j) (q ∘ fullEquiv P S e he G j) := by
  have h := respects_iff_of_equiv (sem' := S.rows) (sem := P.rows)
    (fullEquiv P S e he G j) (fun d => (congrArg Prod.snd (G.index d.1)).symm)
    (fun d f => by
      change (S.scheme.cell d.1).1 ⊆ (S.scheme.cell f.1).1 ↔
        (P.carrier.cell (G.map d.1)).1 ⊆ (P.carrier.cell (G.map f.1)).1
      rw [G.index d.1, G.index f.1]
      exact (Finset.image_subset_image_iff e.injective).symm)
    (fun c d _ => (G.row c.1 (PointImageSemantics.belowEquiv S.scheme e he c.1 d)).symm)
    (q ∘ fullEquiv P S e he G j)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

private theorem lift_of_face {V : Finset ι} {a : ℕ} (O : SemScheme a)
    (e₀ : Fin a ↪ ι) (he₀ : Finset.univ.image e₀ = V) (hV : V ⊆ A)
    (G : ExactSemanticFace (PointImageSemantics.rows O.scheme e₀ he₀ O.rows) P.rows) (j : ℕ)
    (hl : ∀ (p : O.scheme.below (Finset.univ, j) → ExtOrd)
      (q : P.carrier.below (A, j) → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow O.rows (Finset.univ, j) p →
      RespectsSemanticsBelow P.rows (A, j) q → SelfVis j γ →
      (∀ d, min (q (CellScheme.below.mono (show GradedLe (V, j) (A, j) from ⟨hV, le_rfl⟩)
        (fullEquiv P O e₀ he₀ G j d))) γ = min (p d) γ) →
      ∃ r, RespectsSemanticsBelow P.rows (A, j) r ∧
        (∀ d, r (CellScheme.below.mono (show GradedLe (V, j) (A, j) from ⟨hV, le_rfl⟩)
          (fullEquiv P O e₀ he₀ G j d)) = p d) ∧
        ∀ d, min (r d) γ = min (q d) γ) :
    CappedLift P.rows (show GradedLe (V, j) (A, j) from ⟨hV, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let e := fullEquiv P O e₀ he₀ G j
  obtain ⟨r, hr, hread, hcap⟩ := hl (p ∘ e) q γ
    ((full_respects_iff P O e₀ he₀ G j p).mp hp) hq hγ (fun d => hag (e d))
  exact ⟨r, hr, hcap, fun d => by obtain ⟨x, rfl⟩ := e.surjective d; exact hread x⟩

private theorem one_side {V : Finset ι} {a : ℕ} (O : SemScheme a)
    (e₀ : Fin a ↪ ι) (he₀ : Finset.univ.image e₀ = V) (hV : V ⊆ A)
    (G : ExactSemanticFace (PointImageSemantics.rows O.scheme e₀ he₀ O.rows) P.rows)
    (incl : O.scheme.below (Finset.univ, 1) → I.boundary.below (A, 1))
    (pick : Cell O.scheme → Field I.right.scheme I.left.scheme)
    (sVal : State I.right.scheme I.left.scheme → Cell O.scheme → ExtOrd)
    (hid : ∀ x, CellScheme.below.mono (show GradedLe (V, 1) (A, 1) from ⟨hV, le_rfl⟩)
      (fullEquiv P O e₀ he₀ G 1 x) = GrowthPaddedCutTransport.baseEquiv P
        (GrowthOrderedBase.oldAt I X (by omega) (incl x)))
    (hbot : ∀ {p : O.scheme.below (Finset.univ, 1) → ExtOrd},
      RespectsSemanticsBelow O.rows (Finset.univ, 1) p →
      ∃ w, RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) w ∧
        ∀ d, w (GrowthOrderedBase.oldAt I X (by omega) (incl d)) = p d)
    (hfld : ∀ S, Admitted X 1 S → ∀ d : O.scheme.below (Finset.univ, 1),
      S.profile (field I (incl d).1) = S.profile (pick d.1))
    (hslaw : ∀ S, Admitted X 1 S → RespectsSemanticsBelow O.rows (Finset.univ, 1)
      (fun d => sVal S d.1))
    (hseq : ∀ S d, sVal S d = S.profile (pick d))
    (hprot : ∀ {S}, Admitted X 1 S →
      S.profile ∈ CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 1 →
      ∀ {B' : ℕ} {p' : O.scheme.below (Finset.univ, 1) → ExtOrd},
      RespectsSemanticsBelow O.rows (Finset.univ, 1) p' →
      (∀ d, min (p' d) (grid 1 B') = min (sVal S d.1) (grid 1 B')) →
      ∃ U, (∀ d, sVal U d.1 = p' d) ∧ Nonempty (ProtectedRepair X S.profile U 1 B')) :
    CappedLift P.rows (show GradedLe (V, 1) (A, 1) from ⟨hV, le_rfl⟩) := by
  apply lift_of_face P O e₀ he₀ hV G 1
  intro p q γ hp hq hγ hag
  let b := GrowthPaddedCutTransport.baseEquiv P
  have hq' : RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) (q ∘ b) :=
    (GrowthPaddedCutTransport.base_respects_iff P _).mpr
      (by simpa only [b, Function.comp_def, Equiv.apply_symm_apply] using hq)
  have hag' (d) : min ((q ∘ b) (GrowthOrderedBase.oldAt I X (by omega) (incl d))) γ =
      min (p d) γ := by
    simpa only [b, Function.comp_apply, hid] using hag d
  obtain ⟨r, hr, hread, hcap⟩ : ∃ r,
      RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) r ∧
      (∀ d, r (GrowthOrderedBase.oldAt I X (by omega) (incl d)) = p d) ∧
      ∀ d, min (r d) γ = min ((q ∘ b) d) γ := by
    by_cases hz : γ = ⊥
    · obtain ⟨w, hw, hr⟩ := hbot hp
      exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
    exact ReceivingRankLift.face_positive_lift I.boundary I.rows (by omega) (field I)
      (GrowthOrderedBase.fields I X) (GrowthOrderedBase.proper I hB hC)
      (anchor_lawful I X T) (fun a => a.property.1) (anchor_visible_one X)
      ⟨((zero : State I.right.scheme I.left.scheme).normalize 1).profile,
        normalize_inventory 1 (fun d => by cases d <;> exact bot_ne_top),
        _, normalize_admitted X (by decide : 1 ≤ 1) (zero_admitted X 1), rfl⟩
      (fun d => d.2.2) incl pick
      (fun a d => by
        obtain ⟨S, hs, he⟩ := a.property.2
        rw [GrowthOrderedBase.fields, ← he]; exact hfld S hs d)
      (fun a => by
        obtain ⟨S, hS, heS⟩ := a.property.2
        have he : (fun d : O.scheme.below (Finset.univ, 1) => a.val (pick d.1)) =
            fun d => sVal S d.1 :=
          funext fun d => (congrFun heS (pick d.1)).symm.trans (hseq S d.1).symm
        exact he ▸ hslaw S hS)
      (fun a {p' B'} hp' hcap' => by
        obtain ⟨S, hS, heS⟩ := a.property.2
        have hp'cap (d) : min (p' d) (grid 1 B') = min (sVal S d.1) (grid 1 B') := by
          rw [hseq, show S.profile (pick d.1) = a.val (pick d.1) from congrFun heS (pick d.1)]
          exact hcap' d
        obtain ⟨U, hU, ⟨r⟩⟩ := hprot hS (heS.symm ▸ a.property.1) hp' hp'cap
        exact ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩,
          r.decoder, r.witness,
          fun d => (r.readback (pick d.1)).trans ((hseq U d.1).symm.trans (hU d)),
          fun x => (congrArg (fun z => min (z x) _) heS).symm.trans (r.prefix_eq x).symm⟩)
      hp hq' hγ (bot_lt_iff_ne_bot.mpr hz) hag'
  refine ⟨r ∘ b.symm, (GrowthPaddedCutTransport.base_respects_iff P r).mp hr, fun x => ?_,
    fun d => by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (b.symm d)⟩
  rw [Function.comp_apply, hid x, Equiv.symm_apply_apply]; exact hread x

private theorem private_one :
    CappedLift P.rows (show GradedLe (C, 1) (A, 1) from ⟨hC.subset, le_rfl⟩) :=
  one_side P I.right I.placeRight I.imageRight hC.subset (privateFace P)
    (privateIncl I) Sum.inl State.privateValues (fun _ => rfl)
    (fun hp => private_bottom_supply I X T (by omega) hB hC hp)
    (fun _ hS d => field_private I X T hS d.1) (fun _ hS => hS.private_lawful) (fun _ _ => rfl)
    (fun {_} hS hc {_ _} hp' hcap => by
      obtain ⟨U, _, hU, _, _, _, hr⟩ := T.private_protected_all (by decide) hS hc hp' hcap
      exact ⟨U, hU, hr⟩)

private theorem donor_one (hsmall : n + 1 < X.req.N) :
    CappedLift P.rows (show GradedLe (B, 1) (A, 1) from ⟨hB.subset, le_rfl⟩) :=
  one_side P I.left I.placeLeft I.imageLeft hB.subset (donorFace P)
    (donorIncl I) Sum.inr State.donorValues (fun _ => rfl)
    (fun hp => donor_bottom_supply I X T (by omega) hB hC
      ((Nat.succ_le_succ (Nat.zero_le n)).trans_lt hsmall) hp)
    (fun S _ d => field_donor I S d.1) (fun _ hS => hS.donor_lawful) (fun _ _ => rfl)
    (fun {_} hS hc {_ _} hp' hcap => by
      obtain ⟨U, _, hU, _, _, _, hr⟩ := T.donor_protected_before (by decide)
        ((Nat.succ_le_succ (Nat.zero_le n)).trans_lt hsmall) hS hc hp' hcap
      exact ⟨U, hU, hr⟩)
end LayerFaces

section Native
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {t : ℕ} (ht : t + 2 ≤ A.card)

private theorem exists_section {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X (t + 2) S) :
    ∃ w, RespectsSemanticsBelow (build I X T hA hB hC t ht).rows (A, t + 2) w ∧
      ∀ d : I.boundary.below (A, t + 2),
        w ⟨(build I X T hA hB hC t ht).baseMap (RelativeLadderLayer.old I.boundary (by omega) d.1), by
          rw [(build I X T hA hB hC t ht).base_index, RelativeLadderLayer.old_index]; exact d.2⟩ =
          S.profile (field I d.1) := by
  let P := build I X T hA hB hC t ht
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (by omega : 1 ≤ t + 2) hS
  let a : Catalogue X (t + 2) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have hl0 : RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, t + 2)
      (fun d => δ (RelativeLadderLayer.renderWith I.boundary (by omega) (field I) (GrowthHigherSources.fields X 1)
        (GrowthPaddedNativeRows.anchor I X T hA hB hC t ht a) (GrowthHigherSources.fields X (t + 2) a)
        (GrowthPaddedNativeRows.ceiling I t) d.1)) :=
    decoded_renderWith_respects (B := I.boundary) (semB := I.rows) (by omega)
      (field I) (GrowthHigherSources.fields X 1) (GrowthOrderedBase.proper I hB hC)
      (GrowthPaddedNativeRows.anchor I X T hA hB hC t ht a) (GrowthHigherSources.fields X (t + 2) a)
      (GrowthPaddedNativeRows.ceiling I t) (anchor_bound X a) (anchor_visible_one X a)
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (by omega : 1 ≤ t + 2))
      (GrowthPaddedNativeRows.anchor_ranks I X T hA hB hC t ht a) (by omega : 1 ≤ t + 2) hδ hreflect
      (by simpa only [a, hread] using boundary_lawful_at I X T hS)
  have hl : RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, t + 2)
      (fun d => δ (GrowthPaddedNativeRows.source I X T hA hB hC t ht a (P.baseMap d.1))) := by
    dsimp only [P]; simpa only [GrowthPaddedNativeRows.source_base] using hl0
  refine ⟨_, decoded_layer_lawful (GrowthPaddedNativeRows.source_lawful I X T hA hB hC t ht a) hδ
    P.baseMap P.base_index P.base_respects hl (fun c _ => by
      rcases P.cases c with ⟨b, hb⟩ | ⟨hsc, hgr, _⟩
      · exact Or.inl ⟨b, hb⟩
      · exact Or.inr (P.higher_short c hsc hgr)), fun d => ?_⟩
  exact (congrArg δ (GrowthPaddedNativeRows.source_original I X T hA hB hC t ht a d.1)).trans
    (hread _)

private theorem native_side {V : Finset ι} {a : ℕ} (O : SemScheme a)
    (e₀ : Fin a ↪ ι) (he₀ : Finset.univ.image e₀ = V) (hV : V ⊆ A)
    (G : ExactSemanticFace (PointImageSemantics.rows O.scheme e₀ he₀ O.rows) I.rows)
    (hT : ¬ A ⊆ V)
    (pick : Cell O.scheme → Field I.right.scheme I.left.scheme)
    (sVal : State I.right.scheme I.left.scheme → O.scheme.below (Finset.univ, t + 2) → ExtOrd)
    (hs_law : ∀ S, Admitted X (t + 2) S → RespectsSemanticsBelow O.rows (Finset.univ, t + 2) (sVal S))
    (hs_eq : ∀ S, Admitted X (t + 2) S → ∀ d, S.profile (pick d.1) = sVal S d)
    (hfld : ∀ S, Admitted X (t + 2) S → ∀ c, S.profile (field I (G.map c)) = S.profile (pick c))
    (hbot : (∃ d : O.scheme.below (Finset.univ, t + 2), O.scheme.grade d.1 = t + 2) →
      ∀ {p : O.scheme.below (Finset.univ, t + 2) → ExtOrd},
        RespectsSemanticsBelow O.rows (Finset.univ, t + 2) p →
        ∃ S, Admitted X (t + 2) S ∧ ∀ d, sVal S d = p d)
    (hprot : (∃ d : O.scheme.below (Finset.univ, t + 2), O.scheme.grade d.1 = t + 2) →
      ∀ {S}, Admitted X (t + 2) S →
      S.profile ∈ CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) (t + 2) →
      ∀ {b : ℕ} {v : O.scheme.below (Finset.univ, t + 2) → ExtOrd},
      RespectsSemanticsBelow O.rows (Finset.univ, t + 2) v →
      (∀ d, min (v d) (grid (t + 2) b) = min (sVal S d) (grid (t + 2) b)) →
      ∃ S', Admitted X (t + 2) S' ∧ (∀ d, sVal S' d = v d) ∧
        Nonempty (ProtectedRepair X S.profile S' (t + 2) b))
    (hprev : CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (V, t + 1) (A, t + 1) from ⟨hV, le_rfl⟩)) :
    CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (V, t + 2) (A, t + 2) from ⟨hV, le_rfl⟩) := by
  let P := build I X T hA hB hC t ht
  let GP := layerFace P G hT
  let fLow := fun d => CellScheme.below.mono (show GradedLe (V, t + 1) (A, t + 1) from ⟨hV, le_rfl⟩)
    (fullEquiv P O e₀ he₀ GP (t + 1) d)
  let fAt := fun d => CellScheme.below.mono (show GradedLe (V, t + 2) (A, t + 2) from ⟨hV, le_rfl⟩)
    (fullEquiv P O e₀ he₀ GP (t + 2) d)
  have hgr (d : O.scheme.below (Finset.univ, t + 2)) : P.carrier.grade (fAt d).1 = O.scheme.grade d.1 :=
    congrArg Prod.snd (GP.index d.1)
  have hrest := fun {p u M} => restore_face (O := O) (effLow := (Finset.univ, t + 1)) (eff := (Finset.univ, t + 2))
    ⟨Finset.Subset.refl _, Nat.le_succ _⟩ (fun d => d.2.2) (fun c hc => ⟨Finset.subset_univ _, hc⟩)
    fLow fAt hgr (Equiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl)
    (fun p₀ q₀ M hp₀ hq₀ hM hag₀ => by
      let e := fullEquiv P O e₀ he₀ GP (t + 1)
      obtain ⟨r₀, hr₀, hcap₀, hrd₀⟩ := hprev (p₀ ∘ e.symm) q₀ M
        ((full_respects_iff P O e₀ he₀ GP (t + 1) _).mpr
          (by simpa only [e, Function.comp_def, Equiv.symm_apply_apply] using hp₀))
        hq₀ hM (fun d => by
          obtain ⟨x, rfl⟩ := e.surjective d
          simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hag₀ x)
      exact ⟨r₀, hr₀, fun x => by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hrd₀ (e x), hcap₀⟩)
    (p := p) (u := u) (M := M)
  apply lift_of_face P O e₀ he₀ hV GP (t + 2)
  intro p q γ hp hq hγ hag
  exact full_face_lift (by omega) (fun _ => rfl) fAt hgr hrest
    State.profile (Admitted X (t + 2)) Subtype.val Subtype.property
    (fun S hS hc => ⟨_, hc, S, hS, rfl⟩) (fun _ _ _ => rfl)
    (GrowthPaddedNativeRows.source I X T hA hB hC t ht)
    (GrowthPaddedNativeRows.source_lawful I X T hA hB hC t ht)
    (GrowthPaddedNativeRows.source_supported I X T hA hB hC t ht)
    (fun b a {h} hh hba => GrowthPaddedNativeRows.source_prefix I X T hA hB hC t ht b a hh hba)
    hp hq
    (fun hq' => exists_installed_chart (Growth.zeroMember X (t + 2) (by omega))
      (GrowthPaddedNativeRows.owner I X T hA hB hC t ht)
      (GrowthPaddedNativeRows.source I X T hA hB hC t ht)
      (GrowthPaddedNativeRows.owner_index I X T hA hB hC t ht)
      (GrowthPaddedNativeRows.owner_row I X T hA hB hC t ht)
      (GrowthPaddedNativeRows.owner_exhaustive I X T hA hB hC t ht) hq')
    pick sVal hs_law hs_eq
    (fun a d => by
      obtain ⟨S, hS, he⟩ := a.property.2
      exact (GrowthPaddedNativeRows.source_original I X T hA hB hC t ht a (G.map d.1)).trans
        (by change a.val _ = _; rw [← he]; exact hfld S hS d.1))
    (fun hex {p} hp => by
      obtain ⟨S, hS, hr⟩ := hbot hex hp
      obtain ⟨w, hw, hread⟩ := exists_section ht hS
      refine ⟨w, hw, fun d => ?_⟩
      have hd : GradedLe (I.boundary.cell (G.map d.1)) (A, t + 2) :=
        ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
          (congrArg Prod.snd (G.index d.1)).le.trans d.2.2⟩
      exact (hread ⟨_, hd⟩).trans ((hfld S hS d.1).trans ((hs_eq S hS d).trans (hr d))))
    (fun hex {S} hS hc {b v} hv hagv => by
      obtain ⟨S', hS', he', ⟨r⟩⟩ := hprot hex hS hc hv hagv
      exact ⟨r.encoded, r.decoder, r.admitted, r.canonical, r.prefix_eq, r.witness,
        fun d => (r.readback (pick d.1)).trans ((hs_eq S' hS' d).trans (he' d)),
        r.grid_fixed, r.reaches, r.boundary_fixed⟩)
    hγ hag

private theorem native_private
    (hprev : CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (C, t + 1) (A, t + 1) from ⟨hC.subset, le_rfl⟩)) :
    CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (C, t + 2) (A, t + 2) from ⟨hC.subset, le_rfl⟩) :=
  native_side ht I.right I.placeRight I.imageRight hC.subset I.rightFace hC.not_ge
    Sum.inl (fun S d => S.privateValues d.1) (fun _ hS => hS.private_lawful) (fun _ _ _ => rfl)
    (fun _ hS c => GrowthOrderedBase.field_private I X T hS c)
    (fun _ {_} hp => T.private_bottom_state hp)
    (fun _ {_} hS hc {_ _} hv hagv => by
      obtain ⟨S', hS', he', _, _, _, hr⟩ := T.private_protected_all (by omega) hS hc hv hagv
      exact ⟨S', hS', he', hr⟩)
    hprev

private theorem native_donor (hsmall : n + 1 < X.req.N)
    (hprev : CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (B, t + 1) (A, t + 1) from ⟨hB.subset, le_rfl⟩)) :
    CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (B, t + 2) (A, t + 2) from ⟨hB.subset, le_rfl⟩) :=
  native_side ht I.left I.placeLeft I.imageLeft hB.subset I.leftFace hB.not_ge
    Sum.inr (fun S d => S.donorValues d.1) (fun _ hS => hS.donor_lawful) (fun _ _ _ => rfl)
    (fun S _ c => GrowthOrderedBase.field_donor I S c)
    (fun ⟨d, hd⟩ {_} hp => T.donor_bottom_state (hd ▸ Growth.donor_grade_lt I.left hsmall d.1) hp)
    (fun ⟨d, hd⟩ {_} hS hc {_ _} hv hagv => by
      obtain ⟨S', hS', he', _, _, _, hr⟩ :=
        T.donor_protected_before (by omega) (hd ▸ Growth.donor_grade_lt I.left hsmall d.1) hS hc hv hagv
      exact ⟨S', hS', he', hr⟩)
    hprev
end Native

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

private theorem clause_side {V : Finset ι} (hV : V ⊆ A)
    (hone : ∀ {k} (P : Layer I X T hA hB hC k),
      CappedLift P.rows (show GradedLe (V, 1) (A, 1) from ⟨hV, le_rfl⟩))
    (hstep : ∀ {t} (ht : t + 2 ≤ A.card),
      CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (V, t + 1) (A, t + 1) from ⟨hV, le_rfl⟩) →
      CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (V, t + 2) (A, t + 2) from ⟨hV, le_rfl⟩))
    (t : ℕ) (ht : t + 2 ≤ A.card) (j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows (show GradedLe (V, j) (A, j) from ⟨hV, le_rfl⟩) := by
  induction t generalizing j with
  | zero =>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · exact hone _
    · exact hstep ht (hone _)
  | succ t ih =>
    have hlow (l : ℕ) (hl1 : 1 ≤ l) (hlt : l ≤ t + 2) :
        CappedLift (build I X T hA hB hC (t + 1) ht).rows (show GradedLe (V, l) (A, l) from ⟨hV, le_rfl⟩) :=
      GrowthPaddedCutTransport.step_lift (build I X T hA hB hC t (by omega))
        (by omega) (by omega) (show GradedLe (V, l) (A, l) from ⟨hV, le_rfl⟩) hlt
        (ih (by omega) l hl1 hlt)
    by_cases he : j = t + 1 + 2
    · exact he ▸ hstep ht (hlow (t + 2) (by omega) le_rfl)
    · exact hlow j hj (by omega)

theorem private_subface (t : ℕ) (ht : t + 2 ≤ A.card)
    {S : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hSC : S ⊆ C) (hij : i ≤ j) (hj : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows
      (show GradedLe (S, i) (A, j) from ⟨hSC.trans hC.subset, hij⟩) := by
  have hCi : (C, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, (Plan.mem_gradedPlan.mp hS).2.1,
      (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hSC)⟩
  exact ((inherited_lift (build I X T hA hB hC t ht) hS hCi ⟨hSC, le_rfl⟩
    (Or.inr (Finset.Subset.refl _))).comp
      (clause_side I X T hA hB hC hC.subset private_one (fun ht => native_private ht)
        t ht i (Plan.mem_gradedPlan.mp hS).2.1 (hij.trans hj))).raise_target
        (h := hSC.trans hC.subset) hij

theorem donor_subface (hsmall : n + 1 < X.req.N) (t : ℕ) (ht : t + 2 ≤ A.card)
    {S : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hSB : S ⊆ B) (hij : i ≤ j) (hj : j ≤ t + 2) :
    CappedLift (build I X T hA hB hC t ht).rows
      (show GradedLe (S, i) (A, j) from ⟨hSB.trans hB.subset, hij⟩) := by
  have hBi : (B, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, (Plan.mem_gradedPlan.mp hS).2.1,
      (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hSB)⟩
  exact ((inherited_lift (build I X T hA hB hC t ht) hS hBi ⟨hSB, le_rfl⟩
    (Or.inl (Finset.Subset.refl _))).comp
      (clause_side I X T hA hB hC hB.subset (fun P => donor_one P hsmall)
        (fun ht => native_donor ht hsmall) t ht i
        (Plan.mem_gradedPlan.mp hS).2.1 (hij.trans hj))).raise_target
        (h := hSB.trans hB.subset) hij

end
end VaughtConjecture.Knight.GrowthPaddedAllCutoff

namespace VaughtConjecture.Knight.GrowthCarrierEvaluation
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open Transform Growth CoatomBoundaryExtension GrowthHigherMixed CellScheme.restrictFace
noncomputable section
universe w

private theorem correct_of_cap_agreement {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
    {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
    (r : Requests DA DQ) {s s' : DA.below (DA.cell r.C) → ExtOrd} {v v' : Cell DQ → ExtOrd}
    (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) (hvis : SelfVis r.N (s' r.capCell))
    (hc : s r.capCell = s' r.capCell)
    (hs : ∀ d, min (s d) (s' r.capCell) = min (s' d) (s' r.capCell))
    (hv : ∀ d, min (v d) (s' r.capCell) = min (v' d) (s' r.capCell))
    (h : r.Correct s v) : r.Correct s' v' := by
  have href (f) (hf : f ∈ r.F) : r.tOf s f = r.tOf s' f := by
    unfold Requests.tOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl (hoff f hf), hs,
      evr_min_of_selfVis hvis le_rfl (hoff f hf)]
  have hmark : r.dOf s = r.dOf s' := by
    unfold Requests.dOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl r.R_lt_N.le, hs,
      evr_min_of_selfVis hvis le_rfl r.R_lt_N.le]
  exact ⟨fun d hd => by rw [← hv d, ← hc]; exact h.1 d hd,
    fun d hd => by rw [← hv d, ← hc, ← href d hd]; exact h.2.1 d hd,
    fun d hd => by rw [← hv d, ← hc, ← hmark]; exact h.2.2 d hd⟩

section Replicated
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

private theorem bountiful (hsmall : n + 1 < X.req.N) :
    (rows I X T hA hB hC (A.card - 2) (by omega)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_same_grade
  intro S V j hS hV hSV
  let t := A.card - 2
  have ht : t + 2 ≤ A.card := by omega
  have hp : (carrier I X T hA hB hC t ht).plan = R :=
    GrowthPaddedIteration.build_plan I X T hA hB hC t ht
  have hS' : (S, j) ∈ Plan.gradedPlan R := hp ▸ hS
  have hV' : (V, j) ∈ Plan.gradedPlan R := hp ▸ hV
  have hjt : j ≤ t + 2 := by
    have hj := (Plan.mem_gradedPlan.mp hV').2.2
    have hc := Finset.card_le_card (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1)
    omega
  by_cases htarget : V ⊆ B ∨ V ⊆ C
  · exact GrowthReplicatedRows.inherited_lift t ht hS' hV' _ htarget
  have hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V :=
    Or.inr ⟨fun hb => htarget (Or.inl hb), fun hc => htarget (Or.inr hc)⟩
  by_cases hs : S ⊆ B ∨ S ⊆ C
  · have hVA : V ⊆ A := I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1
    have hj0 : 1 ≤ j := (Plan.mem_gradedPlan.mp hS').2.1
    have hfull : CappedLift (rows I X T hA hB hC t ht)
        (show GradedLe (S, j) (A, j) from ⟨hSV.trans hVA, le_rfl⟩) := by
      rcases hs with hb | hc
      · exact GrowthReplicatedRows.lift_to_full
          (GrowthPaddedIteration.build I X T hA hB hC t ht) _ (Or.inl hb)
          (GrowthPaddedAllCutoff.donor_subface I X T hA hB hC hsmall t ht hS' hb le_rfl hjt)
      · exact GrowthReplicatedRows.lift_to_full
          (GrowthPaddedIteration.build I X T hA hB hC t ht) _ (Or.inr hc)
          (GrowthPaddedAllCutoff.private_subface I X T hA hB hC t ht hS' hc le_rfl hjt)
    intro p q γ hp' hq' hγ hag
    let hvA : GradedLe (V, j) (A, j) := ⟨hVA, le_rfl⟩
    obtain ⟨q', hq'L, hqeq⟩ := lawfulExtension I X T hA hB hC t ht
      V (Plan.mem_gradedPlan.mp hV').1 hmV j (Plan.mem_gradedPlan.mp hV').2.2 hj0 hjt A hVA q hq'
    obtain ⟨r, hr, hcap, hread⟩ := hfull p q' γ hp' hq'L hγ fun d =>
      (congrArg (fun z => min z γ)
        (hqeq (CellScheme.below.mono (show GradedLe (S, j) (V, j) from ⟨hSV, le_rfl⟩) d))).trans
        (hag d)
    exact ⟨fun d => r (CellScheme.below.mono hvA d), hr.mono hvA,
      fun d => (hcap (CellScheme.below.mono hvA d)).trans (congrArg (fun z => min z γ) (hqeq d)),
      fun d => hread d⟩
  · exact cappedLift I X T hA hB hC t ht S (Plan.mem_gradedPlan.mp hS').1
      (Or.inr ⟨fun hb => hs (Or.inl hb), fun hc => hs (Or.inr hc)⟩)
      j (Plan.mem_gradedPlan.mp hS').2.2 (Plan.mem_gradedPlan.mp hS').2.1 hjt
      V (Plan.mem_gradedPlan.mp hV').1 hmV (Plan.mem_gradedPlan.mp hV').2.2 hSV

private theorem full_correct (t : ℕ) (ht : t + 2 ≤ A.card) (hfull : A.card ≤ t + 2)
    (hsmall : n + 1 < X.req.N) {v : Cell (carrier I X T hA hB hC t ht) → ExtOrd}
    (hv : RespectsSemantics (rows I X T hA hB hC t ht) v)
    (lab : Cell I.right.scheme → ExtOrd) (hclass : InClass X.ZA lab) (hcap : lab X.req.C ≠ ⊥)
    (hpriv : ∀ d, v ((GrowthReplicatedRows.privateFace I X T hA hB hC t ht).map d) = lab d) :
    X.req.Correct (X.req.sec lab)
      (fun d => v ((GrowthReplicatedRows.donorFace I X T hA hB hC t ht).map d)) := by
  let P := tower I X T hA hB hC t ht
  have hAmem : A ∈ R := by
    have h := GrowthMixedGradeOne.A_mem_plan I X T hA hB hC P
    rwa [GrowthPaddedIteration.build_plan] at h
  have hcardC : (Finset.univ : Finset (Fin J)).card = C.card := by
    rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]
  have hpriv_gr (d : Cell I.right.scheme) : I.right.scheme.grade d ≤ A.card := by
    have hg := I.right.scheme.grade_le_card_scope d
    have h1 := Finset.card_le_card (Finset.subset_univ (I.right.scheme.scope d))
    have h3 := Finset.card_le_card hC.subset; omega
  have hN : X.req.N ≤ A.card := X.grade_C ▸ hpriv_gr X.req.C
  have hdon_gr (d : Cell I.left.scheme) : I.left.scheme.grade d ≤ A.card :=
    ((X.below_top d).2.trans X.top_le_N).trans hN
  let origAt (d : Cell I.boundary) (hd : GradedLe (I.boundary.cell d) (A, A.card)) :
      CellScheme.below (carrier I X T hA hB hC t ht) (A, A.card) :=
    ScopeReplicationCarrier.oldBelow P.carrier B C (A, A.card)
      ⟨original I X T hA hB hC t ht d, by rw [original_index]; exact hd⟩
  let privAt (d : Cell I.right.scheme) :
      CellScheme.below (carrier I X T hA hB hC t ht) (A, A.card) :=
    origAt (I.rightFace.map d)
      ((I.rightFace.index d : I.boundary.cell (I.rightFace.map d) =
        ((I.right.scheme.scope d).image I.placeRight, I.right.scheme.grade d)).symm ▸
        ⟨((Finset.image_subset_image (Finset.subset_univ _)).trans I.imageRight.subset).trans
          hC.subset, hpriv_gr d⟩)
  let donAt (d : Cell I.left.scheme) :
      CellScheme.below (carrier I X T hA hB hC t ht) (A, A.card) :=
    origAt (I.leftFace.map d)
      ((I.leftFace.index d : I.boundary.cell (I.leftFace.map d) =
        ((I.left.scheme.scope d).image I.placeLeft, I.left.scheme.grade d)).symm ▸
        ⟨((Finset.image_subset_image (Finset.subset_univ _)).trans I.imageLeft.subset).trans
          hB.subset, hdon_gr d⟩)
  have hpriv_eq (d : Cell I.right.scheme) : v (privAt d).1 = lab d := by
    rw [← show (GrowthReplicatedRows.privateFace I X T hA hB hC t ht).map d = (privAt d).1 from
      congrArg (ScopeReplicationCarrier.old P.carrier B C)
        (GrowthPaddedInstallation.face_map I X T hA hB hC I.rightFace hC.not_ge t ht d)]
    exact hpriv d
  have hdon_eq (d : Cell I.left.scheme) :
      v (donAt d).1 = v ((GrowthReplicatedRows.donorFace I X T hA hB hC t ht).map d) :=
    congrArg v (congrArg (ScopeReplicationCarrier.old P.carrier B C)
      (GrowthPaddedInstallation.face_map I X T hA hB hC I.leftFace hB.not_ge t ht d)).symm
  let p := hv.toBelow (A, A.card)
  let p_fn : CellScheme.below (carrier I X T hA hB hC t ht) (A, A.card) → ExtOrd :=
    fun z => v z.1
  change RespectsSemanticsBelow _ _ p_fn at p
  have hmA : A = A ∨ ScopeReplicationCarrier.Mixed B C A := Or.inl rfl
  have hj0 : 1 ≤ A.card := by omega
  obtain ⟨S, hS, he⟩ := exists_admitted_at I X T hA hB hC t ht A hAmem hmA A.card le_rfl hj0 p
    X.req.N (by omega) hN (hN.trans hfull)
  let H := gradeMax I X T hA hB hC t ht A A.card p_fn X.req.N
  have hmax_le (k : ℕ) (hk : k ≤ X.req.N) :
      H ≤ height I X T hA hB hC t ht A A.card p_fn k := by
    have he' : height I X T hA hB hC t ht A A.card p_fn X.req.N = H := by
      simp only [height, ite_eq_right (by omega : ¬ X.req.N ≤ 1), ite_eq_left hN]; rfl
    rw [← he']
    exact height_antitone I X T hA hB hC t ht A hAmem hmA A.card le_rfl p hfull hk
  have hpriv_read (d : Cell I.right.scheme) :
      p_fn (privAt d) = min (shadowSup I X T hA hB hC t ht A hAmem hmA A.card le_rfl hj0 p_fn
        (GrowthOrderedBase.field I (I.rightFace.map d)))
        (height I X T hA hB hC t ht A A.card p_fn (I.right.scheme.grade d)) := by
    have hr := projection_readback I X T hA hB hC t ht A hAmem hmA A.card le_rfl hj0 p hfull
      (privAt d) (I.rightFace.map d) (ScopeReplicationCarrier.erase_old P.carrier B C _)
    rwa [show I.boundary.grade (I.rightFace.map d) = I.right.scheme.grade d from
      congrArg Prod.snd (I.rightFace.index d)] at hr
  have hdon_read (d : Cell I.left.scheme) :
      p_fn (donAt d) = min (shadowSup I X T hA hB hC t ht A hAmem hmA A.card le_rfl hj0 p_fn
        (GrowthOrderedBase.field I (I.leftFace.map d)))
        (height I X T hA hB hC t ht A A.card p_fn (I.left.scheme.grade d)) := by
    have hr := projection_readback I X T hA hB hC t ht A hAmem hmA A.card le_rfl hj0 p hfull
      (donAt d) (I.leftFace.map d) (ScopeReplicationCarrier.erase_old P.carrier B C _)
    rwa [show I.boundary.grade (I.leftFace.map d) = I.left.scheme.grade d from
      congrArg Prod.snd (I.leftFace.index d)] at hr
  have hbound : lab X.req.C ≤ H := by
    rw [← hpriv_eq X.req.C]
    change p_fn (privAt X.req.C) ≤ H
    rw [hpriv_read, X.grade_C, height, ite_eq_right (by omega : ¬ X.req.N ≤ 1), ite_eq_left hN]
    exact min_le_right _ _
  have hpos : H ≠ ⊥ := fun hz => hcap (le_bot_iff.mp (hbound.trans_eq hz))
  have hpriv_cap (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ X.req.N) :
      S.privateValues d = min (lab d) H := by
    rw [← hpriv_eq d]
    change S.privateValues d = min (p_fn (privAt d)) H
    rw [hpriv_read, min_assoc, min_eq_right (hmax_le _ hd)]
    exact (GrowthOrderedBase.field_private I X T hS d).symm.trans (he _)
  have hdon_cap (d : Cell I.left.scheme) :
      S.donorValues d = min (v ((GrowthReplicatedRows.donorFace I X T hA hB hC t ht).map d)) H := by
    have hdg : I.left.scheme.grade d ≤ X.req.N := (X.below_top d).2.trans X.top_le_N
    rw [← hdon_eq d]
    change S.donorValues d = min (p_fn (donAt d)) H
    rw [hdon_read, min_assoc, min_eq_right (hmax_le _ hdg)]
    exact (GrowthOrderedBase.field_donor I S d).symm.trans (he _)
  have hc : S.privateValues X.req.C = lab X.req.C := by
    rw [hpriv_cap _ X.grade_C.le, min_eq_left hbound]
  have hin : InClass X.ZA S.privateValues := fun d => by
    rw [hpriv_cap d.1 (d.2.2.trans_eq X.grade_C)]
    exact ⟨fun h => (hclass d).mp (eq_of_min_eq_of_lt' h (bot_lt_iff_ne_bot.mpr hpos)),
      fun h => by rw [(hclass d).mpr h, min_eq_left bot_le]⟩
  have hvis : SelfVis X.req.N (lab X.req.C) := by
    rw [← hc]
    have ho := (hS.private_lawful.orderly (Growth.capAt X le_rfl X.req.capCell)).symm
    change SelfVis (I.right.scheme.grade X.req.C) (S.privateValues X.req.C) at ho
    rwa [X.grade_C] at ho
  exact correct_of_cap_agreement X.req X.off_lt hvis hc
    (fun d => by
      change min (S.privateValues d.1) (lab X.req.C) = _
      rw [hpriv_cap d.1 (d.2.2.trans_eq X.grade_C), min_assoc, min_eq_right hbound]; rfl)
    (fun d => by
      change min (S.donorValues d) (lab X.req.C) = _
      rw [hdon_cap d, min_assoc, min_eq_right hbound]; rfl)
    (hS.correct le_rfl hin)
end Replicated

theorem exists_correct_donor {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    {n J : ℕ} (C : S α.1 J) (P : SemScheme (n + 1)) (Q : SemScheme n) (e : Fin n ↪ Fin J)
    (hvC : Finset.univ.image e ∈ C.scheme.scheme.plan)
    (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
    (hC : C.scheme.restrictFace e hvC = Q)
    (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
    (X : RelativeData C.scheme.scheme C.scheme.rows P.scheme P.rows)
    (T : RootAttachment Q Fin.castSuccEmb hvP hP e hvC hC X)
    (hsmall : n + 1 < X.req.N)
    (L : W.ActualLabelling) {u : Fin J ↪ M} (hM : W.IsModel) (hu : W.eval u = some C)
    (hclass : InClass X.ZA (L.label u C)) :
    ∃ (y : M) (_hy : y ∉ Set.range u) (hyRoot : y ∉ Set.range (e.trans u))
      (s : S α.1 (n + 1)), W.eval (snoc (e.trans u) y hyRoot) = some s ∧
      ∃ hs : s.scheme = P,
        X.req.Correct (X.req.sec (L.label u C))
          (fun d => L.label (snoc (e.trans u) y hyRoot) s (SemScheme.castCell hs.symm d)) := by
  let pspec := WholeDonorAttachment.plan_spec e C.scheme P Q hvC hvP hC hP
  let I : WholeDonorBoundary.Input Finset.univ (WholeDonorAttachment.donorScope e)
      WholeDonorAttachment.privateScope (WholeDonorAttachment.plan e C.scheme P Q hvC hvP hC hP)
      n (n + 1) J :=
    { isPlan := pspec.1, left := P, right := C.scheme, common := Q,
      placeLeft := onePointProj e, placeRight := Fin.castSuccEmb,
      imageLeft := rfl, imageRight := rfl, commonLeft := Fin.castSuccEmb, commonRight := e,
      visibleLeft := hvP, visibleRight := hvC, faceLeft := hP, faceRight := hC,
      commute := (WholeDonorAttachment.commute e).symm,
      intersection := (WholeDonorAttachment.root_right_image e).trans
        ((WholeDonorAttachment.intersection e).symm.trans (Finset.inter_comm _ _)),
      planLeft := pspec.2.2.2.2, planRight := pspec.2.2.1 }
  have hNJ : X.req.N ≤ J := by
    have hg := C.scheme.scheme.grade_le_card_scope X.req.C
    have hc := Finset.card_le_card (Finset.subset_univ (C.scheme.scheme.scope X.req.C))
    rw [X.grade_C] at hg; simpa only [Finset.card_univ, Fintype.card_fin] using hg.trans hc
  have hnJ : n + 1 < J := hsmall.trans_le hNJ
  have hA : 2 ≤ (Finset.univ : Finset (Fin (J + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]; omega
  have hB : WholeDonorAttachment.donorScope e ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, WholeDonorAttachment.donor_proper e hnJ⟩
  have hD : WholeDonorAttachment.privateScope (N := J) ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, WholeDonorAttachment.private_proper⟩
  let t := (Finset.univ : Finset (Fin (J + 1))).card - 2
  have ht : t + 2 ≤ (Finset.univ : Finset (Fin (J + 1))).card := by omega
  let E : SemScheme (J + 1) :=
    { scheme := carrier I X T hA hB hD t ht
      rows := rows I X T hA hB hD t ht
      rows_coded := GrowthReplicatedRows.build_coded I X T hA hB hD t ht
      consistent := GrowthReplicatedRows.build_consistent I X T hA hB hD t ht
      bountiful := bountiful I X T hA hB hD hsmall
      complete := GrowthReplicatedRows.complete }
  have hplan : E.scheme.plan = WholeDonorAttachment.plan e C.scheme P Q hvC hvP hC hP :=
    GrowthPaddedIteration.build_plan I X T hA hB hD t ht
  let F := GrowthReplicatedRows.privateFace I X T hA hB hD t ht
  let G := GrowthReplicatedRows.donorFace I X T hA hB hD t ht
  have hdplan : Plan.restrictPlan E.scheme.plan (WholeDonorAttachment.donorScope e) =
      P.scheme.plan.image (Finset.image (onePointProj e)) := by rw [hplan]; exact I.planLeft
  have hpplan : Plan.restrictPlan E.scheme.plan WholeDonorAttachment.privateScope =
      C.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb) := by rw [hplan]; exact I.planRight
  have hvD := OrderedFaceRestriction.visible P E.scheme (onePointProj e) rfl hdplan
  have hvPriv := OrderedFaceRestriction.visible C.scheme E.scheme Fin.castSuccEmb rfl hpplan
  have hsD : E.restrictFace (onePointProj e) hvD = P :=
    LowOnlyPaddedLegal.restrict_eq_of_face P E (onePointProj e) rfl G
      (GrowthReplicatedRows.donor_order I X T hA hB hD t ht) hdplan
  have hsPriv : E.restrictFace Fin.castSuccEmb hvPriv = C.scheme :=
    LowOnlyPaddedLegal.restrict_eq_of_face C.scheme E Fin.castSuccEmb rfl F
      (GrowthReplicatedRows.private_order I X T hA hB hD t ht) hpplan
  have hoccD (d : Cell P.scheme) :
      toCell E.scheme (onePointProj e) hvD (SemScheme.castCell hsD.symm d) = G.map d :=
    OrderedFaceRestriction.toCell_eq P E.scheme E.rows (onePointProj e) rfl G
      (GrowthReplicatedRows.donor_order I X T hA hB hD t ht) hdplan d
  have hoccP (d : Cell C.scheme.scheme) :
      toCell E.scheme Fin.castSuccEmb hvPriv (SemScheme.castCell hsPriv.symm d) = F.map d :=
    OrderedFaceRestriction.toCell_eq C.scheme E.scheme E.rows Fin.castSuccEmb rfl F
      (GrowthReplicatedRows.private_order I X T hA hB hD t ht) hpplan d
  obtain ⟨y, hy, r, hr, hco, hev⟩ := hM.genSat u C hu E ⟨hvPriv, hsPriv⟩
  have hplab (d : Cell C.scheme.scheme) :
      L.label (snoc u y hy) r (SemScheme.castCell hr.symm (F.map d)) = L.label u C d := by
    obtain ⟨Er, _, _, _⟩ := r; change Er = E at hr; subst Er
    rw [← hoccP d]
    exact L.mapCell hev (castSuccEmb_trans_snoc u y hy) hco d
  have hc := full_correct I X T hA hB hD t ht (by omega) hsmall
    (respects_castCell hr (L.lawful hev)) (L.label u C) hclass (X.cap_ne_bot hclass) hplab
  obtain ⟨s, hs, he, hmap⟩ := exists_restriction_with_map (onePointProj e) hvD hsD G.map hoccD hr
  obtain ⟨hyRoot, htup, heval⟩ := restrict_actual_extension hM.consistent e rfl hy hev hs
  have hval (d : Cell P.scheme) :
      L.label (snoc (e.trans u) y hyRoot) s (SemScheme.castCell he.symm d) =
        L.label (snoc u y hy) r (SemScheme.castCell hr.symm (G.map d)) := by
    rw [← hmap d]; exact (L.mapCell hev htup hs _).symm
  exact ⟨y, hy, hyRoot, s, heval, he, by simpa only [hval] using hc⟩

end
end VaughtConjecture.Knight.GrowthCarrierEvaluation
