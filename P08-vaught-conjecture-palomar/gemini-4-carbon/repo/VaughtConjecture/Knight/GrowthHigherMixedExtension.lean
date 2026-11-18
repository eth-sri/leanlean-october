/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedNativeRows
public import VaughtConjecture.Knight.GrowthReplicatedRows
public import VaughtConjecture.Knight.AmbientGradeCharts

@[expose] public section

namespace VaughtConjecture.Knight
open Transform Value ExtOrd AmalgamationPlan

namespace SharpWitnessComposition
theorem map_respects_of_bottom_reflection {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : BoundedMap K ν)
    (hbot : ∀ d, ν (r d) = ⊥ ↔ r d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) :=
  (map_respects_iff_rowBlockBottom hr hK hν).mpr
    (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hr) hbot)
end SharpWitnessComposition

namespace SupportLadderRows
open FiniteProfileControllers

section ImageReflection
variable {X Q : Type*} [Finite X] [Finite Q] [Nonempty Q] {H : ℕ} {profile : Q → X → ℕ}

def Component (profile : Q → X → ℕ) (a : Q) (v : Point H X Q) : Prop := index profile a v ≠ 0

private theorem component_iff (hH : 0 < H) (a : Q) (v : Point H X Q) :
    Component profile a v ↔ Agree (profile a) (profile (parent v)) 1 ∧ ceiling profile v ≠ 0 := by
  unfold Component index
  rw [Ne, Nat.min_eq_zero_iff, not_or]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(agree_cut H _ _).mono (Nat.pos_of_ne_zero h1), h2⟩,
    fun ⟨h1, h2⟩ => ⟨Nat.pos_iff_ne_zero.mp (le_cut hH h1), h2⟩⟩

private theorem image_ne_bot_iff (a : Q) {f : ℕ → ExtOrd} (h0 : f 0 = ⊥)
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) (v : Point H X Q) :
    image profile a f v ≠ ⊥ ↔ Component profile a v :=
  ⟨fun hne hz => hne (by unfold image; rw [hz, h0]),
   fun hne => hp _ (Nat.pos_of_ne_zero hne) (index_le a v)⟩

theorem bottom_reflection_image (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
    {p : Point H X Q → ExtOrd} (hp : Lawful profile p) (a₀ : Q) {f : ℕ → ExtOrd} (h0 : f 0 = ⊥)
    (hf : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) {τ : ExtOrd → ExtOrd} {h : ExtOrd} (hh : h ≠ ⊥)
    (hread : ∀ v, τ (image profile a₀ f v) = min (p v) h) (hspare : τ (f H) = h)
    (v : Point H X Q) : τ (image profile a₀ f v) = ⊥ ↔ image profile a₀ f v = ⊥ := by
  have hsp : p (leaf hH a₀) ≠ ⊥ := fun hz => by
    have h1 := hread (leaf hH a₀)
    rw [image, index_leaf, cut_refl, hspare, hz, min_bot_left] at h1
    exact hh h1
  have hsup : p v ≠ ⊥ ↔ Component profile a₀ v := by
    rcases (lawful_iff_shape hbound hH p).mp hp with hz | ⟨b, g, -, hg0, -, hgp, he⟩
    · exact absurd (hz _) hsp
    have hb (w : Point H X Q) : p w ≠ ⊥ ↔ Component profile b w := by
      rw [he w]; exact image_ne_bot_iff b hg0 hgp w
    have hleaf := (component_iff hH b (leaf hH a₀)).mp ((hb _).mp hsp)
    rw [hb v, component_iff hH, component_iff hH]
    exact and_congr_left fun _ =>
      ⟨fun ha d => (hleaf.1 d).symm.trans (ha d), fun ha d => (hleaf.1 d).trans (ha d)⟩
  have himg := image_ne_bot_iff (profile := profile) a₀ h0 hf v
  rw [hread v]
  refine ⟨fun h1 => by_contra fun hne => ?_, fun h1 => ?_⟩
  · exact (min_eq_bot.mp h1).elim (hsup.mpr (himg.mp hne)) hh
  · rw [not_not.mp fun hne => (himg.mpr (hsup.mp hne)) h1, min_bot_left]
end ImageReflection
end SupportLadderRows

namespace Growth
open CappedDonor.Ref SharpWitnessComposition
noncomputable section
theorem Admitted.map_on_profile {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
    {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
    {semA : Semantics DA} {semQ : Semantics DQ} (X : RelativeData DA semA DQ semQ)
    {j : ℕ} {S : State DA DQ} (hS : Admitted X j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ f : Field DA DQ, σ (S.profile f) = ⊥ → S.profile f = ⊥) : Admitted X j (S.map σ) where
  private_lawful := map_respects_of_bottom_reflection hS.private_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ)
    fun d => ⟨hbot (.inl d.1), fun hz => by rw [hz, hσ.bot]⟩
  donor_lawful := map_respects_of_bottom_reflection hS.donor_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ)
    fun d => ⟨hbot (.inr d.1), fun hz => by rw [hz, hσ.bot]⟩
  visible f := by rw [State.profile_map]; exact selfVis_map hσ hj (hS.visible f)
  shared d := congrArg σ (hS.shared d)
  correct hN hc := by
    have hc' : InClass X.ZA S.privateValues := fun d =>
      ⟨fun hd => (hc d).mp (by change σ (S.privateValues d.1) = ⊥; rw [hd, hσ.bot]),
       fun hd => hbot (.inl d.1) ((hc d).mpr hd)⟩
    obtain ⟨hz, hf, ht⟩ := hS.correct hN hc'
    refine ⟨fun z hZ => ?_, fun f hF => ?_, fun y hT => ?_⟩
    · change min (σ (S.donorValues z)) (σ (S.privateValues X.req.C)) = ⊥
      rw [← hσ.mono.map_min]; exact (congrArg σ (hz z hZ)).trans hσ.bot
    · change min (σ (S.donorValues f)) (σ (S.privateValues X.req.C)) =
        min (extVisibilityReplace (σ (S.privateValues (X.req.ρ f).1)) X.req.N
          (X.req.off f)) (σ (S.privateValues X.req.C))
      rw [← map_comm hσ hN _ (X.off_lt f hF), ← hσ.mono.map_min, ← hσ.mono.map_min]
      exact congrArg σ (hf f hF)
    · change min (extVisibilityReplace (σ (S.privateValues X.req.a.1)) X.req.N X.req.R)
        (σ (S.privateValues X.req.C)) ≤
        min (σ (S.donorValues y)) (σ (S.privateValues X.req.C))
      rw [← map_comm hσ hN _ X.req.R_lt_N.le, ← hσ.mono.map_min, ← hσ.mono.map_min]
      exact hσ.mono (ht y hT)
end
end Growth

namespace GradePrefixProjection
theorem respectsBelow {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {ρ : Cell D → ExtOrd} {H : ℕ → ExtOrd}
    (ha : Antitone H)
    (hp : ∀ j ≤ BJ.2, RespectsSemanticsBelow sem (BJ.1, j) (fun d => min (ρ d.1) (H j))) :
    RespectsSemanticsBelow sem BJ (fun d => min (ρ d.1) (H (D.grade d.1))) where
  orderly d := (hp (D.grade d.1) d.2.2).orderly ⟨d.1, d.2.1, le_rfl⟩
  locality c := by
    refine transformsTo_congr rfl rfl ?_ ((hp (D.grade c.1) c.2.2).locality ⟨c.1, c.2.1, le_rfl⟩)
    funext d
    change min (min (ρ d.1) (H (D.grade c.1))) (min (ρ c.1) (H (D.grade c.1))) =
      min (min (ρ d.1) (H (D.grade d.1))) (min (ρ c.1) (H (D.grade c.1)))
    have hdc : H (D.grade c.1) ≤ H (D.grade d.1) := ha d.2.2
    rw [min_min_min_comm, min_self, min_min_min_comm, min_eq_right hdc]
  availability c e hs hg := by
    obtain ⟨w, hw, hle⟩ := (hp (D.grade c.1) c.2.2).availability
      ⟨c.1, c.2.1, le_rfl⟩ ⟨e.1, e.2.1, hg.symm.le⟩ hs hg
    refine ⟨⟨w.1, w.2.1, w.2.2.trans c.2.2⟩, hw, ?_⟩
    have hgrade : D.grade w.1 = D.grade c.1 := (congrArg Prod.snd hw).trans hg.symm
    change min (ρ c.1) (H (D.grade c.1)) ≤ min (ρ w.1) (H (D.grade w.1))
    rwa [hgrade]
end GradePrefixProjection

namespace ScopeReplicationCharts
open ScopeReplicationCarrier ScopeReplicationSemantics
theorem erase_index {ι : Type*} [DecidableEq ι] {A : Finset ι}
    (D : CellScheme A) (B C : Finset ι)
    (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
    {U : Finset ι} {j : ℕ} (hm : U = A ∨ Mixed B C U)
    (c : Cell (scheme D B C)) (hc : (scheme D B C).cell c = (U, j)) :
    D.cell (erase D B C c) = (A, j) := by
  refine Prod.ext ?_ (show D.grade (erase D B C c) = j from
    (erase_grade D B C c).trans (congrArg Prod.snd hc))
  change D.scope (erase D B C c) = A
  by_contra hne
  have hs : D.scope (erase D B C c) = U :=
    (erase_scope_of_ne D B C c hne).trans (congrArg Prod.fst hc)
  rcases hm with rfl | hm
  · exact hne hs
  · exact (hcover _ hne).elim (fun hb => hm.1 (hs ▸ hb)) (fun hc' => hm.2 (hs ▸ hc'))

theorem auxiliary_eq {ι : Type*} [DecidableEq ι] {A : Finset ι}
    (D : CellScheme A) (B C : Finset ι)
    (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
    (sem : Semantics D) {U V : Finset ι} {j : ℕ}
    (hU : U ∈ D.plan) (hmU : U = A ∨ Mixed B C U) (hjU : j ≤ U.card)
    (hV : V ∈ D.plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
    (hUV : U ⊆ V) {p q : (scheme D B C).below (V, j) → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) (V, j) p)
    (hq : RespectsSemanticsBelow (rows D B C hcover sem) (V, j) q)
    (hag : ∀ d : (scheme D B C).below (U, j),
      p (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d))
    (z : (scheme D B C).below (V, j)) (hz : D.scope (erase D B C z.1) = A) : p z = q z := by
  have hg : D.grade (erase D B C z.1) ≤ j := (erase_grade D B C z.1).le.trans z.2.2
  let u : (scheme D B C).below (U, j) :=
    ⟨atScope D B C U hU hmU (erase D B C z.1) hz (hg.trans hjU),
      (atScope_index D B C U hU hmU (erase D B C z.1) hz (hg.trans hjU)) ▸ ⟨le_rfl, hg⟩⟩
  let v : (scheme D B C).below (V, j) :=
    ⟨atScope D B C V hV hmV (erase D B C z.1) hz (hg.trans hjV),
      (atScope_index D B C V hV hmV (erase D B C z.1) hz (hg.trans hjV)) ▸ ⟨le_rfl, hg⟩⟩
  let u' := CellScheme.below.mono (D := scheme D B C) (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) u
  have heu : erase D B C u.1 = erase D B C v.1 :=
    (erase_atScope D B C U hU hmU (erase D B C z.1) hz (hg.trans hjU)).trans
      (erase_atScope D B C V hV hmV (erase D B C z.1) hz (hg.trans hjV)).symm
  have hsu : (scheme D B C).scope u'.1 ⊆ (scheme D B C).scope v.1 := by
    change ((scheme D B C).cell u.1).1 ⊆ ((scheme D B C).cell v.1).1
    rw [atScope_index, atScope_index]; exact hUV
  have hsz : (scheme D B C).scope z.1 ⊆ (scheme D B C).scope v.1 := by
    change (scheme D B C).scope z.1 ⊆ ((scheme D B C).cell v.1).1
    rw [atScope_index]; exact z.2.1
  have hez : erase D B C z.1 = erase D B C v.1 :=
    (erase_atScope D B C V hV hmV (erase D B C z.1) hz (hg.trans hjV)).symm
  exact (copy_eq D B C hcover sem hp z v hsz hez).trans
    ((copy_eq D B C hcover sem hp u' v hsu heu).symm.trans
      ((hag u).trans ((copy_eq D B C hcover sem hq u' v hsu heu).trans
        (copy_eq D B C hcover sem hq z v hsz hez).symm)))
end ScopeReplicationCharts

namespace GrowthPaddedOwnerProvenance
open Growth GrowthOrderedBase GrowthHigherSources GrowthPaddedContract GrowthPaddedIteration
open GrowthPaddedNativeRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

structure Origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier) where
  birth : ℕ
  birth_le : birth ≤ t
  height : birth + 2 ≤ A.card
  member : Catalogue X (birth + 2)
  map : Cell (build I X T hA hB hC birth height).carrier →
    Cell (build I X T hA hB hC t ht).carrier
  index : ∀ d, (build I X T hA hB hC t ht).carrier.cell (map d) =
    (build I X T hA hB hC birth height).carrier.cell d
  base : ∀ d, map ((build I X T hA hB hC birth height).baseMap d) =
    (build I X T hA hB hC t ht).baseMap d
  occurrence : map (owner I X T hA hB hC birth height member) = c
  domain : (build I X T hA hB hC birth height).carrier.below
      ((build I X T hA hB hC birth height).carrier.cell
        (owner I X T hA hB hC birth height member)) ≃
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c)
  domain_val : ∀ d, (domain d).1 = map d.1
  row : ∀ d, (build I X T hA hB hC t ht).rows.E c (domain d) =
    source I X T hA hB hC birth height member d.1

theorem exists_origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier)
    (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c) :
    Nonempty (Origin I X T hA hB hC t ht c) := by
  induction t with
  | zero =>
    rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨d, rfl⟩ | ⟨a, rfl⟩
    · have hi : (build I X T hA hB hC 0 ht).carrier.cell
          (GrowthPaddedSuccessor.old I X T hA hB hC d) = (base I X T hA hB hC).cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      have he : (base I X T hA hB hC).grade d = 1 :=
        base_full_grade I X T hA hB hC d ((congrArg Prod.fst hi).symm.trans hc)
      have hh : 2 ≤ (base I X T hA hB hC).grade d := hg.trans_eq (congrArg Prod.snd hi)
      omega
    · exact ⟨⟨0, le_rfl, ht, a, id, fun _ => rfl, fun _ => rfl, rfl,
        Equiv.refl _, fun _ => rfl, owner_row I X T hA hB hC 0 ht a⟩⟩
  | succ t ih =>
    let P := build I X T hA hB hC t (by omega)
    obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration P.carrier
      (Catalogue X (t + 2 + 1)) (t + 2 + 1) (Nat.succ_pos _) (by omega)).surjective c
    change SourceLayerCarrier.toCell _ _ _ _ _ x = c at hx
    rcases x with d | a
    · rw [← hx] at hc hg ⊢
      have hi : (build I X T hA hB hC (t + 1) ht).carrier.cell
          (SourceLayerCarrier.toCell P.carrier (Catalogue X (t + 2 + 1))
            (t + 2 + 1) (Nat.succ_pos _) (by omega) (.inl d)) = P.carrier.cell d :=
        SourceLayerCarrier.cell_toCell _ _ _ _ _ _
      obtain ⟨O⟩ := ih (by omega) d ((congrArg Prod.fst hi).symm.trans hc)
        (hg.trans_eq (congrArg Prod.snd hi))
      exact ⟨⟨O.birth, O.birth_le.trans (Nat.le_succ t), O.height, O.member,
        fun e => GrowthPaddedStepRows.old P (by omega) (O.map e),
        fun e => (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (O.index e),
        fun e => congrArg (GrowthPaddedStepRows.old _ _) (O.base e),
        congrArg (GrowthPaddedStepRows.old _ _) O.occurrence,
        O.domain.trans (GrowthPaddedStepRows.ownerEquiv P (by omega) (by omega) d),
        fun e => congrArg (GrowthPaddedStepRows.old _ _) (O.domain_val e),
        fun e => (GrowthPaddedStepRows.inherited_row P (by omega) (by omega) d
          (O.domain e)).trans (O.row e)⟩⟩
    · rw [← hx]
      exact ⟨⟨t + 1, le_rfl, ht, a, id, fun _ => rfl, fun _ => rfl, rfl,
        Equiv.refl _, fun _ => rfl, owner_row I X T hA hB hC (t + 1) ht a⟩⟩

def origin (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier)
    (hc : (build I X T hA hB hC t ht).carrier.scope c = A)
    (hg : 2 ≤ (build I X T hA hB hC t ht).carrier.grade c) :
    Origin I X T hA hB hC t ht c :=
  Classical.choice (exists_origin I X T hA hB hC t ht c hc hg)

namespace Origin
variable {I X T hA hB hC} {t : ℕ} {ht : t + 2 ≤ A.card}
  {c : Cell (build I X T hA hB hC t ht).carrier}
  (O : Origin I X T hA hB hC t ht c)

theorem owner_index : (build I X T hA hB hC t ht).carrier.cell c = (A, O.birth + 2) :=
  (congrArg _ O.occurrence).symm.trans ((O.index _).trans
    (GrowthPaddedNativeRows.owner_index I X T hA hB hC O.birth O.height O.member))

theorem row_diagonal :
    (build I X T hA hB hC t ht).rows.E c ⟨c, GradedLe.refl _⟩ = ceiling I O.birth := by
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨owner I X T hA hB hC O.birth O.height O.member, GradedLe.refl _⟩
  exact (congrArg ((build I X T hA hB hC t ht).rows.E c)
    (Subtype.ext ((O.domain_val e).trans O.occurrence))).symm.trans
    ((O.row e).trans (source_diagonal I X T hA hB hC O.birth O.height O.member))

def baseArgument (d : Cell (GrowthPaddedContract.base I X T hA hB hC))
    (hd : GradedLe ((GrowthPaddedContract.base I X T hA hB hC).cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c) :=
  ⟨(build I X T hA hB hC t ht).baseMap d, by rw [PaddedTower.Layer.base_index, O.owner_index]; exact hd⟩

theorem row_base_source (d : Cell (GrowthPaddedContract.base I X T hA hB hC))
    (hd : GradedLe ((GrowthPaddedContract.base I X T hA hB hC).cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).rows.E c (O.baseArgument d hd) =
      source I X T hA hB hC O.birth O.height O.member
        ((build I X T hA hB hC O.birth O.height).baseMap d) := by
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨(build I X T hA hB hC O.birth O.height).baseMap d, by
      rw [PaddedTower.Layer.base_index, GrowthPaddedNativeRows.owner_index]; exact hd⟩
  rw [← show O.domain e = O.baseArgument d hd from Subtype.ext ((O.domain_val e).trans (O.base d)),
    O.row]

theorem row_original (d : Cell I.boundary)
    (hd : GradedLe (I.boundary.cell d) (A, O.birth + 2)) :
    (build I X T hA hB hC t ht).rows.E c
      (O.baseArgument (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)
        (by simpa only [RelativeLadderLayer.old_index] using hd)) =
      fields X (O.birth + 2) O.member (field I d) := by
  rw [row_base_source, source_original]

def ladderArgument (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell c) :=
  O.baseArgument (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)
    (by rw [RelativeLadderLayer.added_index]; exact ⟨le_rfl, by omega⟩)

theorem row_ladder (v : RelativeLadderLayer.Point
    (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC O.birth O.height O.member)
        (LadderScalarRendering.level
          (LadderScalarRendering.values (fields X (O.birth + 2) O.member))
          (ceiling I O.birth)) v :=
  (O.row_base_source _ _).trans (source_ladder I X T hA hB hC O.birth O.height O.member v)

theorem row_shadow_sup (f : Field I.right.scheme I.left.scheme) :
    (Finset.univ : Finset (Catalogue X 1)).sup
      (fun b => (build I X T hA hB hC t ht).rows.E c
        (O.ladderArgument (SupportLadderRows.shadow b f))) =
      fields X (O.birth + 2) O.member f := by
  have hl (v) : (build I X T hA hB hC t ht).rows.E c (O.ladderArgument v) =
      source I X T hA hB hC O.birth O.height O.member (ladder I X T hA hB hC O.birth O.height v) :=
    O.row_base_source _ _
  simp only [hl]
  exact source_shadow_sup I X T hA hB hC O.birth O.height O.member f

theorem row_spare :
    (build I X T hA hB hC t ht).rows.E c
      (O.ladderArgument (SupportLadderRows.leaf (Nat.succ_pos _)
        (anchor I X T hA hB hC O.birth O.height O.member))) = ceiling I O.birth :=
  (O.row_base_source _ _).trans (source_spare I X T hA hB hC O.birth O.height O.member)

theorem row_ceiling_at (i : ℕ) (hi : 1 ≤ i) (hib : i ≤ O.birth + 2) :
    ∃ d : (build I X T hA hB hC t ht).carrier.below
        ((build I X T hA hB hC t ht).carrier.cell c),
      (build I X T hA hB hC t ht).carrier.cell d.1 = (A, i) ∧
        (build I X T hA hB hC t ht).rows.E c d = ceiling I O.birth := by
  obtain ⟨d, hd, hv⟩ := source_ceiling_at I X T hA hB hC O.birth O.height O.member i hi hib
  let e : (build I X T hA hB hC O.birth O.height).carrier.below
      ((build I X T hA hB hC O.birth O.height).carrier.cell
        (owner I X T hA hB hC O.birth O.height O.member)) :=
    ⟨d, by rw [hd, GrowthPaddedNativeRows.owner_index]; exact ⟨le_rfl, hib⟩⟩
  exact ⟨O.domain e, (congrArg _ (O.domain_val e)).trans ((O.index d).trans hd),
    (O.row e).trans hv⟩
end Origin
end
end GrowthPaddedOwnerProvenance

namespace GrowthMixedGradeOne
open Growth GrowthHigherSources SupportLadderRows LadderScalarRendering SharpWitnessComposition
open GrowthPaddedContract ScopeReplicationCarrier
noncomputable section

theorem card_pos {ι : Type*} {A : Finset ι} (h : 2 ≤ A.card) : 0 < A.card := by omega

theorem cap_sup {Y : Type*} [Fintype Y] (g : Y → ExtOrd) (h : ExtOrd) :
    min (Finset.univ.sup g) h = Finset.univ.sup fun y => min (g y) h :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => min x h)
    (fun _ _ hxy => min_le_min_right _ hxy) (min_bot_left _)

theorem respectsBelow_zero {ιS : Type*} [DecidableEq ιS] {S : Finset ιS} {DS : CellScheme S}
    (semS : Semantics DS) (r : DS.below (S, 0) → ExtOrd) :
    RespectsSemanticsBelow semS (S, 0) r := by
  have hno (d : DS.below (S, 0)) : False := by
    have h1 : DS.grade d.1 ≤ 0 := d.2.2; have h2 := DS.grade_pos d.1; omega
  exact ⟨fun d => (hno d).elim, fun d => (hno d).elim, fun d => (hno d).elim⟩

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

theorem rungs_pos : 0 < rungs := Nat.succ_pos _

local notation "spare" => SupportLadderRows.leaf (rungs_pos I)

theorem rank_le_rungs (a : Catalogue X 1) (f : Fld) : ranks₁ a f ≤ rungs :=
  (RelativeLadderLayer.rank_bound (fields X 1) a f).le

theorem index_shadow_self (a : Catalogue X 1) (f : Fld) :
    SupportLadderRows.index (H := rungs) ranks₁ a (shadow a f) = ranks₁ a f := by
  change min (FiniteProfileControllers.cut rungs (ranks₁ a) (ranks₁ a)) (ranks₁ a f) = _
  rw [FiniteProfileControllers.cut_refl]
  exact min_eq_right (rank_le_rungs I X a f)

theorem ladderRow_spare_added (a : Catalogue X 1) (v : Pt) :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.added I.boundary (card_pos hA) v) =
      SupportLadderRows.row ranks₁ (spare a) v := by
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ (spare a))
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent (spare a))
      (RelativeLadderLayer.added I.boundary (card_pos hA) v)) = _
  rw [RelativeLadderLayer.rankIndex_added]; rfl

theorem ladderRow_spare_old (a : Catalogue X 1) (d : Cell I.boundary) :
    RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (spare a) (RelativeLadderLayer.old I.boundary (card_pos hA) d) =
      SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d)) := by
  change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ (spare a))
    (RelativeLadderLayer.rankIndex I.boundary (card_pos hA) (GrowthOrderedBase.field I)
      (fields X 1) (SupportLadderRows.parent (spare a))
      (RelativeLadderLayer.old I.boundary (card_pos hA) d)) = _
  rw [RelativeLadderLayer.rankIndex_old, SupportLadderRows.ceiling_leaf]; rfl

theorem row_spare (a : Catalogue X 1) (v : Pt) :
    SupportLadderRows.row ranks₁ (spare a) v =
      SupportLadderRows.source rungs (SupportLadderRows.index ranks₁ a v) := by
  rw [SupportLadderRows.row, SupportLadderRows.ceiling_leaf]; rfl

variable {k : ℕ} (P : Layer I X T hA hB hC k)

local notation "Base" => GrowthPaddedContract.base I X T hA hB hC
local notation "BaseRows" => GrowthPaddedContract.baseRows I X T hA hB hC
local notation "Carrier" => GrowthReplicatedRows.carrier P
local notation "Rows" => GrowthReplicatedRows.rows P
local notation "eraseP" => GrowthReplicatedRows.erase P
local notation "addedB" => RelativeLadderLayer.added I.boundary (card_pos hA)
local notation "oldB" => RelativeLadderLayer.old I.boundary (card_pos hA)
local notation "ladderRow₁" =>
  RelativeLadderLayer.ladderRow I.boundary (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)

theorem base_added_cell (v : Pt) : CellScheme.cell Base (addedB v) = (A, 1) :=
  RelativeLadderLayer.added_index I.boundary (card_pos hA) v

theorem base_old_cell (d : Cell I.boundary) : CellScheme.cell Base (oldB d) = I.boundary.cell d :=
  RelativeLadderLayer.old_index I.boundary (card_pos hA) d

theorem carrier_added_cell (v : Pt) : P.carrier.cell (P.baseMap (addedB v)) = (A, 1) :=
  (P.base_index _).trans (base_added_cell I X T hA hB hC v)

theorem carrier_old_cell (d : Cell I.boundary) :
    P.carrier.cell (P.baseMap (oldB d)) = I.boundary.cell d :=
  (P.base_index _).trans (base_old_cell I X T hA hB hC d)

theorem eq_baseMap_of_grade_le_one (c : Cell P.carrier) (hc : P.carrier.grade c ≤ 1) :
    ∃ b, c = P.baseMap b := by
  rcases P.cases c with h | ⟨_, hg, _⟩
  · exact h
  · omega

theorem A_mem_plan : A ∈ P.carrier.plan := by
  have h := P.carrier.scope_mem_plan (P.baseMap (addedB (spare (Growth.zeroMember X 1 le_rfl))))
  rwa [show P.carrier.scope _ = A from congrArg Prod.fst (carrier_added_cell I X T hA hB hC P _)] at h

variable (U : Finset ι) (hU : U ∈ P.carrier.plan) (hm : U = A ∨ Mixed B C U)

theorem scope_added (v : Pt) : P.carrier.scope (P.baseMap (addedB v)) = A :=
  congrArg Prod.fst (carrier_added_cell I X T hA hB hC P v)

theorem grade_added (v : Pt) : P.carrier.grade (P.baseMap (addedB v)) = 1 :=
  congrArg Prod.snd (carrier_added_cell I X T hA hB hC P v)

include hm in
theorem grade_added_le (v : Pt) : P.carrier.grade (P.baseMap (addedB v)) ≤ U.card := by
  rw [grade_added]
  rcases hm with rfl | hm
  · omega
  · exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr
      fun h => hm.1 (h ▸ Finset.empty_subset _))

def ladderAt (v : Pt) : CellScheme.below Carrier (U, 1) :=
  ⟨atScope P.carrier B C U hU hm (P.baseMap (addedB v))
      (scope_added I X T hA hB hC P v) (grade_added_le I X T hA hB hC P U hm v), by
    change GradedLe ((scheme P.carrier B C).cell _) (U, 1)
    rw [atScope_index, grade_added]
    exact GradedLe.refl _⟩

theorem ladder_index (v : Pt) :
    CellScheme.cell Carrier (ladderAt I X T hA hB hC P U hU hm v).1 = (U, 1) :=
  (atScope_index P.carrier B C U hU hm (P.baseMap (addedB v))
    (scope_added I X T hA hB hC P v) (grade_added_le I X T hA hB hC P U hm v)).trans
    (congrArg (fun k => (U, k)) (grade_added I X T hA hB hC P v))

theorem erase_ladder (v : Pt) :
    eraseP (ladderAt I X T hA hB hC P U hU hm v).1 = P.baseMap (addedB v) :=
  erase_atScope P.carrier B C U hU hm (P.baseMap (addedB v))
    (scope_added I X T hA hB hC P v) (grade_added_le I X T hA hB hC P U hm v)

def ladderBelow (c v : Pt) :
    CellScheme.below Carrier (CellScheme.cell Carrier (ladderAt I X T hA hB hC P U hU hm c).1) :=
  ⟨(ladderAt I X T hA hB hC P U hU hm v).1, by rw [ladder_index, ladder_index]; exact GradedLe.refl _⟩

theorem row_ladder (c v : Pt) :
    Semantics.E Rows (ladderAt I X T hA hB hC P U hU hm c).1
      (ladderBelow I X T hA hB hC P U hU hm c v) = SupportLadderRows.row ranks₁ c v := by
  have hv : GradedLe (CellScheme.cell Base (addedB v)) (CellScheme.cell Base (addedB c)) := by
    rw [base_added_cell, base_added_cell]; exact GradedLe.refl _
  have h1 : Semantics.E Rows (ladderAt I X T hA hB hC P U hU hm c).1
      (ladderBelow I X T hA hB hC P U hU hm c v) =
      P.rows.E (P.baseMap (addedB c)) ⟨P.baseMap (addedB v), by simpa only [P.base_index] using hv⟩ :=
    P.rows.E_congr (erase_ladder I X T hA hB hC P U hU hm c)
      (erase_ladder I X T hA hB hC P U hU hm v)
  rw [h1, P.base_row (addedB c) ⟨addedB v, hv⟩]
  refine (RelativeLadderLayer.row_added I.boundary I.rows (card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC) c ⟨addedB v, hv⟩).trans ?_
  change SupportLadderRows.source _ (RelativeLadderLayer.rankIndex I.boundary (card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1) (SupportLadderRows.parent c) (addedB v)) = _
  rw [RelativeLadderLayer.rankIndex_added]; rfl

theorem ladder_lawful {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, 1) p) :
    Lawful ranks₁ (fun v => p (ladderAt I X T hA hB hC P U hU hm v)) :=
  ⟨fun v => by
    have hv := hp.orderly (ladderAt I X T hA hB hC P U hU hm v)
    change p _ = extVisibilityReplace (p _) (CellScheme.cell Carrier _).2
      (CellScheme.cell Carrier _).2 at hv
    rw [ladder_index] at hv; exact hv.symm,
   fun c => transformsTo_congr
    (funext fun v => congrArg Prod.snd (ladder_index I X T hA hB hC P U hU hm v))
    (funext fun v => row_ladder I X T hA hB hC P U hU hm c v) rfl
    ((hp.locality (ladderAt I X T hA hB hC P U hU hm c)).reindex
      (ladderBelow I X T hA hB hC P U hU hm c))⟩

def shadowSup (p : CellScheme.below Carrier (U, 1) → ExtOrd) (f : Fld) : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt I X T hA hB hC P U hU hm (shadow b f))

def spareSup (p : CellScheme.below Carrier (U, 1) → ExtOrd) : ExtOrd :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt I X T hA hB hC P U hU hm (spare b))

theorem ladder_le_spareSup {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, 1) p) (v : Pt) :
    p (ladderAt I X T hA hB hC P U hU hm v) ≤ spareSup I X T hA hB hC P U hU hm p :=
  ((ladder_lawful I X T hA hB hC P U hU hm hp).le_parent
    (rank_le_rungs I X) (rungs_pos I) v).trans
    (Finset.le_sup (f := fun b => p (ladderAt I X T hA hB hC P U hU hm (spare b)))
      (Finset.mem_univ _))

theorem exists_spare_chart {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, 1) p) :
    ∃ (a : Catalogue X 1) (τ : ExtOrd → ExtOrd), Witness (gTop 1) τ ∧
      p (ladderAt I X T hA hB hC P U hU hm (spare a)) = spareSup I X T hA hB hC P U hU hm p ∧
      (∀ x, τ x ≤ spareSup I X T hA hB hC P U hU hm p) ∧
      (∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v)) ∧
      ∀ (z : CellScheme.below Carrier (U, 1)) (d : Cell I.boundary),
        eraseP z.1 = P.baseMap (oldB d) →
        τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d))) = p z := by
  let a₀ := Growth.zeroMember X 1 le_rfl
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Catalogue X 1))
    (fun b => p (ladderAt I X T hA hB hC P U hU hm (spare b))) ⟨a₀, Finset.mem_univ _⟩
  let c := ladderAt I X T hA hB hC P U hU hm (spare a)
  have hpc : p c = spareSup I X T hA hB hC P U hU hm p :=
    le_antisymm (Finset.le_sup (f := fun b => p (ladderAt I X T hA hB hC P U hU hm (spare b)))
      (Finset.mem_univ a)) (Finset.sup_le hmax)
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := (⟨c.1, GradedLe.refl _⟩ : CellScheme.below Carrier (CellScheme.cell Carrier c.1)))
    (fun d => d.2.2) (hp.orderly c).symm (hp.locality c)
  have hgrade : CellScheme.grade Carrier c.1 = 1 :=
    congrArg Prod.snd (ladder_index I X T hA hB hC P U hU hm _)
  refine ⟨a, τ, hgrade ▸ hτ, hpc, fun x => (hb x).trans_eq hpc, fun v => ?_, fun z d hz => ?_⟩
  · have h := hr (ladderBelow I X T hA hB hC P U hU hm (spare a) v)
    rw [row_ladder] at h
    exact h.trans (min_eq_left
      ((ladder_le_spareSup I X T hA hB hC P U hU hm hp v).trans_eq hpc.symm))
  · have hg : CellScheme.grade Carrier z.1 = 1 :=
      le_antisymm z.2.2 (CellScheme.grade_pos Carrier z.1)
    have hgd : I.boundary.grade d ≤ 1 := by
      have he : P.carrier.grade (eraseP z.1) = CellScheme.grade Carrier z.1 :=
        erase_grade P.carrier B C z.1
      rw [hz, show P.carrier.grade (P.baseMap (oldB d)) = I.boundary.grade d from
        congrArg Prod.snd (carrier_old_cell I X T hA hB hC P d), hg] at he
      exact he.le
    have hd : GradedLe (CellScheme.cell Base (oldB d)) (CellScheme.cell Base (addedB (spare a))) := by
      rw [base_old_cell, base_added_cell]
      exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hgd⟩
    let e : CellScheme.below Carrier (CellScheme.cell Carrier c.1) :=
      ⟨z.1, by rw [ladder_index]; exact z.2⟩
    have hrow : Semantics.E Rows c.1 e =
        SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d)) := by
      have h1 : Semantics.E Rows c.1 e =
          P.rows.E (P.baseMap (addedB (spare a))) ⟨P.baseMap (oldB d), by simpa only [P.base_index] using hd⟩ :=
        P.rows.E_congr (erase_ladder I X T hA hB hC P U hU hm (spare a)) hz
      rw [h1, P.base_row (addedB (spare a)) ⟨oldB d, hd⟩]
      exact (RelativeLadderLayer.row_added I.boundary I.rows (card_pos hA)
        (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC) (spare a)
        ⟨oldB d, hd⟩).trans (ladderRow_spare_old I X hA a d)
    have hzw : p z ≤ spareSup I X T hA hB hC P U hU hm p := by
      obtain ⟨w, hw, hle⟩ := hp.availability z (ladderAt I X T hA hB hC P U hU hm (spare a₀))
        (by change CellScheme.scope Carrier z.1 ⊆ (CellScheme.cell Carrier _).1
            rw [ladder_index]; exact z.2.1)
        (hg.trans (congrArg Prod.snd (ladder_index I X T hA hB hC P U hU hm _)).symm)
      have hw' := hw.trans (ladder_index I X T hA hB hC P U hU hm _)
      have hei := ScopeReplicationCharts.erase_index P.carrier B C
        (GrowthReplicatedRows.proper_covered P) hm w.1 hw'
      obtain ⟨b0, hb0⟩ := eq_baseMap_of_grade_le_one I X T hA hB hC P _
        (by change (P.carrier.cell _).2 ≤ 1; rw [hei])
      rcases RelativeLadderLayer.cell_cases I.boundary (card_pos hA) b0 with ⟨d0, rfl⟩ | ⟨v0, rfl⟩
      · exact (GrowthOrderedBase.proper I hB hC d0
          ((congrArg Prod.fst (carrier_old_cell I X T hA hB hC P d0)).symm.trans
            (congrArg Prod.fst (hb0 ▸ hei)))).elim
      · have heq := GrowthReplicatedRows.copy_eq P hp w
          (ladderAt I X T hA hB hC P U hU hm v0)
          (by change (CellScheme.cell Carrier w.1).1 ⊆ (CellScheme.cell Carrier _).1
              rw [hw', ladder_index])
          (hb0.trans (erase_ladder I X T hA hB hC P U hU hm v0).symm)
        exact hle.trans (heq.trans_le (ladder_le_spareSup I X T hA hB hC P U hU hm hp v0))
    have h := hr e; rw [hrow] at h
    exact h.trans (min_eq_left (hzw.trans_eq hpc.symm))

theorem shadowSup_eq_spare {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
    (hread : ∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) =
      p (ladderAt I X T hA hB hC P U hU hm v)) (f : Fld) :
    shadowSup I X T hA hB hC P U hU hm p f =
      τ (SupportLadderRows.source rungs (ranks₁ a f)) := by
  have he := SupportLadderRows.readout_image (H := rungs)
    (rank_le_rungs I X) a (SupportLadderRows.source_mono rungs) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1)) from
    Subsingleton.elim _ _] at he
  rw [← he, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot, shadowSup]
  refine congrArg _ (funext fun b => ?_)
  rw [Function.comp_apply, ← hread, row_spare]; rfl

theorem spare_bottom_reflection {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (_ : Witness (gTop 1) τ)
    (hread : ∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) =
      p (ladderAt I X T hA hB hC P U hU hm v))
    (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (hmax : p (ladderAt I X T hA hB hC P U hU hm (spare a)) = spareSup I X T hA hB hC P U hU hm p)
    (hne : spareSup I X T hA hB hC P U hU hm p ≠ ⊥) (v : Pt) :
    τ (SupportLadderRows.row ranks₁ (spare a) v) = ⊥ ↔
      SupportLadderRows.row ranks₁ (spare a) v = ⊥ := by
  have : Nonempty (Catalogue X 1) := ⟨Growth.zeroMember X 1 le_rfl⟩
  have himg (w : Pt) : SupportLadderRows.row ranks₁ (spare a) w =
      SupportLadderRows.image ranks₁ a (SupportLadderRows.source rungs) w := row_spare I X a w
  rw [himg v]
  exact SupportLadderRows.bottom_reflection_image (rank_le_rungs I X) (rungs_pos I)
    (ladder_lawful I X T hA hB hC P U hU hm hp) a (SupportLadderRows.source_zero rungs)
    (fun i hi hiH => by
      rw [Ne, SupportLadderRows.source_bot_iff, min_eq_left hiH]; exact hi.ne') hne
    (fun w => by
      rw [← himg w, hread, min_eq_left (ladder_le_spareSup I X T hA hB hC P U hU hm hp w)])
    (by
      have hd := (hread (spare a)).trans hmax
      rwa [row_spare, SupportLadderRows.index_leaf, FiniteProfileControllers.cut_refl] at hd) v

theorem original_readback_one {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (z : CellScheme.below Carrier (U, 1)) (d : Cell I.boundary)
    (hz : eraseP z.1 = P.baseMap (oldB d)) :
    p z = shadowSup I X T hA hB hC P U hU hm p (GrowthOrderedBase.field I d) := by
  obtain ⟨a, τ, hτ, -, -, hread, horig⟩ := exists_spare_chart I X T hA hB hC P U hU hm hp
  exact (horig z d hz).symm.trans (shadowSup_eq_spare I X T hA hB hC P U hU hm hτ hread _).symm

def layerSection (a : Catalogue X 1) (τ : ExtOrd → ExtOrd) (c : Cell P.carrier) : ExtOrd := by
  classical
  exact if h : ∃ b, c = P.baseMap b then τ (ladderRow₁ (spare a) h.choose) else ⊥

theorem layerSection_baseMap (a : Catalogue X 1) (τ : ExtOrd → ExtOrd) (b : Cell Base) :
    layerSection I X T hA hB hC P a τ (P.baseMap b) = τ (ladderRow₁ (spare a) b) := by
  classical
  unfold layerSection
  split_ifs with h
  · exact congrArg (fun x => τ (ladderRow₁ (spare a) x)) (P.base_mono.injective h.choose_spec.symm)
  · exact absurd ⟨b, rfl⟩ h

theorem layerSection_lawful {p : CellScheme.below Carrier (U, 1) → ExtOrd}
    {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)
    (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (hmax : p (ladderAt I X T hA hB hC P U hU hm (spare a)) = spareSup I X T hA hB hC P U hU hm p)
    (hb : ∀ x, τ x ≤ spareSup I X T hA hB hC P U hU hm p)
    (hread : ∀ v : Pt, τ (SupportLadderRows.row ranks₁ (spare a) v) =
      p (ladderAt I X T hA hB hC P U hU hm v)) :
    RespectsSemanticsBelow P.rows (A, 1) (fun d => layerSection I X T hA hB hC P a τ d.1) := by
  have hbase : RespectsSemanticsBelow BaseRows (A, 1) (fun d => τ (ladderRow₁ (spare a) d.1)) := by
    have hlad := RelativeLadderLayer.ladder_respects I.boundary I.rows
      (card_pos hA) (GrowthOrderedBase.field I) (fields X 1)
      (GrowthOrderedBase.proper I hB hC) (GrowthOrderedBase.anchor_lawful I X T) (spare a)
    by_cases hne : spareSup I X T hA hB hC P U hU hm p = ⊥
    · have hz : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hne)
      simp only [hz]; exact respectsBelow_bot _ (A, 1)
    · refine map_respects_of_bottom_reflection hlad (fun d => d.2.2) (boundedMap_of_witness hτ)
        fun d => ?_
      rcases RelativeLadderLayer.cell_cases I.boundary (card_pos hA) d.1 with ⟨e, he⟩ | ⟨v, hv⟩
      · rw [he, ladderRow_spare_old I X hA a e, ← index_shadow_self I X a, ← row_spare I X a]
        exact spare_bottom_reflection I X T hA hB hC P U hU hm hτ hread hp hmax hne _
      · rw [hv, ladderRow_spare_added I X hA a v]
        exact spare_bottom_reflection I X T hA hB hC P U hU hm hτ hread hp hmax hne v
  have hrhs : RespectsSemanticsBelow BaseRows (CellScheme.cell Base (addedB (spare a)))
      (fun d => layerSection I X T hA hB hC P a τ (P.baseMap d.1)) := by
    have hc := GradeCutLayerRows.cast_respects Base BaseRows
      (base_added_cell I X T hA hB hC (spare a)).symm hbase
    have he : (fun d : CellScheme.below Base (CellScheme.cell Base (addedB (spare a))) =>
        τ (ladderRow₁ (spare a) d.1)) =
        fun d => layerSection I X T hA hB hC P a τ (P.baseMap d.1) :=
      funext fun d => (layerSection_baseMap I X T hA hB hC P a τ d.1).symm
    rwa [← he]
  exact GradeCutLayerRows.cast_respects P.carrier P.rows
    (carrier_added_cell I X T hA hB hC P (spare a))
    ((P.base_respects (addedB (spare a)) (layerSection I X T hA hB hC P a τ)).mpr hrhs)

end
end GrowthMixedGradeOne

namespace GrowthHigherMixed
open Growth GrowthHigherSources GrowthPaddedContract GrowthPaddedIteration SupportLadderRows
open LadderScalarRendering SharpWitnessComposition GrowthMixedGradeOne
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)

abbrev tower := build I X T hA hB hC t ht
abbrev carrier := GrowthReplicatedRows.carrier (tower I X T hA hB hC t ht)
abbrev rows := GrowthReplicatedRows.rows (tower I X T hA hB hC t ht)
abbrev erase := GrowthReplicatedRows.erase (tower I X T hA hB hC t ht)

local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht
local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

def original (d : Cell I.boundary) : Cell (P).carrier :=
  (P).baseMap (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

theorem original_index (d : Cell I.boundary) :
    (P).carrier.cell (original I X T hA hB hC t ht d) = I.boundary.cell d :=
  ((P).base_index _).trans (RelativeLadderLayer.old_index _ _ d)

theorem original_injective : Function.Injective (original I X T hA hB hC t ht) :=
  ((P).base_mono.comp
    (SourceLayerCarrier.old_order I.boundary Pt 1 Nat.one_pos (by omega))).injective

abbrev ladder (v : Pt) : Cell (P).carrier :=
  GrowthPaddedNativeRows.ladder I X T hA hB hC t ht v

theorem ladder_index (v : Pt) :
    (P).carrier.cell (ladder I X T hA hB hC t ht v) = (A, 1) :=
  GrowthPaddedNativeRows.ladder_index I X T hA hB hC t ht v

theorem original_or_full (c : Cell (P).carrier) :
    (∃ d : Cell I.boundary, c = original I X T hA hB hC t ht d) ∨ (P).carrier.scope c = A := by
  rcases (P).cases c with ⟨b, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) b with
      ⟨d, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨d, rfl⟩
    · exact Or.inr (congrArg Prod.fst (ladder_index I X T hA hB hC t ht v))
  · exact Or.inr hs

section Observed
variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card)

def place (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) : (D).below (U, j) :=
  ⟨ScopeReplicationCarrier.atScope (P).carrier B C U
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm c hc (hg.trans hj),
    by rw [ScopeReplicationCarrier.atScope_index]; exact ⟨le_rfl, hg⟩⟩

theorem place_index (c) (hc) (hg) : (D).cell
    (place I X T hA hB hC t ht U hU hm j hj c hc hg).1 = (U, (P).carrier.grade c) :=
  ScopeReplicationCarrier.atScope_index (P).carrier B C U _ hm c hc (hg.trans hj)

theorem erase_place (c) (hc) (hg) : erase I X T hA hB hC t ht
    (place I X T hA hB hC t ht U hU hm j hj c hc hg).1 = c :=
  ScopeReplicationCarrier.erase_atScope (P).carrier B C U _ hm c hc (hg.trans hj)

def ladderAt (hj0 : 1 ≤ j) (v : Pt) : (D).below (U, j) :=
  place I X T hA hB hC t ht U hU hm j hj (ladder I X T hA hB hC t ht v)
    (congrArg Prod.fst (ladder_index I X T hA hB hC t ht v))
    ((congrArg Prod.snd (ladder_index I X T hA hB hC t ht v)).le.trans hj0)

theorem ladderAt_index (hj0 : 1 ≤ j) (v : Pt) :
    (D).cell (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v).1 = (U, 1) :=
  (place_index I X T hA hB hC t ht U hU hm j hj _ _ _).trans
    (congrArg (fun k => (U, k)) (congrArg Prod.snd (ladder_index I X T hA hB hC t ht v)))

theorem erase_ladderAt (hj0 : 1 ≤ j) (v : Pt) : erase I X T hA hB hC t ht
    (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v).1 = ladder I X T hA hB hC t ht v :=
  erase_place I X T hA hB hC t ht U hU hm j hj _ _ _

def shadowSup (hj0 : 1 ≤ j) (p : (D).below (U, j) → ExtOrd) (f : Fld) : ExtOrd :=
  Finset.univ.sup fun a : Catalogue X 1 =>
    p (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f))

def nativeArgument (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (z : (D).below (U, j)) (hz : (D).grade z.1 ≤ (P).carrier.grade c) :
    (P).carrier.below ((P).carrier.cell c) :=
  ⟨erase I X T hA hB hC t ht z.1,
    ((P).carrier.isPlan.subset_of_mem ((P).carrier.scope_mem_plan _)).trans hc.symm.le,
    (ScopeReplicationCarrier.erase_grade (P).carrier B C z.1).le.trans hz⟩

theorem exists_owner_chart {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p)
    (c : Cell (P).carrier) (hc : (P).carrier.scope c = A) (hg : (P).carrier.grade c ≤ j) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop ((P).carrier.grade c)) τ ∧
      ∀ (z : (D).below (U, j)) (hz : (D).grade z.1 ≤ (P).carrier.grade c),
        τ ((P).rows.E c (nativeArgument I X T hA hB hC t ht U j c hc z hz)) =
          min (p z) (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)) := by
  let q := place I X T hA hB hC t ht U hU hm j hj c hc hg
  obtain ⟨τ, hτ, -, hr⟩ := exists_bounded_exact_capped_witness
    (c := (⟨q.1, GradedLe.refl _⟩ : (D).below ((D).cell q.1)))
    (fun d => d.2.2) (hp.orderly q).symm (hp.locality q)
  have hgrade := congrArg Prod.snd (place_index I X T hA hB hC t ht U hU hm j hj c hc hg)
  change (D).grade q.1 = (P).carrier.grade c at hgrade
  change Witness (gTop ((D).grade q.1)) τ at hτ
  rw [hgrade] at hτ
  refine ⟨τ, hτ, fun z hz => ?_⟩
  let d : (D).below ((D).cell q.1) := ⟨z.1, by rw [place_index]; exact ⟨z.2.1, hz⟩⟩
  exact (congrArg τ ((P).rows.E_congr (erase_place I X T hA hB hC t ht U hU hm j hj c hc hg)
    rfl).symm).trans (hr d)

section Owner
variable (hj0 : 1 ≤ j) {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}
  (c : Cell (tower I X T hA hB hC t ht).carrier)
  (hc : (tower I X T hA hB hC t ht).carrier.scope c = A)
  (hg : (tower I X T hA hB hC t ht).carrier.grade c ≤ j)
  (O : GrowthPaddedOwnerProvenance.Origin I X T hA hB hC t ht c)
  {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop ((tower I X T hA hB hC t ht).carrier.grade c)) τ)
  (hread : ∀ (z : CellScheme.below (carrier I X T hA hB hC t ht) (U, j))
      (hz : (carrier I X T hA hB hC t ht).grade z.1 ≤
        (tower I X T hA hB hC t ht).carrier.grade c),
    τ ((tower I X T hA hB hC t ht).rows.E c
      (nativeArgument I X T hA hB hC t ht U j c hc z hz)) =
        min (p z) (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)))

include hτ hread in
private theorem owner_recognition (f : Fld) :
    τ (fields X (O.birth + 2) O.member f) =
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p f)
        (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)) := by
  rw [← O.row_shadow_sup f, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot,
    shadowSup, cap_sup]
  refine Finset.sup_congr rfl fun a _ => ?_
  have hz : (D).grade (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f)).1 ≤
      (P).carrier.grade c :=
    (congrArg Prod.snd (ladderAt_index I X T hA hB hC t ht U hU hm j hj hj0 _)).le.trans
      ((P).carrier.grade_pos c)
  exact (congrArg τ ((P).rows.E_congr rfl
    (erase_ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f))).symm).trans (hread _ hz)

include hread in
private theorem owner_ceiling : τ (GrowthPaddedNativeRows.ceiling I O.birth) =
    p (place I X T hA hB hC t ht U hU hm j hj c hc hg) := by
  have hz : (D).grade (place I X T hA hB hC t ht U hU hm j hj c hc hg).1 ≤ (P).carrier.grade c :=
    (congrArg Prod.snd (place_index I X T hA hB hC t ht U hU hm j hj c hc hg)).le
  have hr := hread (place I X T hA hB hC t ht U hU hm j hj c hc hg) hz
  have he : (P).rows.E c (nativeArgument I X T hA hB hC t ht U j c hc
      (place I X T hA hB hC t ht U hU hm j hj c hc hg) hz) =
        GrowthPaddedNativeRows.ceiling I O.birth :=
    ((P).rows.E_congr rfl (erase_place I X T hA hB hC t ht U hU hm j hj c hc hg)).trans
      O.row_diagonal
  rwa [he, min_self] at hr

include O hread in
private theorem exists_lower_dominator (i : ℕ) (hi : 1 ≤ i) (hic : i ≤ (P).carrier.grade c) :
    ∃ d : (D).below (U, j), (D).cell d.1 = (U, i) ∧
      p (place I X T hA hB hC t ht U hU hm j hj c hc hg) ≤ p d := by
  obtain ⟨d, hd, hv⟩ := O.row_ceiling_at i hi (hic.trans_eq (congrArg Prod.snd O.owner_index))
  have hds : (P).carrier.scope d.1 = A := congrArg Prod.fst hd
  have hdg : (P).carrier.grade d.1 = i := congrArg Prod.snd hd
  let z := place I X T hA hB hC t ht U hU hm j hj d.1 hds (hdg.le.trans (hic.trans hg))
  have hzi : (D).cell z.1 = (U, i) :=
    (place_index I X T hA hB hC t ht U hU hm j hj _ _ _).trans (congrArg (fun k => (U, k)) hdg)
  have hzg : (D).grade z.1 ≤ (P).carrier.grade c := (congrArg Prod.snd hzi).le.trans hic
  have he : (P).rows.E c (nativeArgument I X T hA hB hC t ht U j c hc z hzg) =
      GrowthPaddedNativeRows.ceiling I O.birth :=
    ((P).rows.E_congr rfl (erase_place I X T hA hB hC t ht U hU hm j hj _ _ _)).trans hv
  have hr := hread z hzg
  rw [he, owner_ceiling I X T hA hB hC t ht U hU hm j hj c hc hg O hread] at hr
  exact ⟨z, hzi, min_eq_right_iff.mp hr.symm⟩

include O hτ hread in
private theorem owner_original_readback (z : (D).below (U, j)) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC t ht z.1 = original I X T hA hB hC t ht d)
    (hzc : (D).grade z.1 ≤ (P).carrier.grade c) :
    min (p z) (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)) =
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
        (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)) := by
  have he_gr : (P).carrier.grade (erase I X T hA hB hC t ht z.1) = (D).grade z.1 :=
    ScopeReplicationCarrier.erase_grade (P).carrier B C z.1
  rw [hz] at he_gr
  have hdg : I.boundary.grade d ≤ O.birth + 2 :=
    (congrArg Prod.snd (original_index I X T hA hB hC t ht d)).symm.le.trans
      (he_gr.le.trans (hzc.trans_eq (congrArg Prod.snd O.owner_index)))
  have he : (P).rows.E c (nativeArgument I X T hA hB hC t ht U j c hc z hzc) =
      fields X (O.birth + 2) O.member (GrowthOrderedBase.field I d) :=
    ((P).rows.E_congr rfl hz).trans
      (O.row_original d ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hdg⟩)
  exact (hread z hzc).symm.trans ((congrArg τ he).trans
    (owner_recognition I X T hA hB hC t ht U hU hm j hj hj0 c hc hg O hτ hread _))

include hj0 hτ hread in
private theorem owner_bottom_reflection (hp : RespectsSemanticsBelow Rows (U, j) p)
    (hne : p (place I X T hA hB hC t ht U hU hm j hj c hc hg) ≠ ⊥) (f : Fld) :
    τ (fields X (O.birth + 2) O.member f) = ⊥ → fields X (O.birth + 2) O.member f = ⊥ := by
  let a := GrowthPaddedNativeRows.anchor I X T hA hB hC O.birth O.height O.member
  let H := GrowthPaddedNativeRows.ceiling I O.birth
  have hceil := owner_ceiling I X T hA hB hC t ht U hU hm j hj c hc hg O hread
  have hHne : H ≠ ⊥ := fun hz => hne (hceil.symm.trans ((congrArg τ hz).trans hτ.bot))
  have : Nonempty (Catalogue X 1) := ⟨Growth.zeroMember X 1 le_rfl⟩
  have hspare : τ (LadderScalarRendering.level (values (fields X (O.birth + 2) O.member)) H rungs) =
      p (place I X T hA hB hC t ht U hU hm j hj c hc hg) := by
    have he := O.row_ladder (SupportLadderRows.leaf (rungs_pos I) a)
    rw [O.row_spare, SupportLadderRows.image, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl] at he
    exact (congrArg τ he.symm).trans hceil
  have hr (v : Pt) :
      τ (SupportLadderRows.image ranks₁ a
        (LadderScalarRendering.level (values (fields X (O.birth + 2) O.member)) H) v) =
        min (p (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v))
          (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)) := by
    have hz : (D).grade (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v).1 ≤
        (P).carrier.grade c :=
      (congrArg Prod.snd (ladderAt_index I X T hA hB hC t ht U hU hm j hj hj0 v)).le.trans
        ((P).carrier.grade_pos c)
    exact (congrArg τ (((P).rows.E_congr rfl
      (erase_ladderAt I X T hA hB hC t ht U hU hm j hj hj0 v)).trans
      (O.row_ladder v)).symm).trans (hread _ hz)
  have hrefl := SupportLadderRows.bottom_reflection_image (rank_le_rungs I X) (rungs_pos I)
    (GrowthMixedGradeOne.ladder_lawful I X T hA hB hC P U
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm
      (hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)))
    a (level_zero _ _)
    (fun i hi _ => level_pos (bot_not_values _) (values_bound (anchor_bound X O.member)) hHne hi)
    hne hr hspare (shadow a f)
  rw [SupportLadderRows.image, index_shadow_self,
    GrowthPaddedNativeRows.anchor_ranks, field_readback] at hrefl
  exact hrefl.mp
end Owner

def gradeMax (p : (D).below (U, j) → ExtOrd) (i : ℕ) : ExtOrd := by
  classical
  letI := Fintype.ofFinite ((D).below (U, j))
  exact (Finset.univ : Finset ((D).below (U, j))).sup fun z =>
    if (D).grade z.1 = i then p z else ⊥

theorem le_gradeMax (p : (D).below (U, j) → ExtOrd) (i : ℕ)
    (z : (D).below (U, j)) (hz : (D).grade z.1 = i) :
    p z ≤ gradeMax I X T hA hB hC t ht U j p i := by
  classical
  let _ := Fintype.ofFinite ((D).below (U, j))
  simpa only [gradeMax, ite_eq_left hz] using
    Finset.le_sup (s := (Finset.univ : Finset ((D).below (U, j))))
      (f := fun w => if (D).grade w.1 = i then p w else ⊥) (Finset.mem_univ z)

theorem exists_maximal_owner {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p)
    (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hit : i ≤ t + 2) :
    ∃ (c : Cell (P).carrier) (hc : (P).carrier.scope c = A) (hg : (P).carrier.grade c = i),
      p (place I X T hA hB hC t ht U hU hm j hj c hc (hg.le.trans hij)) =
        gradeMax I X T hA hB hC t ht U j p i := by
  classical
  let _ := Fintype.ofFinite ((D).below (U, j))
  obtain ⟨c₀, hc₀⟩ := GrowthReplicatedRows.complete_through I X T hA hB hC t ht
    (V := (U, i)) (Plan.mem_gradedPlan.mpr ⟨hU, hi, hij.trans hj⟩) hit
  obtain ⟨Ch⟩ := AmbientGradeCharts.exists_chart hp ⟨⟨c₀, by rw [hc₀]; exact ⟨le_rfl, hij⟩⟩, hc₀⟩
  have he := ScopeReplicationCharts.erase_index (P).carrier B C
    (GrowthReplicatedRows.proper_covered P) hm Ch.owner.1 Ch.index
  let c := erase I X T hA hB hC t ht Ch.owner.1
  have hc : (P).carrier.scope c = A := congrArg Prod.fst he
  have hg : (P).carrier.grade c = i := congrArg Prod.snd he
  refine ⟨c, hc, hg, ?_⟩
  have hv := GrowthReplicatedRows.copy_eq P hp Ch.owner
    (place I X T hA hB hC t ht U hU hm j hj c hc (hg.le.trans hij))
    (by change ((D).cell Ch.owner.1).1 ⊆ ((D).cell _).1; rw [Ch.index, place_index])
    (erase_place I X T hA hB hC t ht U hU hm j hj c hc (hg.le.trans hij)).symm
  refine hv.symm.trans (le_antisymm (le_gradeMax I X T hA hB hC t ht U j p i _ Ch.grade) ?_)
  refine Finset.sup_le fun z _ => ?_
  split_ifs with hz
  · exact Ch.dominates z hz
  · exact bot_le

include hU hm hj in
theorem gradeMax_antitone {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p)
    (i k : ℕ) (hi : 1 ≤ i) (hk : 2 ≤ k) (hik : i ≤ k) (hkj : k ≤ j) (hkt : k ≤ t + 2) :
    gradeMax I X T hA hB hC t ht U j p k ≤ gradeMax I X T hA hB hC t ht U j p i := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj hp
    k (by omega) hkj hkt
  let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc (hk.trans_eq hg.symm)
  obtain ⟨τ, _, hr⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp c hc (hg.le.trans hkj)
  obtain ⟨d, hd, hle⟩ := exists_lower_dominator I X T hA hB hC t ht U hU hm j hj
    c hc (hg.le.trans hkj) O hr i hi (hik.trans_eq hg.symm)
  exact hmax.symm.le.trans (hle.trans
    (le_gradeMax I X T hA hB hC t ht U j p i d (congrArg Prod.snd hd)))

theorem exists_admitted_at (hj0 : 1 ≤ j) {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p)
    (k : ℕ) (hk : 2 ≤ k) (hkj : k ≤ j) (hkt : k ≤ t + 2) :
    ∃ S : State I.right.scheme I.left.scheme, Admitted X k S ∧
      ∀ f, S.profile f = min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p f)
        (gradeMax I X T hA hB hC t ht U j p k) := by
  by_cases hz : gradeMax I X T hA hB hC t ht U j p k = ⊥
  · exact ⟨zero, zero_admitted X k, fun f => by rw [hz, min_bot_right]; cases f <;> rfl⟩
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj hp
    k (by omega) hkj hkt
  let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc (hk.trans_eq hg.symm)
  obtain ⟨τ, hτ, hr⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp c hc (hg.le.trans hkj)
  have hb : O.birth + 2 = k := (congrArg Prod.snd O.owner_index).symm.trans hg
  have hτ' : Witness (gTop (O.birth + 2)) τ := hb.symm ▸ (hg ▸ hτ)
  refine ⟨(state X O.member).map τ, hb ▸ ?_, fun f => ?_⟩
  · refine Admitted.map_on_profile X (state_admitted X O.member) hτ' (by omega) fun f hf => ?_
    rw [state_profile] at hf ⊢
    exact owner_bottom_reflection I X T hA hB hC t ht U hU hm j hj hj0 c hc
      (hg.le.trans hkj) O hτ hr hp (fun he => hz (hmax.symm.trans he)) f hf
  · rw [State.profile_map, state_profile, ← hmax]
    exact owner_recognition I X T hA hB hC t ht U hU hm j hj hj0 c hc (hg.le.trans hkj) O hτ hr f

def height (p : (D).below (U, j) → ExtOrd) (k : ℕ) : ExtOrd :=
  if k ≤ 1 then ⊤ else if k ≤ j then gradeMax I X T hA hB hC t ht U j p k else ⊥

include hU hm hj in
theorem height_antitone {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) :
    Antitone (height I X T hA hB hC t ht U j p) := by
  intro a b hab
  by_cases hb : b ≤ 1
  · simp only [height, ite_eq_left hb, ite_eq_left (hab.trans hb), le_refl]
  by_cases ha : a ≤ 1
  · rw [height, height, ite_eq_left ha]; exact le_top
  by_cases hbj : b ≤ j
  · simp only [height, ite_eq_right hb, ite_eq_right ha,
      ite_eq_left hbj, ite_eq_left (hab.trans hbj)]
    exact gradeMax_antitone I X T hA hB hC t ht U hU hm j hj hp a b
      (by omega) (by omega) hab hbj (hbj.trans hjt)
  · simp only [height, ite_eq_right hb, ite_eq_right hbj, bot_le]

theorem boundary_projection (hj0 : 1 ≤ j) {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) :
    RespectsSemanticsBelow I.rows (A, j) (fun d =>
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d.1))
        (height I X T hA hB hC t ht U j p (I.boundary.grade d.1))) := by
  apply GradePrefixProjection.respectsBelow (sem := I.rows) (BJ := (A, j))
    (ρ := fun d => shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
    (height_antitone I X T hA hB hC t ht U hU hm j hj hp hjt)
  intro k hkj
  by_cases hk0 : k = 0
  · subst k; exact respectsBelow_zero I.rows _
  by_cases hk1 : k = 1
  · subst k
    simpa only [height, ite_eq_left (le_refl (1 : ℕ)), min_top_right] using (by
      have hplan : U ∈ (P).carrier.plan := by rw [GrowthPaddedIteration.build_plan]; exact hU
      let q : (D).below (U, 1) → ExtOrd :=
        fun d => p (CellScheme.below.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩) d)
      have hq : RespectsSemanticsBelow Rows (U, 1) q :=
        hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)
      obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ :=
        GrowthMixedGradeOne.exists_spare_chart I X T hA hB hC P U hplan hm hq
      have hl := RelativeLadderLayer.rank_respects I.boundary I.rows (GrowthOrderedBase.field I)
        (fields X 1) a (GrowthHigherSources.anchor_lawful_at I X T a) rungs
      have he : (fun d : I.boundary.below (A, 1) =>
          shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d.1)) =
          fun d => τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d.1))) :=
        funext fun d => GrowthMixedGradeOne.shadowSup_eq_spare I X T hA hB hC P U hplan hm hτ hread _
      rw [he]
      by_cases hz : GrowthMixedGradeOne.spareSup I X T hA hB hC P U hplan hm q = ⊥
      · have htau : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hz)
        simp only [htau]; exact respectsBelow_bot I.rows (A, 1)
      · refine map_respects_of_bottom_reflection hl (fun d => d.2.2) (boundedMap_of_witness hτ)
          fun d => ?_
        have hr := GrowthMixedGradeOne.spare_bottom_reflection I X T hA hB hC P U hplan hm
          hτ hread hq hmax hz (shadow a (GrowthOrderedBase.field I d.1))
        rwa [row_spare, index_shadow_self] at hr :
      RespectsSemanticsBelow I.rows (A, 1) _)
  · obtain ⟨S, hS, he⟩ := exists_admitted_at I X T hA hB hC t ht U hU hm j hj hj0 hp k
      (by omega) hkj (hkj.trans hjt)
    simpa only [height, ite_eq_right (by omega : ¬ k ≤ 1), ite_eq_left hkj, he] using
      GrowthOrderedBase.boundary_lawful_at I X T hS

theorem projection_readback (hj0 : 1 ≤ j) {p : (D).below (U, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (z : (D).below (U, j)) (d : Cell I.boundary)
    (hz : erase I X T hA hB hC t ht z.1 = original I X T hA hB hC t ht d) :
    p z = min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
      (height I X T hA hB hC t ht U j p (I.boundary.grade d)) := by
  have hg : I.boundary.grade d = (D).grade z.1 :=
    (congrArg Prod.snd (original_index I X T hA hB hC t ht d)).symm.trans
      ((congrArg (P).carrier.grade hz).symm.trans (ScopeReplicationCarrier.erase_grade _ B C z.1))
  have hpos := (D).grade_pos z.1
  have hle : (D).grade z.1 ≤ j := z.2.2
  rw [height, hg]
  by_cases h1 : (D).grade z.1 ≤ 1
  · rw [ite_eq_left h1, min_top_right]
    have hg1 : (D).grade z.1 = 1 := by omega
    exact GrowthMixedGradeOne.original_readback_one I X T hA hB hC P U
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm
      (hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)) ⟨z.1, z.2.1, hg1.le⟩ d hz
  · rw [ite_eq_right h1, ite_eq_left hle]
    obtain ⟨c, hc, hgc, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj hp
      ((D).grade z.1) (by omega) z.2.2 (hle.trans hjt)
    let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc
      ((by omega : 2 ≤ (D).grade z.1).trans_eq hgc.symm)
    obtain ⟨τ, hτ, hr⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp c hc
      (hgc.le.trans z.2.2)
    have he := owner_original_readback I X T hA hB hC t ht U hU hm j hj hj0
      c hc (hgc.le.trans z.2.2) O hτ hr z d hz hgc.symm.le
    rwa [hmax, min_eq_left (le_gradeMax I X T hA hB hC t ht U j p _ z rfl)] at he

section Extension
variable (hj0 : 1 ≤ j) (p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd)

def boundaryValue (d : Cell I.boundary) : ExtOrd :=
  min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
    (height I X T hA hB hC t ht U j p (I.boundary.grade d))

def nativeValue (c : Cell (P).carrier) : ExtOrd := by
  classical
  exact if ho : ∃ d, c = original I X T hA hB hC t ht d then
    boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p ho.choose
  else if ha : (P).carrier.scope c = A ∧ (P).carrier.grade c ≤ j then
    p (place I X T hA hB hC t ht U hU hm j hj c ha.1 ha.2)
  else ⊥

theorem native_original (d : Cell I.boundary) :
    nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p (original I X T hA hB hC t ht d) =
      boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p d := by
  classical
  unfold nativeValue; split_ifs with ho
  · exact congrArg (boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p)
      (original_injective I X T hA hB hC t ht ho.choose_spec.symm)
  all_goals exact (ho ⟨d, rfl⟩).elim

theorem native_full (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) :
    nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p c =
      p (place I X T hA hB hC t ht U hU hm j hj c hc hg) := by
  classical
  unfold nativeValue; split_ifs with ho ha
  · obtain ⟨d, rfl⟩ := ho
    exact (GrowthOrderedBase.proper I hB hC d
      ((congrArg Prod.fst (original_index I X T hA hB hC t ht d)).symm.trans hc)).elim
  · rfl
  · exact (ha ⟨hc, hg⟩).elim

def value {V : Finset ι} (z : (D).below (V, j)) : ExtOrd :=
  nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p (erase I X T hA hB hC t ht z.1)

variable {p}

private theorem native_lawful (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) :
    RespectsSemanticsBelow (P).rows (A, j)
      (fun d => nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p d.1) where
  orderly d := by
    rcases original_or_full I X T hA hB hC t ht d.1 with ⟨e, he⟩ | hd
    · have hh : GradedLe (I.boundary.cell e) (A, j) :=
        (original_index I X T hA hB hC t ht e) ▸ (he ▸ d.2)
      simpa only [he, native_original, boundaryValue, CellScheme.grade, original_index] using
        (boundary_projection I X T hA hB hC t ht U hU hm j hj hj0 hp hjt).orderly ⟨e, hh⟩
    · dsimp only
      rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p d.1 hd d.2.2]
      have hv := hp.orderly (place I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2)
      have hi : (D).grade (place I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2).1 =
          (P).carrier.grade d.1 :=
        congrArg (fun x => x.2) (place_index I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2)
      change _ = extVisibilityReplace _ ((D).grade _) ((D).grade _) at hv
      rwa [hi] at hv
  locality c := by
    by_cases hc1 : (P).carrier.grade c.1 ≤ 1
    · have hplan : U ∈ (P).carrier.plan := by rw [GrowthPaddedIteration.build_plan]; exact hU
      let q : (D).below (U, 1) → ExtOrd :=
        fun d => p (CellScheme.below.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩) d)
      have hq : RespectsSemanticsBelow Rows (U, 1) q :=
        hp.mono (show GradedLe (U, 1) (U, j) from ⟨le_rfl, hj0⟩)
      obtain ⟨a, τ, hτ, hmax, hb, hread, -⟩ :=
        GrowthMixedGradeOne.exists_spare_chart I X T hA hB hC P U hplan hm hq
      have hl := GrowthMixedGradeOne.layerSection_lawful I X T hA hB hC P U hplan hm
        hτ hq hmax hb hread
      have he : (fun d : (P).carrier.below (A, 1) =>
          nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p d.1) =
          fun d => GrowthMixedGradeOne.layerSection I X T hA hB hC P a τ d.1 := by
        funext d
        obtain ⟨b, hb'⟩ := GrowthMixedGradeOne.eq_baseMap_of_grade_le_one I X T hA hB hC P d.1 d.2.2
        rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) b with
            ⟨e, rfl⟩ | ⟨v, rfl⟩
        · have hge : I.boundary.grade e ≤ 1 :=
            (congrArg Prod.snd (original_index I X T hA hB hC t ht e)).symm.le.trans
              ((congrArg (P).carrier.grade hb').symm.le.trans d.2.2)
          rw [hb']
          change nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p
            (original I X T hA hB hC t ht e) = _
          rw [native_original, boundaryValue, height, ite_eq_left hge, min_top_right,
            GrowthMixedGradeOne.layerSection_baseMap, ladderRow_spare_old I X hA a e]
          exact GrowthMixedGradeOne.shadowSup_eq_spare I X T hA hB hC P U hplan hm hτ hread _
        · have hvs : (P).carrier.scope ((P).baseMap (RelativeLadderLayer.added
              I.boundary (by omega : 0 < A.card) v)) = A :=
            congrArg Prod.fst (ladder_index I X T hA hB hC t ht v)
          have hvg : (P).carrier.grade ((P).baseMap (RelativeLadderLayer.added
              I.boundary (by omega : 0 < A.card) v)) ≤ j :=
            (congrArg Prod.snd (ladder_index I X T hA hB hC t ht v)).le.trans hj0
          rw [hb', native_full I X T hA hB hC t ht U hU hm j hj hj0 p _ hvs hvg,
            GrowthMixedGradeOne.layerSection_baseMap, ladderRow_spare_added I X hA a v]
          exact (hread v).symm
      exact (he.symm ▸ hl).locality ⟨c.1, c.2.1, hc1⟩
    rcases c with ⟨c, hcut⟩
    change ¬ (P).carrier.grade c ≤ 1 at hc1
    rcases original_or_full I X T hA hB hC t ht c with ⟨d, hd⟩ | hc
    · have hgd : I.boundary.grade d ≤ j :=
        (congrArg Prod.snd (original_index I X T hA hB hC t ht d)).symm.le.trans
          ((congrArg (P).carrier.grade hd).symm.le.trans hcut.2)
      subst c
      have horig : RespectsSemanticsBelow (P).rows
          ((P).carrier.cell (original I X T hA hB hC t ht d))
          (fun e => nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p e.1) := by
        apply ((P).base_respects (RelativeLadderLayer.old I.boundary (by omega) d) _).mpr
        apply (RelativeLadderLayer.old_respects_iff I.boundary I.rows (by omega)
          (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC) d _).mpr
        have hl := (boundary_projection I X T hA hB hC t ht U hU hm j hj hj0 hp hjt).mono
          (show GradedLe (I.boundary.cell d) (A, j) from
            ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hgd⟩)
        have he : (fun e : I.boundary.below (I.boundary.cell d) =>
            nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p
              (original I X T hA hB hC t ht e.1)) =
            fun e => boundaryValue I X T hA hB hC t ht U hU hm j hj hj0 p e.1 :=
          funext fun e => native_original I X T hA hB hC t ht U hU hm j hj hj0 p e.1
        change RespectsSemanticsBelow I.rows (I.boundary.cell d) (fun e =>
          nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p
            (original I X T hA hB hC t ht e.1))
        rw [he]; exact hl
      exact horig.locality ⟨original I X T hA hB hC t ht d, GradedLe.refl _⟩
    · have hg2 : 2 ≤ (P).carrier.grade c := by omega
      let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc hg2
      obtain ⟨τ, hτ, hr⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp c hc hcut.2
      dsimp only [CellScheme.below.incl]
      apply hτ.transformsTo
      intro d
      rw [gTop_of_le (show (P).carrier.grade d.1 ≤ (P).carrier.grade c from d.2.2), min_top_right,
        native_full I X T hA hB hC t ht U hU hm j hj hj0 p c hc hcut.2]
      rcases original_or_full I X T hA hB hC t ht d.1 with ⟨e, he⟩ | hdf
      · have hed : GradedLe (I.boundary.cell e) ((P).carrier.cell c) :=
          (original_index I X T hA hB hC t ht e) ▸ (he ▸ d.2)
        have hs : (P).rows.E c d = fields X (O.birth + 2) O.member (GrowthOrderedBase.field I e) :=
          ((P).rows.E_congr rfl he).trans (O.row_original e (O.owner_index ▸ hed))
        have hge : I.boundary.grade e ≤ j := hed.2.trans hcut.2
        have hown_le : p (place I X T hA hB hC t ht U hU hm j hj c hc hcut.2) ≤
            height I X T hA hB hC t ht U j p (I.boundary.grade e) := by
          unfold height
          by_cases hi1 : I.boundary.grade e ≤ 1
          · rw [ite_eq_left hi1]; exact le_top
          rw [ite_eq_right hi1, ite_eq_left hge]
          exact (le_gradeMax I X T hA hB hC t ht U j p _ _
            (congrArg Prod.snd (place_index I X T hA hB hC t ht U hU hm j hj c hc hcut.2))).trans
              (gradeMax_antitone I X T hA hB hC t ht U hU hm j hj hp _ ((P).carrier.grade c)
                (by omega) hg2 hed.2 hcut.2 (hcut.2.trans hjt))
        rw [hs, owner_recognition I X T hA hB hC t ht U hU hm j hj hj0 c hc hcut.2 O hτ hr,
          he, native_original, boundaryValue, min_assoc, min_eq_right hown_le]
      · have hgd := d.2.2.trans hcut.2
        have hz : (D).grade (place I X T hA hB hC t ht U hU hm j hj d.1 hdf hgd).1 ≤
            (P).carrier.grade c :=
          (congrArg Prod.snd (place_index I X T hA hB hC t ht U hU hm j hj d.1 hdf hgd)).le.trans d.2.2
        rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p d.1 hdf hgd]
        exact (hr _ hz).symm.trans (congrArg τ
          ((P).rows.E_congr rfl (erase_place I X T hA hB hC t ht U hU hm j hj d.1 hdf hgd)))
  availability c v hs hg := by
    rcases original_or_full I X T hA hB hC t ht v.1 with ⟨e, he⟩ | hv
    · have hev : (P).carrier.cell v.1 = I.boundary.cell e :=
        he ▸ original_index I X T hA hB hC t ht e
      have hem : GradedLe (I.boundary.cell e) (A, j) := hev ▸ v.2
      rcases original_or_full I X T hA hB hC t ht c.1 with ⟨d, hd⟩ | hc
      · have hdc : (P).carrier.cell c.1 = I.boundary.cell d :=
          hd ▸ original_index I X T hA hB hC t ht d
        obtain ⟨w, hw, hle⟩ :=
          (boundary_projection I X T hA hB hC t ht U hU hm j hj hj0 hp hjt).availability
            ⟨d, hdc ▸ c.2⟩ ⟨e, hem⟩
            ((congrArg Prod.fst hdc).symm.le.trans (hs.trans (congrArg Prod.fst hev).le))
            ((congrArg Prod.snd hdc).symm.trans (hg.trans (congrArg Prod.snd hev)))
        exact ⟨⟨original I X T hA hB hC t ht w.1,
          (original_index I X T hA hB hC t ht w.1) ▸ w.2⟩,
          (original_index I X T hA hB hC t ht w.1).trans (hw.trans hev.symm),
          by simpa only [hd, native_original, boundaryValue] using hle⟩
      · exact (GrowthOrderedBase.proper I hB hC e (le_antisymm
          (I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan e))
          (hc.symm.le.trans (hs.trans (congrArg Prod.fst hev).le)))).elim
    · obtain ⟨w, hw, hwg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj
        hp ((P).carrier.grade v.1) ((P).carrier.grade_pos v.1) v.2.2 (v.2.2.trans hjt)
      refine ⟨⟨w, hw.le, hwg.le.trans v.2.2⟩, Prod.ext (hw.trans hv.symm) hwg, ?_⟩
      rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p w hw (hwg.le.trans v.2.2),
        hmax, ← hg]
      rcases original_or_full I X T hA hB hC t ht c.1 with ⟨e, hce⟩ | hf
      · have he : (P).carrier.grade (original I X T hA hB hC t ht e) = I.boundary.grade e :=
          congrArg Prod.snd (original_index I X T hA hB hC t ht e)
        rw [hce, he, native_original, boundaryValue, height]
        split_ifs with he1 hej
        · rw [min_top_right, le_antisymm he1 (I.boundary.grade_pos e)]
          exact Finset.sup_le fun a _ => le_gradeMax I X T hA hB hC t ht U j p 1 _
            (by rw [CellScheme.grade, ladderAt_index])
        · exact min_le_right _ _
        · simp only [min_bot_right, bot_le]
      · rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p c.1 hf c.2.2]
        exact le_gradeMax I X T hA hB hC t ht U j p _ _
          (congrArg (fun x => x.2) (place_index I X T hA hB hC t ht U hU hm j hj c.1 hf c.2.2))

include hU hm hj hj0 in
theorem lawfulExtension (hjt : j ≤ t + 2) (V : Finset ι) (hUV : U ⊆ V)
    (q : (D).below (U, j) → ExtOrd) (hq : RespectsSemanticsBelow Rows (U, j) q) :
    ∃ r : (D).below (V, j) → ExtOrd, RespectsSemanticsBelow Rows (V, j) r ∧
      ∀ d, r (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d) = q d := by
  refine ⟨value I X T hA hB hC t ht U hU hm j hj hj0 q,
    ScopeReplicationSemantics.duplicateBelow_respects (P).carrier B C
      (GrowthReplicatedRows.proper_covered P) (P).rows (J := (V, j)) (K := (A, j))
      (fun d => ⟨(P).carrier.isPlan.subset_of_mem ((P).carrier.scope_mem_plan _),
        (ScopeReplicationCarrier.erase_grade (P).carrier B C d.1).le.trans d.2.2⟩)
      (native_lawful I X T hA hB hC t ht U hU hm j hj hj0 hq hjt),
    fun z => ?_⟩
  change nativeValue I X T hA hB hC t ht U hU hm j hj hj0 q
    (erase I X T hA hB hC t ht z.1) = q z
  rcases original_or_full I X T hA hB hC t ht (erase I X T hA hB hC t ht z.1) with ⟨d, hd⟩ | hz
  · rw [hd, native_original]
    exact (projection_readback I X T hA hB hC t ht U hU hm j hj hj0 hq hjt z d hd).symm
  · rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 q _ hz
      ((ScopeReplicationCarrier.erase_grade (P).carrier B C z.1).le.trans z.2.2)]
    exact (GrowthReplicatedRows.copy_eq P hq z _
      (z.2.1.trans (congrArg Prod.fst
        (place_index I X T hA hB hC t ht U hU hm j hj _ _ _)).symm.le)
      (erase_place I X T hA hB hC t ht U hU hm j hj _ _ _).symm).symm
end Extension
end Observed

theorem eq_of_restriction (U V : Finset ι) (hU : U ∈ R) (hV : V ∈ R)
    (hmU : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
    (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
    (j : ℕ) (hjU : j ≤ U.card) (hjV : j ≤ V.card) (hj0 : 1 ≤ j) (hjt : j ≤ t + 2)
    (hUV : U ⊆ V) {p q : (D).below (V, j) → ExtOrd}
    (hp : RespectsSemanticsBelow Rows (V, j) p) (hq : RespectsSemanticsBelow Rows (V, j) q)
    (hag : ∀ d : (D).below (U, j),
      p (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d)) : p = q := by
  have haux (z : (D).below (V, j))
      (hz : (P).carrier.scope (erase I X T hA hB hC t ht z.1) = A) : p z = q z :=
    ScopeReplicationCharts.auxiliary_eq (P).carrier B C
      (GrowthReplicatedRows.proper_covered P) (P).rows
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hmU hjU
      (by rw [GrowthPaddedIteration.build_plan]; exact hV) hmV hjV hUV hp hq hag z hz
  have hshadow (f : Fld) :
      shadowSup I X T hA hB hC t ht V hV hmV j hjV hj0 p f =
        shadowSup I X T hA hB hC t ht V hV hmV j hjV hj0 q f :=
    Finset.sup_congr rfl fun _ _ => haux _ (by
      rw [erase_ladderAt]; exact congrArg Prod.fst (ladder_index I X T hA hB hC t ht _))
  have hmax_eq (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      gradeMax I X T hA hB hC t ht V j p k = gradeMax I X T hA hB hC t ht V j q k := by
    have hle {r s : (D).below (V, j) → ExtOrd} (hr : RespectsSemanticsBelow Rows (V, j) r)
        (heq : ∀ z : (D).below (V, j),
          (P).carrier.scope (erase I X T hA hB hC t ht z.1) = A → r z = s z) :
        gradeMax I X T hA hB hC t ht V j r k ≤ gradeMax I X T hA hB hC t ht V j s k := by
      obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht V hV hmV j hjV
        hr k hk hkj (hkj.trans hjt)
      rw [← hmax, heq _ (by rw [erase_place]; exact hc)]
      exact le_gradeMax I X T hA hB hC t ht V j s k _
        ((congrArg Prod.snd (place_index I X T hA hB hC t ht V hV hmV j hjV _ _ _)).trans hg)
    exact le_antisymm (hle hp haux) (hle hq fun z hz => (haux z hz).symm)
  have hheight (k : ℕ) : height I X T hA hB hC t ht V j p k =
      height I X T hA hB hC t ht V j q k := by
    unfold height; split_ifs with hk hkj
    · rfl
    · exact hmax_eq k (by omega) hkj
    · rfl
  funext z
  rcases original_or_full I X T hA hB hC t ht (erase I X T hA hB hC t ht z.1) with ⟨d, hd⟩ | hz
  · rw [projection_readback I X T hA hB hC t ht V hV hmV j hjV hj0 hp hjt z d hd,
      projection_readback I X T hA hB hC t ht V hV hmV j hjV hj0 hq hjt z d hd,
      hshadow, hheight]
  · exact haux z hz

theorem cappedLift (U : Finset ι) (hU : U ∈ R)
    (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
    (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j) (hjt : j ≤ t + 2)
    (V : Finset ι) (hV : V ∈ R)
    (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V) (hjV : j ≤ V.card) (hUV : U ⊆ V) :
    CoatomBoundaryExtension.CappedLift Rows
      (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hres⟩ := lawfulExtension I X T hA hB hC t ht U hU hm j hj hj0 hjt V hUV p hp
  have hcap := eq_of_restriction I X T hA hB hC t ht U V hU hV hm hmV j hj hjV hj0 hjt hUV
    (hr.cap hγ) (hq.cap hγ) fun d => (congrArg (fun x => min x γ) (hres d)).trans (hag d).symm
  exact ⟨r, hr, congrFun hcap, hres⟩

end
end GrowthHigherMixed
end VaughtConjecture.Knight
