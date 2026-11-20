/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.CanonicalPairedProfiles
public import VaughtConjecture.Knight.TerminalProfile
public import VaughtConjecture.Knight.RelativeLadderTableDecode
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.ReceivingCatalogueRanks
public import VaughtConjecture.Knight.PairedCoupledSections

@[expose] public section

namespace VaughtConjecture.Knight.Padded

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- The original boundary and canonical source tables. The two constructions differ in
what it means for a state to be admissible, not in how these tables extend the ladder. -/
structure Spec (A : Finset ι) where
  boundary : CellScheme A
  boundaryRows : Semantics boundary
  height : 2 ≤ A.card
  proper : ∀ d : Cell boundary, boundary.scope d ≠ A
  Field : Type
  State : Type 1
  [fieldFinite : Fintype Field]
  context : TerminalProfile.Context State Field
  [anchorFinite : ∀ j, Fintype (context.Anchor j)]
  seed : ∀ j, 1 ≤ j → context.Anchor j
  field : Cell boundary → Field
  state : ∀ {j}, context.Anchor j → State
  state_admitted : ∀ {j} (a : context.Anchor j), context.admitted j (state a)
  state_profile_eq : ∀ {j} (a : context.Anchor j), context.profile (state a) = a.val
  admitted_down : ∀ {i j S}, 1 ≤ i → i ≤ j → context.admitted j S → context.admitted i S
  profile_visible : ∀ {j}, 1 ≤ j → ∀ S, context.admitted j S → ∀ d, SelfVis 1 (context.profile S d)
  profile_lawful : ∀ {j} S, context.admitted j S →
    RespectsSemanticsBelow boundaryRows (A, j) (fun d => context.profile S (field d.1))

attribute [instance] Spec.fieldFinite

namespace Spec

variable (K : Spec A)

@[implicit_reducible]
def Anchor := K.context.Anchor

instance (j : ℕ) : Fintype (K.Anchor j) := K.anchorFinite j

abbrev fields (j : ℕ) (a : K.Anchor j) := a.val

theorem canonical (j : ℕ) (a : K.Anchor j) : K.fields j a ∈ CanonicalPairedProfiles.inventory K.Field j :=
  a.property.1

abbrev anchor (j : ℕ) (S : K.State) (hs : K.context.admitted j S)
    (hc : K.context.profile S ∈ CanonicalPairedProfiles.inventory K.Field j) : K.Anchor j :=
  ⟨_, hc, S, hs, rfl⟩

abbrev profile := K.context.profile

abbrev Admitted := K.context.admitted

theorem state_profile {j : ℕ} (a : K.Anchor j) : K.profile (K.state a) = K.fields j a :=
  K.state_profile_eq a

def normalize {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (S : K.State)
    (hs : K.Admitted j S) (hp : ∀ f, K.profile S f ≠ ⊤) : K.Anchor i :=
  K.anchor i (K.context.norm i S) (K.context.norm_closed hi (K.admitted_down hi hij hs))
    (by simpa only [funext (K.context.norm_profile i S)] using CanonicalPairedProfiles.normalize_mem_inventory K.Field i hp)

theorem normalize_fields {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (S : K.State)
    (hs : K.Admitted j S) (hp : ∀ f, K.profile S f ≠ ⊤) :
    K.fields i (K.normalize hi hij S hs hp) = PairedSlotEncoding.normalize i (K.profile S) :=
  funext (K.context.norm_profile i S)

include K in
theorem one : 0 < A.card := by have := K.height; omega

abbrev base := RelativeLadderLayer.carrier K.boundary K.one (X := K.Field) (Q := K.Anchor 1)

abbrev baseRows := RelativeLadderLayer.rows K.boundary K.boundaryRows K.one K.field (K.fields 1) K.proper

theorem base_full_grade (c : Cell K.base) (hc : K.base.scope c = A) : K.base.grade c = 1 := by
  rcases RelativeLadderLayer.cell_cases K.boundary K.one c with ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exact (K.proper d ((congrArg Prod.fst (RelativeLadderLayer.old_index K.boundary K.one d)).symm.trans hc)).elim
  · exact congrArg Prod.snd (RelativeLadderLayer.added_index K.boundary K.one v)

theorem anchor_proper {j : ℕ} (a : K.Anchor j) (d : K.Field) : K.fields j a d ≠ ⊤ :=
  (K.canonical j a).2 d

theorem anchor_bound {j : ℕ} (a : K.Anchor j) (d : K.Field) :
    K.fields j a d ≤ CanonicalFieldLayer.ceiling j K.Field :=
  (CanonicalPairedProfiles.inventory_bound _ _ (K.canonical j a) d).trans
    (ofOrd_le_ofOrd.mpr (add_le_add (by simp) le_rfl))

theorem anchor_short {j : ℕ} (a : K.Anchor j) (d : K.Field) : Short j (K.fields j a d) :=
  CanonicalPairedProfiles.inventory_short _ _ (K.canonical j a) d

theorem anchor_visible {j : ℕ} (hj : 1 ≤ j) (a : K.Anchor j) (d : K.Field) :
    SelfVis 1 (K.fields j a d) := by
  rw [← K.state_profile a]
  exact K.profile_visible hj _ (K.state_admitted a) d

theorem state_proper {j : ℕ} (a : K.Anchor j) (d : K.Field) : K.profile (K.state a) d ≠ ⊤ := by
  rw [K.state_profile]
  apply K.anchor_proper

theorem state_bound {j : ℕ} (a : K.Anchor j) (d : K.Field) :
    K.profile (K.state a) d ≤ CanonicalFieldLayer.ceiling j K.Field := by
  rw [K.state_profile]
  apply K.anchor_bound

end Spec

/-- Invariant preserved when adding a new grade to an ordered boundary. -/
structure Layer (K : Spec A) (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  consistent : rows.IsConsistent
  baseMap : Cell K.base → Cell carrier
  base_mono : StrictMono baseMap
  base_index : ∀ c, carrier.cell (baseMap c) = K.base.cell c
  base_row : ∀ c (d : K.base.below (K.base.cell c)),
    rows.E (baseMap c) ⟨baseMap d.1, by grind⟩ = K.baseRows.E c d
  base_respects : ∀ c (p : Cell carrier → ExtOrd),
    RespectsSemanticsBelow rows (carrier.cell (baseMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow K.baseRows (K.base.cell c) (fun d => p (baseMap d.1))
  cases : ∀ d, (∃ c, d = baseMap c) ∨
    carrier.scope d = A ∧ 2 ≤ carrier.grade d ∧ carrier.grade d ≤ k
  higher_short : ∀ c, carrier.scope c = A → 2 ≤ carrier.grade c →
    ∀ d : carrier.below (carrier.cell c), Short (carrier.grade c) (rows.E c d)
  pos : 1 ≤ k
  source : K.Anchor k → Cell carrier → ExtOrd
  controller : K.Anchor k → {c : Cell carrier // carrier.cell c = (A, k)}
  controller_row : ∀ a (d : carrier.below (carrier.cell (controller a).1)),
    rows.E (controller a).1 d = source a d.1
  source_leaf : ∀ a b, source a (controller b).1 =
    cut (sourceGrid k (Fintype.card K.Field)) (K.fields k a) (K.fields k b)
  baseAnchor : K.Anchor k → K.Anchor 1
  anchor_ranks : ∀ a d, RelativeLadderLayer.ranks (K.fields 1) (baseAnchor a) d =
    LadderScalarRendering.fieldRank (K.fields k a) d
  source_base : ∀ a d, source a (baseMap d) =
    RelativeLadderLayer.renderWith K.boundary K.one K.field (K.fields 1) (baseAnchor a)
      (K.fields k a) (CanonicalFieldLayer.ceiling k K.Field) d
  source_chart : ∀ {q}, RespectsSemanticsBelow rows (A, k) q →
    ∃ a σ H, Witness (gTop k) σ ∧ (∀ d, carrier.grade d.1 = k → q d ≤ H) ∧
      ∀ d, σ (source a d.1) = min (q d) H
  source_lawful : ∀ a, RespectsSemanticsBelow rows (A, k) (fun d => source a d.1)
  source_supported : ∀ a d, OrbitPrefixSupport.Supported k
    (sourceGrid k (Fintype.card K.Field) : Set ExtOrd) (K.fields k a) (source a d)
  source_prefix : ∀ a b {h}, h ∈ sourceGrid k (Fintype.card K.Field) →
    Agree (K.fields k a) (K.fields k b) h → Agree (source a) (source b) h
  source_ceiling_at : ∀ a i, 1 ≤ i → i ≤ k →
    ∃ c, carrier.cell c = (A, i) ∧ source a c = CanonicalFieldLayer.ceiling k K.Field

namespace Layer

variable {K : Spec A} {k : ℕ} (P : Layer K k)

theorem full_grade (hk : 1 ≤ k) (d : Cell P.carrier) (hd : P.carrier.scope d = A) :
    P.carrier.grade d ≤ k := by
  rcases P.cases d with ⟨c, rfl⟩ | ⟨_, _, hg⟩
  · exact (congrArg Prod.snd (P.base_index c)).trans_le
      ((K.base_full_grade c ((congrArg Prod.fst (P.base_index c)).symm.trans hd)).trans_le hk)
  · exact hg

theorem separated (hk : 1 ≤ k) (d : Cell P.carrier) : ¬ GradedLe (A, k + 1) (P.carrier.cell d) := by
  intro hd
  exact (Nat.not_succ_le_self k) (hd.2.trans (P.full_grade hk d
    ((P.carrier.scope_subset d).antisymm hd.1)))

abbrev leafAt (a : K.Anchor k) : P.carrier.below (A, k) :=
  ⟨(P.controller a).1, (P.controller a).2.symm ▸ GradedLe.refl _⟩

theorem source_diagonal (a : K.Anchor k) :
    P.source a (P.controller a).1 = CanonicalFieldLayer.ceiling k K.Field := by
  rw [P.source_leaf]
  exact cut_refl (sourceGrid_endpoint le_rfl) (fun z hz => CanonicalFieldLayer.grid_bound k K.Field hz) _

theorem source_short (a : K.Anchor k) (d : Cell P.carrier) : Short k (P.source a d) :=
  PairedCoupledSections.supported_short (fun _ hz => CanonicalFieldLayer.grid_short _ _ hz)
    (K.anchor_short a) (P.source_supported a d)

theorem top_chart {q} (hq : RespectsSemanticsBelow P.rows (A, k) q)
    (ht : ∃ d, P.carrier.grade d.1 = k ∧ q d = ⊤) :
    ∃ a σ, Witness (gTop k) σ ∧ ∀ d, σ (P.source a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := P.source_chart hq
  obtain ⟨d, hd, ht⟩ := ht
  have : M = ⊤ := top_le_iff.mp (ht ▸ hM d hd)
  exact ⟨a, σ, hσ, by simp_all⟩

theorem map_lawful (a : K.Anchor k) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop k) δ)
    (hbase : ∀ b : Cell K.base, GradedLe (K.base.cell b) (A, k) →
      RespectsSemanticsBelow K.baseRows (K.base.cell b) (fun d => δ (P.source a (P.baseMap d.1)))) :
    RespectsSemanticsBelow P.rows (A, k) (fun d => δ (P.source a d.1)) := by
  apply map_respects_of_short_or_local (P.source_lawful a) (fun d => d.2.2) hδ
  rintro ⟨c, hc⟩
  rcases P.cases c with ⟨b, rfl⟩ | ⟨hs, hl, _⟩
  · have hr := (P.base_respects b (fun d => δ (P.source a d))).mpr
      (hbase b (P.base_index b ▸ hc))
    exact Or.inr (hr.locality ⟨_, GradedLe.refl _⟩)
  · exact Or.inl (P.higher_short c hs hl)

theorem decoded_lawful (a : K.Anchor k) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop k) δ)
    (hreflect : ∀ f, δ (K.fields k a f) = ⊥ → K.fields k a f = ⊥)
    (horiginal : RespectsSemanticsBelow K.boundaryRows (A, k)
      (fun d => δ (K.fields k a (K.field d.1)))) :
    RespectsSemanticsBelow P.rows (A, k) (fun d => δ (P.source a d.1)) := by
  apply P.map_lawful a hδ
  intro b hb
  simp only [P.source_base]
  exact (RelativeLadderLayer.renderWith_decode_respects K.boundary K.boundaryRows K.one
    K.field (K.fields 1) K.proper _ _ (P.anchor_ranks a) (K.anchor_bound a)
    (K.anchor_visible P.pos a) ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono P.pos)
    P.pos hδ hreflect horiginal).mono hb

variable {j : ℕ} (hj : k ≤ j) (S : K.State) (hS : K.Admitted j S)
  (hp : ∀ f, K.profile S f ≠ ⊤)

abbrev normalized := K.normalize P.pos hj S hS hp

abbrev birth := P.baseAnchor (P.normalized hj S hS hp)

theorem birth_ranks (d : K.Field) :
    RelativeLadderLayer.ranks (K.fields 1) (P.birth hj S hS hp) d =
      LadderScalarRendering.fieldRank (K.profile S) d := by
  rw [birth, P.anchor_ranks, normalized, K.normalize_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize k _ hp d

def render (G : Finset ExtOrd) (H : ExtOrd) (d : Cell P.carrier) : ExtOrd :=
  PairedSlotDecoder.decode k (PairedSlotEncoding.values (K.profile S)) G H
    (P.source (P.normalized hj S hS hp) d)

variable {G : Finset ExtOrd} {H : ExtOrd}

local notation "Rend" => P.render hj S hS hp G H

local notation "baseRender" => RelativeLadderLayer.renderWith K.boundary K.one K.field (K.fields 1)
  (P.birth hj S hS hp) (K.profile S) H

theorem render_base (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H)
    (hb : ∀ d, K.profile S d ≤ H) (d : Cell K.base) : Rend (P.baseMap d) = baseRender d := by
  unfold render
  rw [P.source_base, normalized, K.normalize_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized K.boundary K.one K.field (K.fields 1)
    k _ _ hp hG hH (decode_reserved_ceiling hH hb) d

theorem lawful (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H)
    (hb : ∀ d, K.profile S d ≤ H) :
    RespectsSemanticsBelow P.rows (A, j) (fun d => Rend d.1) := by
  have hbase : RespectsSemanticsBelow K.baseRows (A, j) (fun d => baseRender d.1) :=
    RelativeLadderLayer.renderWith_respects K.boundary K.boundaryRows K.one K.field (K.fields 1)
      K.proper _ _ (P.birth_ranks hj S hS hp) hb (K.profile_visible (P.pos.trans hj) S hS)
      (hH.mono P.pos) (K.profile_lawful S hS)
  have hnative : RespectsSemanticsBelow P.rows (A, k) (fun d => Rend d.1) := by
    apply P.map_lawful _ (PairedSlotDecoder.decode_witness hG hH)
    intro b h
    change RespectsSemanticsBelow K.baseRows _ (fun d => Rend (P.baseMap d.1))
    have hl : GradedLe (K.base.cell b) (A, j) := ⟨h.1, h.2.trans hj⟩
    simp only [P.render_base hj S hS hp hG hH hb]
    exact hbase.mono hl
  apply RespectsSemanticsBelow.of_local
  rintro ⟨c, hc⟩
  rcases P.cases c with ⟨b, rfl⟩ | ⟨_, _, hu⟩
  · apply (P.base_respects b Rend).mpr
    have hl : GradedLe (K.base.cell b) (A, j) := P.base_index b ▸ hc
    simp only [P.render_base hj S hS hp hG hH hb]
    exact hbase.mono hl
  · exact hnative.mono ⟨P.carrier.scope_subset c, hu⟩

theorem bound (hH : SelfVis k H) (hb : ∀ d, K.profile S d ≤ H) (d : Cell P.carrier) : Rend d ≤ H := by
  exact PairedSlotDecoder.decode_le_of_bound hH hb _

theorem supported {l : ℕ} (hl : k ≤ l) (hH : H ∈ G) (d : Cell P.carrier) :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) (K.profile S) (Rend d) :=
  PairedSlotDecoder.decode_supported hl hH _

theorem agreement (T : K.State) (hT : K.Admitted j T) (ht : ∀ d, K.profile T d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hh : h ∈ G) (hhH : h ≤ H)
    (hag : Agree (K.profile S) (K.profile T) h) : Agree Rend (P.render hj T hT ht G H) h := by
  apply decode_agreement hG hH hh hhH hp ht hag
  intro e heG he
  apply P.source_prefix _ _ heG
  simpa only [normalized, K.normalize_fields] using he

theorem ceiling_at (_hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H)
    (hb : ∀ d, K.profile S d ≤ H) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    ∃ c, P.carrier.cell c = (A, i) ∧ Rend c = H := by
  obtain ⟨c, hc, hv⟩ := P.source_ceiling_at (P.normalized hj S hS hp) i hi hik
  exact ⟨c, hc, by rw [render, hv]; exact decode_reserved_ceiling hH hb⟩

end Layer

end

end VaughtConjecture.Knight.Padded
