/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedInitial
public import VaughtConjecture.Knight.PaddedIteration
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.PaddedFaceLift

@[expose] public section

namespace VaughtConjecture.Knight.Padded

open Transform Value ExtOrd SourcePrefixRows PairedSlotComparison CanonicalPairedInverse SharpWitnessComposition

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

abbrev faceBoundary {K : Spec A} {n : ℕ} (S : SemScheme n) {B : Finset ι}
    {e : Fin n ↪ ι} {he : Finset.univ.image e = B} {i j : ℕ}
    (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) K.boundaryRows)
    (hi : i ≤ j) (d : S.scheme.below (Finset.univ, i)) : K.boundary.below (A, j) :=
  G.belowAmbient d.1 (d.2.2.trans hi)

/-- The two native fibre operations used by the installed lift. The caller
supplies this only at grades where the requested fibre is enabled. -/
abbrev NativeFibre (K : Spec A) {n : ℕ} (S : SemScheme n) {i j : ℕ}
    (g : S.scheme.below (Finset.univ, i) → K.boundary.below (A, j)) : Prop :=
  K.context.Fibre j (fun d => K.field (g d).1)
    (RespectsSemanticsBelow S.rows (Finset.univ, i))

namespace Layer

variable {K : Spec A} {j : ℕ} (M : Layer K j)

abbrev original (d : Cell K.boundary) : Cell M.carrier :=
  M.baseMap (RelativeLadderLayer.old K.boundary K.one d)

theorem original_index (d : Cell K.boundary) :
    M.carrier.cell (M.original d) = K.boundary.cell d :=
  (M.base_index _).trans (RelativeLadderLayer.old_index K.boundary K.one d)

abbrev originalAt (d : K.boundary.below (A, j)) : M.carrier.below (A, j) :=
  ⟨M.original d.1, by rw [M.original_index]; exact d.2⟩

abbrev faceAt {n : ℕ} (S : SemScheme n) {B : Finset ι}
    {e : Fin n ↪ ι} {he : Finset.univ.image e = B} {i : ℕ}
    (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) K.boundaryRows)
    (hi : i ≤ j) : S.scheme.below (Finset.univ, i) → M.carrier.below (A, j) :=
  M.originalAt ∘ faceBoundary S G hi

theorem source_original (a : K.Anchor j) (d : Cell K.boundary) :
    M.source a (M.original d) = K.fields j a (K.field d) := by
  rw [original, M.source_base]
  exact RelativeLadderLayer.renderWith_old _ _ _ _ _ _ _ (M.anchor_ranks a) d

theorem originalAt_grade (d : K.boundary.below (A, j)) :
    M.carrier.grade (M.originalAt d).1 = K.boundary.grade d.1 :=
  congrArg Prod.snd (M.original_index d.1)

theorem faceAt_grade {B : Finset ι} {E : CellScheme B} {r : Semantics E}
    (F : ExactSemanticFace r K.boundaryRows) (d : Cell E) (hd : E.grade d ≤ j) :
    M.carrier.grade (M.originalAt (F.belowAmbient d hd)).1 = E.grade d :=
  (M.originalAt_grade _).trans (congrArg Prod.snd (F.index d))

theorem exists_section (hj : 1 ≤ j) {s : K.State} (hs : K.Admitted j s) :
    ∃ w, RespectsSemanticsBelow M.rows (A, j) w ∧
      ∀ d, w (M.originalAt d) = K.profile s (K.field d.1) := by
  obtain ⟨q, hq, hcanon, δ, hδ, hread, hreflect, _⟩ := K.context.exists_supported_decoder hj hs
  let a := K.anchor j q hq hcanon
  have ha : K.fields j a = K.profile q := rfl
  have ho : RespectsSemanticsBelow K.boundaryRows (A, j) (fun d => δ (K.fields j a (K.field d.1))) := by
    simpa only [ha, hread] using K.profile_lawful s hs
  refine ⟨fun d => δ (M.source a d.1), M.decoded_lawful a hδ (ha ▸ hreflect) ho, ?_⟩
  intro d
  change δ (M.source a (M.original d.1)) = _
  rw [M.source_original, ha, hread]

theorem exists_face {Y : Type*} (g : Y → K.boundary.below (A, j))
    (hj : 1 ≤ j) {s : K.State} (hs : K.Admitted j s)
    {v : Y → ExtOrd} (hread : ∀ d, K.profile s (K.field (g d).1) = v d) :
    ∃ w, RespectsSemanticsBelow M.rows (A, j) w ∧ ∀ d, w (M.originalAt (g d)) = v d := by
  obtain ⟨w, hw, hr⟩ := M.exists_section hj hs
  grind

theorem protected_face {Y : Type*} (g : Y → K.boundary.below (A, j))
    {a : K.Anchor j} {s : K.State} {b : ℕ}
    (R : K.context.ProtectedRepair (K.fields j a) s j b) (hb : b ≤ 2 * Fintype.card K.Field + 1)
    {v : Y → ExtOrd} (hread : ∀ d, K.profile s (K.field (g d).1) = v d) :
    ∃ w, RespectsSemanticsBelow M.rows (A, j) w ∧ (∀ d, w (M.originalAt (g d)) = v d) ∧
      ∀ d, min (w d) (grid j b) = min (M.source a d.1) (grid j b) := by
  let a' := K.anchor j R.encoded R.admitted R.canonical
  have ha' : K.fields j a' = K.profile R.encoded := rfl
  obtain ⟨hw, hag⟩ := R.decode_rows (M.source_lawful a) (M.source_lawful a')
    (fun d => M.source_supported a d.1) (fun d => M.source_prefix a' a (sourceGrid_endpoint hb)
      (ha' ▸ R.prefix_eq) d.1)
  refine ⟨_, hw, fun d => ?_, hag⟩
  change R.decoder (M.source a' (M.original (g d).1)) = _
  rw [M.source_original, ha', R.readback]
  exact hread d

variable {n i : ℕ} {S : SemScheme n} {B : Finset ι} {e : Fin n ↪ ι}
  {he : Finset.univ.image e = B}
  {G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) K.boundaryRows}
  (hi : i ≤ j)

local notation "reading" => faceBoundary S G hi

/-- The chart, coding, normalization and physical readback are independent of the fibre. -/
theorem capped_fibre (F : NativeFibre K S reading) :
    PaddedOwnerRepair.Capped S.rows M.rows (M.faceAt S G hi) := by
  refine PaddedOwnerRepair.capped_of_catalogue (m := Fintype.card K.Field) M.source
    (fun d => M.faceAt_grade G d.1 (d.2.2.trans hi)) M.source_chart M.source_short fun a => ?_
  have hs := K.state_admitted a
  have he : K.context.profile (K.state a) = K.fields j a := K.state_profile a
  refine ⟨(fun d => K.fields j a (K.field (reading d).1)), fun d => M.source_original a (reading d).1,
    he ▸ F.lawful hs,
    fun d => CanonicalPairedProfiles.inventory_coded _ _ (K.canonical j a) _, ?_⟩
  intro b hb v hv hag
  obtain ⟨t, _, hval, ⟨r⟩⟩ := F.repair hs (he.symm ▸ K.canonical j a) hv
    (he ▸ hag)
  exact M.protected_face reading (he ▸ r) hb hval

theorem lift_fibre (hj : 1 ≤ j)
    (fibre : (∃ d : S.scheme.below (Finset.univ, i), S.scheme.grade d.1 = j) → NativeFibre K S reading)
    (hr : PaddedFaceLift.Restore S.rows M.rows (M.faceAt S G hi)) :
    PaddedFaceLift.Lift S.rows M.rows (M.faceAt S G hi) := by
  refine PaddedFaceLift.lift_of_capped (PaddedFaceLift.complete_full S hj hi)
    (fun h {p} hp => ?_) (fun h => M.capped_fibre hi (fibre h)) hr
  obtain ⟨t, ht, hv⟩ := (fibre h).bottom hp
  exact M.exists_face reading hj ht hv

end Layer

end

end VaughtConjecture.Knight.Padded
