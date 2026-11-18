/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.CappedDonorSource
public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.MaximalFullLayer

@[expose] public section

namespace VaughtConjecture.Knight.WeightedSourcePrefixLayer
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : ScopedSourcePrefixLayer.Data D k X)
variable (weight : Controller D k → ExtOrd)

/-- The uncapped master has weighted new columns and literal old columns. -/
def master (q : Controller D k) (d : Cell D) : ExtOrd :=
  if hd : D.cell d = (A, k) then min (F.profile q d) (weight ⟨d, hd⟩)
  else F.profile q d

theorem master_old (q : Controller D k) {d : Cell D} (hd : D.cell d ≠ (A, k)) :
    master F weight q d = F.lower q d := by
  simp only [master, hd, ↓reduceDIte, F.profile_old q hd]

theorem master_new (q p : Controller D k) :
    master F weight q p.1 = min (cut F.grid (F.boundary q) (F.boundary p)) (weight p) := by
  simp only [master, p.2, ↓reduceDIte, F.profile_new]

theorem master_le_profile (q : Controller D k) (d : Cell D) :
    master F weight q d ≤ F.profile q d := by
  unfold master
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem master_bound (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    master F weight q d ≤ F.ceiling :=
  (master_le_profile F weight q d).trans (F.profile_bound q d hd)

theorem master_agreement (p q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    min (master F weight p d) (cut F.grid (F.boundary p) (F.boundary q)) =
      min (master F weight q d) (cut F.grid (F.boundary p) (F.boundary q)) := by
  unfold master
  split_ifs with he
  · simpa only [min_right_comm] using
      congrArg (fun x => min x (weight ⟨d, he⟩)) (F.profile_agreement p q d hd)
  · exact F.profile_agreement p q d hd

theorem master_prefix {p q : Controller D k} {h : ExtOrd}
    (hh : h ∈ F.grid) (hpq : Agree (F.boundary p) (F.boundary q) h) :
    Agree (fun d : D.below (A, k) => master F weight p d.1)
      (fun d : D.below (A, k) => master F weight q d.1) h := by
  have ha : Agree (fun d : D.below (A, k) => master F weight p d.1)
      (fun d : D.below (A, k) => master F weight q d.1)
      (cut F.grid (F.boundary p) (F.boundary q)) :=
    fun d => master_agreement F weight p q d.1 d.2.2
  exact ha.mono (le_cut hh hpq)

variable (hvis : ∀ q, SelfVis k (weight q))

include hvis in
theorem master_visible (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    SelfVis (D.grade d) (master F weight q d) := by
  unfold master
  split_ifs with he
  · exact selfVis_min (F.profile_visible q d hd) ((hvis ⟨d, he⟩).mono hd)
  · exact F.profile_visible q d hd

/-- Weighted installation only changes the new index. -/
def rows : Semantics D where
  E c d := if hc : D.cell c = (A, k) then
    min (master F weight ⟨c, hc⟩ d.1) (weight ⟨c, hc⟩) else F.base.E c d
  orderly c d := by
    dsimp only
    split_ifs with hc
    · have hd : D.grade d.1 ≤ k := by
        simpa only [CellScheme.grade, hc] using d.2.2
      exact (selfVis_min (master_visible F weight hvis ⟨c, hc⟩ d.1 hd)
        ((hvis ⟨c, hc⟩).mono hd)).symm
    · exact F.base.orderly c d

theorem row_old {c : Cell D} (hc : D.cell c ≠ (A, k)) :
    (rows F weight hvis).E c = F.base.E c := by
  funext d
  simp only [rows, hc, ↓reduceDIte]

theorem row_new (q : Controller D k) (d : D.below (D.cell q.1)) :
    (rows F weight hvis).E q.1 d = min (master F weight q d.1) (weight q) := by
  simp only [rows, q.2, ↓reduceDIte]

theorem old_respects_iff {c : Cell D} (hc : D.cell c ≠ (A, k))
    {r : D.below (D.cell c) → ExtOrd} :
    RespectsSemanticsBelow (rows F weight hvis) (D.cell c) r ↔
      RespectsSemanticsBelow F.base (D.cell c) r := by
  constructor <;> intro hr <;> refine ⟨hr.orderly, ?_, hr.availability⟩
  · intro d
    simpa only [row_old F weight hvis (F.below_old hc d)] using hr.locality d
  · intro d
    rw [row_old F weight hvis (F.below_old hc d)]
    exact hr.locality d

theorem master_locality (q p : Controller D k) :
    TransformsTo (fun d : D.below (D.cell p.1) => D.grade d.1)
      ((rows F weight hvis).E p.1)
      (fun d => min (master F weight q d.1) (master F weight q p.1)) := by
  have hb (d : D.below (D.cell p.1)) : D.grade d.1 ≤ k := by
    simpa only [CellScheme.grade, p.2] using d.2.2
  have ht := (TransformsTo.refl
    (grade := fun d : D.below (D.cell p.1) => D.grade d.1)
    ((rows F weight hvis).E p.1)).cap
    hb (F.grid_visible _ (cut_mem F.bot_mem (F.boundary q) (F.boundary p)))
  have he : (fun d : D.below (D.cell p.1) =>
      min ((rows F weight hvis).E p.1 d) (cut F.grid (F.boundary q) (F.boundary p))) =
      (fun d => min (master F weight q d.1) (master F weight q p.1)) := by
    funext d
    rw [row_new, master_new, min_right_comm,
      ← master_agreement F weight q p d.1 (hb d)]
    exact min_assoc _ _ _
  rwa [he] at ht

variable (hbound : ∀ q, weight q ≤ F.ceiling)

include hbound in
theorem diagonal (q : Controller D k) :
    (rows F weight hvis).E q.1 ⟨q.1, GradedLe.refl _⟩ = weight q := by
  simp only [rows, q.2, ↓reduceDIte]
  rw [master_new, cut_refl F.ceiling_mem F.grid_bound,
    min_eq_right (hbound q), min_self]

include hbound in
theorem parent_read (q p : Controller D k)
    (hp : F.boundary p = F.boundary q) (hw : weight p = F.ceiling) :
    (rows F weight hvis).E q.1 ⟨p.1, by rw [p.2, q.2]; exact GradedLe.refl _⟩ =
      weight q := by
  simp only [rows, q.2, ↓reduceDIte]
  rw [master_new, hp, hw, cut_refl F.ceiling_mem F.grid_bound, min_self,
    min_eq_right (hbound q)]

include hbound in
/-- Actual locality promotes a top weighted node to its ceiling leaf; this is
about arbitrary lawful sections, not selected source displays. -/
theorem le_parent {BJ : Finset ι × ℕ} (hBJ : GradedLe (A, k) BJ)
    {v : D.below BJ → ExtOrd} (hv : RespectsSemanticsBelow (rows F weight hvis) BJ v)
    (q p : Controller D k) (hp : F.boundary p = F.boundary q)
    (hw : weight p = F.ceiling) :
    v ⟨q.1, q.2.symm ▸ hBJ⟩ ≤ v ⟨p.1, p.2.symm ▸ hBJ⟩ := by
  let c : D.below BJ := ⟨q.1, q.2.symm ▸ hBJ⟩
  let self : D.below (D.cell q.1) := ⟨q.1, GradedLe.refl _⟩
  let parent : D.below (D.cell q.1) :=
    ⟨p.1, by rw [p.2, q.2]; exact GradedLe.refl _⟩
  have he : (rows F weight hvis).E q.1 parent = (rows F weight hvis).E q.1 self :=
    (parent_read F weight hvis hbound q p hp hw).trans
      (diagonal F weight hvis hbound q).symm
  obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hv.locality c
  have ha := hr parent
  have hb := hr self
  have hg : D.grade p.1 = D.grade q.1 :=
    (congrArg Prod.snd p.2).trans (congrArg Prod.snd q.2).symm
  change min (v ⟨p.1, p.2.symm ▸ hBJ⟩) (v c) =
    min (σ ((rows F weight hvis).E q.1 parent)) (g (D.grade p.1)) at ha
  change min (v c) (v c) =
    min (σ ((rows F weight hvis).E q.1 self)) (g (D.grade q.1)) at hb
  rw [he, hg, ← hb, min_self] at ha
  exact min_eq_right_iff.mp ha

include hvis in
/-- Weighted columns introduce no unhosted orbit: below a common cut a field
node's weight is represented by this source's own field vector. -/
theorem master_supported
    (hkind : ∀ p, weight p = F.ceiling ∨ ∃ x, weight p = F.boundary p x)
    (hlower : ∀ q d, D.grade d ≤ k → D.cell d ≠ (A, k) →
      OrbitPrefixSupport.Supported k (F.grid : Set ExtOrd) (F.boundary q) (F.lower q d))
    (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    OrbitPrefixSupport.Supported k (F.grid : Set ExtOrd) (F.boundary q)
      (master F weight q d) := by
  by_cases he : D.cell d = (A, k)
  · let p : Controller D k := ⟨d, he⟩
    change OrbitPrefixSupport.Supported k (F.grid : Set ExtOrd) (F.boundary q)
      (master F weight q p.1)
    rw [master_new]
    by_cases hc : cut F.grid (F.boundary q) (F.boundary p) ≤ weight p
    · rw [min_eq_left hc]
      exact Or.inr (Or.inl (cut_mem F.bot_mem _ _))
    · have hc' := lt_of_not_ge hc
      rw [min_eq_right hc'.le]
      rcases hkind p with hw | ⟨x, hw⟩
      · exact False.elim (hc ((cut_le F.grid_bound _ _).trans_eq hw.symm))
      · have ha := agree_cut F.bot_mem (F.boundary q) (F.boundary p) x
        rw [← hw, min_eq_left hc'.le] at ha
        have hx : F.boundary q x = weight p := by
          by_cases hb : F.boundary q x ≤ cut F.grid (F.boundary q) (F.boundary p)
          · rwa [min_eq_left hb] at ha
          · rw [min_eq_right (le_of_not_ge hb)] at ha
            exact False.elim (ne_of_lt hc' ha.symm)
        exact Or.inr (Or.inr ⟨x, 0, Nat.zero_le _, by
          rw [hx]; exact (evr_eq_self_of_selfVis (hvis p) 0).symm⟩)
  · rw [master_old F weight q he]
    exact hlower q d hd he

/-- A ceiling leaf with the same source supplies availability even for zero nodes. -/
theorem master_respects
    (hleaf : ∀ q, ∃ p, F.boundary p = F.boundary q ∧ weight p = F.ceiling)
    (q : Controller D k) :
    RespectsSemanticsBelow (rows F weight hvis) (A, k)
      (fun d => master F weight q d.1) where
  orderly d := (master_visible F weight hvis q d.1 d.2.2).symm
  locality c := by
    by_cases hc : D.cell c.1 = (A, k)
    · exact master_locality F weight hvis q ⟨c.1, hc⟩
    · have ht := (F.lower_lawful q c.1 c.2.2 hc).locality ⟨c.1, GradedLe.refl _⟩
      simpa only [row_old F weight hvis hc, master_old F weight q hc,
        master_old F weight q (F.below_old hc _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    by_cases ht : D.cell t.1 = (A, k)
    · obtain ⟨p, hp, hw⟩ := hleaf q
      refine ⟨⟨p.1, by rw [p.2]; exact GradedLe.refl _⟩, p.2.trans ht.symm, ?_⟩
      rw [master_new, hp, hw, cut_refl F.ceiling_mem F.grid_bound, min_self]
      exact master_bound F weight q c.1 c.2.2
    · have hc : GradedLe (D.cell c.1) (D.cell t.1) := ⟨hs, hg.le⟩
      obtain ⟨w, hw, hle⟩ := (F.lower_lawful q t.1 t.2.2 ht).availability
        ⟨c.1, hc⟩ ⟨t.1, GradedLe.refl _⟩ hs hg
      refine ⟨⟨w.1, w.2.trans t.2⟩, hw, ?_⟩
      simpa only [master_old F weight q (F.below_old ht ⟨c.1, hc⟩),
        master_old F weight q (F.below_old ht w)] using hle

theorem consistent
    (hleaf : ∀ q, ∃ p, F.boundary p = F.boundary q ∧ weight p = F.ceiling)
    (hbase : ∀ c : Cell D, D.cell c ≠ (A, k) →
      RespectsSemanticsBelow F.base (D.cell c) (F.base.E c)) :
    (rows F weight hvis).IsConsistent := by
  intro c
  by_cases hc : D.cell c = (A, k)
  · have hr := (master_respects F weight hvis hleaf ⟨c, hc⟩).cap (hvis ⟨c, hc⟩)
    have ht := GradeCutLayerRows.cast_respects D (rows F weight hvis) hc.symm hr
    convert ht using 1
    exact funext (row_new F weight hvis ⟨c, hc⟩)
  · rw [row_old F weight hvis hc]
    exact (old_respects_iff F weight hvis hc).mpr (hbase c hc)

end
end VaughtConjecture.Knight.WeightedSourcePrefixLayer

namespace VaughtConjecture.Knight.SharpWitnessComposition
open Transform Value ExtOrd

theorem map_respects_of_short_or_reflecting {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : Witness (gTop K) ν)
    (hc : ∀ c : D.below BJ,
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1),
        ν (r (CellScheme.below.incl c d)) = ⊥ ↔ r (CellScheme.below.incl c d) = ⊥)) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) :=
  map_respects_of_short_or_local hr hK hν fun c => (hc c).imp id fun hb =>
    ((map_respects_iff_rowBlockBottom (hr.mono c.2)
      (fun d => d.2.2.trans (hK c)) (boundedMap_of_witness hν)).mpr
      (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects (hr.mono c.2)) hb)).locality
      ⟨c.1, GradedLe.refl _⟩
end VaughtConjecture.Knight.SharpWitnessComposition

namespace VaughtConjecture.Knight.NativePrivateFace
open Transform Value ExtOrd CappedDonor
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A S : Finset ι} {D : CellScheme A}
  {N : ℕ} (C : SemScheme N) (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
  {sem : Semantics D}
  (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) sem)

def fullEquiv : C.scheme.below (effC N N) ≃ D.below (S, N) :=
  Equiv.ofBijective
    (fun d => ⟨E.map d.1, (E.index d.1).symm ▸
      ⟨hS ▸ Finset.image_subset_image (Finset.subset_univ _), gradeC_le d.1⟩⟩)
    ⟨fun _ _ he => Subtype.ext (E.map.injective (congrArg Subtype.val he)), fun d => by
      obtain ⟨c, hc⟩ := E.exhaustive d.1 d.2.1
      exact ⟨⟨c, Finset.subset_univ _, le_min (gradeC_le c) (gradeC_le c)⟩, Subtype.ext hc⟩⟩

theorem fullEquiv_grade (d : C.scheme.below (effC N N)) :
    D.grade (fullEquiv C place hS E d).1 = C.scheme.grade d.1 :=
  congrArg Prod.snd (E.index d.1)

theorem respects_iff (p : D.below (S, N) → ExtOrd) :
    RespectsSemanticsBelow sem (S, N) p ↔
      RespectsSemanticsBelow C.rows (effC N N) (p ∘ fullEquiv C place hS E) := by
  have h := respects_iff_of_equiv (sem' := C.rows) (sem := sem)
    (fullEquiv C place hS E) (fun d => (fullEquiv_grade C place hS E d).symm)
    (fun d e => by
      change C.scheme.scope d.1 ⊆ C.scheme.scope e.1 ↔ (D.cell (E.map d.1)).1 ⊆ (D.cell (E.map e.1)).1
      rw [show (D.cell (E.map d.1)).1 = (C.scheme.scope d.1).image place from congrArg Prod.fst (E.index d.1),
        show (D.cell (E.map e.1)).1 = (C.scheme.scope e.1).image place from congrArg Prod.fst (E.index e.1),
        Finset.image_subset_image_iff place.injective])
    (fun c d _ => ((E.row c.1 (PointImageSemantics.belowEquiv C.scheme place hS c.1 d)).trans
      (PointImageSemantics.row C.scheme place hS C.rows c.1 d)).symm)
    (p ∘ fullEquiv C place hS E)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm
end
end VaughtConjecture.Knight.NativePrivateFace

namespace VaughtConjecture.Knight.FinalGateLayer
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
open SharpWitnessComposition CoatomBoundaryExtension AmalgamationPlan
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
  {A : Finset ι} {D : CellScheme A} {N : ℕ}

structure Input (D : CellScheme A) (N : ℕ) (X Q : Type*) where
  sem : Semantics D
  positive : 0 < N
  height : N ≤ A.card
  separated : ∀ d : Cell D, ¬ GradedLe (A, N) (D.cell d)
  fields : Q → X → ExtOrd
  gate : X
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis N h
  lower : Q → Cell D → ExtOrd
  lower_lawful : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1)
  lower_bound : ∀ a d, D.grade d ≤ N → lower a d ≤ ceiling
  lower_prefix : ∀ a b h, h ∈ grid → Agree (fields a) (fields b) h →
    ∀ d, D.grade d ≤ N → min (lower a d) h = min (lower b d) h
  gate_visible : ∀ a, SelfVis N (fields a gate)
  gate_bound : ∀ a, fields a gate ≤ ceiling

namespace Input
variable (I : Input D N X Q)

abbrev Node := Q × Bool
abbrev carrier := SourceLayerCarrier.scheme D (Node (Q := Q)) N I.positive I.height
abbrev old (d : Cell D) : Cell I.carrier :=
  SourceLayerCarrier.toCell D (Node (Q := Q)) N I.positive I.height (.inl d)
abbrev added (a : Q) (marked : Bool) : Cell I.carrier :=
  SourceLayerCarrier.toCell D (Node (Q := Q)) N I.positive I.height (.inr (a, marked))
abbrev controller := SeparatedSourceLayerCarrier.controller D (Node (Q := Q)) N I.positive I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv D (Node (Q := Q))
  N I.positive I.height I.separated).symm

@[simp] theorem member_controller (a : Q) (marked : Bool) :
    I.member (I.controller (a, marked)) = (a, marked) := Equiv.symm_apply_apply _ _
@[simp] theorem old_index (d : Cell D) : I.carrier.cell (I.old d) = D.cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _
@[simp] theorem added_index (a : Q) (marked : Bool) :
    I.carrier.cell (I.added a marked) = (A, N) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem old_strictMono : StrictMono I.old :=
  SourceLayerCarrier.old_order D (Node (Q := Q)) N I.positive I.height

theorem proper_occurrence {S : Finset ι} {k : ℕ} (hS : S ⊆ A) (hne : S ≠ A)
    (d : I.carrier.below (S, k)) : ∃ x : D.below (S, k), d.1 = I.old x.1 := by
  obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height d.1
    fun he => hne (Finset.Subset.antisymm hS (he ▸ d.2).1)
  exact ⟨⟨x, by simpa only [hx, I.old_index] using d.2⟩, hx⟩

def lowerVector (a : Q) (d : Cell I.carrier) : ExtOrd :=
  match SourceLayerCarrier.toOcc D (Node (Q := Q)) N I.positive I.height d with
  | .inl x => I.lower a x
  | .inr _ => ⊥

theorem lowerVector_old (a : Q) (d : Cell D) : I.lowerVector a (I.old d) = I.lower a d := by
  simp only [lowerVector, old, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data I.carrier N X where
  base := SeparatedSourceLayerCarrier.base D (Node (Q := Q)) N I.positive I.height I.separated I.sem
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height c hc
    rw [SourceLayerCarrier.cell_toCell]; exact I.separated x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.fields (I.member q).1
  lower q := I.lowerVector (I.member q).1
  lower_bound q d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height d hd
    rw [lowerVector_old]; exact I.lower_bound _ x (by simpa only [CellScheme.grade, old_index] using hg)
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height c hc
    apply (SeparatedSourceLayerCarrier.base_respects_iff D (Node (Q := Q)) N
      I.positive I.height I.separated I.sem x _).mpr
    have hx : GradedLe (D.cell x) (A, N) :=
      ⟨D.isPlan.subset_of_mem (D.scope_mem_plan x),
        by simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lowerVector_old, CellScheme.below.mono] using (I.lower_lawful _).mono hx
  grid_agreement p q h hh hag d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height d hd
    simpa only [lowerVector_old] using I.lower_prefix _ _ h hh hag x
      (by simpa only [CellScheme.grade, old_index] using hg)

def nodeWeight (v : Node (Q := Q)) : ExtOrd := if v.2 then I.fields v.1 I.gate else I.ceiling
def weight (q : Controller I.carrier N) : ExtOrd := I.nodeWeight (I.member q)

theorem weight_visible (q : Controller I.carrier N) : SelfVis N (I.weight q) := by
  unfold weight nodeWeight; split; exact I.gate_visible _; exact I.grid_visible _ I.ceiling_mem

theorem weight_bound (q : Controller I.carrier N) : I.weight q ≤ I.ceiling := by
  unfold weight nodeWeight; split; exact I.gate_bound _; exact le_rfl

theorem weight_kind (q : Controller I.carrier N) :
    I.weight q = I.data.ceiling ∨ ∃ x, I.weight q = I.data.boundary q x := by
  unfold weight nodeWeight; split; exact Or.inr ⟨I.gate, rfl⟩; exact Or.inl rfl

theorem parent (q : Controller I.carrier N) :
    ∃ p, I.data.boundary p = I.data.boundary q ∧ I.weight p = I.data.ceiling :=
  ⟨I.controller ((I.member q).1, false),
    by change I.fields (I.member (I.controller _)).1 = _; rw [member_controller]; rfl,
    by simp only [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]; rfl⟩

abbrev rows := WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible
abbrev source (a : Q) := WeightedSourcePrefixLayer.master I.data I.weight (I.controller (a, false))

theorem source_lawful (a : Q) : RespectsSemanticsBelow I.rows (A, N) (fun d => I.source a d.1) :=
  WeightedSourcePrefixLayer.master_respects I.data I.weight I.weight_visible I.parent _

theorem source_old (a : Q) (d : Cell D) : I.source a (I.old d) = I.lower a d := by
  rw [source, WeightedSourcePrefixLayer.master_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated d)]
  change I.lowerVector (I.member (I.controller (a, false))).1 (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_added (a b : Q) (marked : Bool) :
    I.source a (I.added b marked) =
      min (cut I.grid (I.fields a) (I.fields b)) (I.nodeWeight (b, marked)) := by
  rw [source, show I.added b marked = (I.controller (b, marked)).1 from rfl,
    WeightedSourcePrefixLayer.master_new]
  simp only [data, weight, member_controller]

theorem source_marked (a b : Q) : I.source a (I.added b true) =
    min (I.fields a I.gate) (cut I.grid (I.fields a) (I.fields b)) := by
  rw [source_added]
  change min (cut I.grid (I.fields a) (I.fields b)) (I.fields b I.gate) = _
  rw [min_comm]; exact (agree_cut I.bot_mem _ _ I.gate).symm

theorem source_marked_le (a b : Q) : I.source a (I.added b true) ≤ I.fields a I.gate := by
  rw [source_marked]; exact min_le_left _ _

theorem source_own_marked (a : Q) : I.source a (I.added a true) = I.fields a I.gate := by
  rw [source_marked, cut_refl I.ceiling_mem I.grid_bound, min_eq_left (I.gate_bound a)]

theorem source_bound (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    I.source a d ≤ I.ceiling := WeightedSourcePrefixLayer.master_bound I.data I.weight _ d hd

theorem leaf_row (a : Q) (d : I.carrier.below (I.carrier.cell (I.added a false))) :
    I.rows.E (I.added a false) d = I.source a d.1 := by
  have hw : I.weight (I.controller (a, false)) = I.ceiling := by
    simp only [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]
  exact (WeightedSourcePrefixLayer.row_new I.data I.weight I.weight_visible
    (I.controller (a, false)) d).trans (by
      rw [hw, min_eq_left]
      exact I.source_bound a d.1 (by simpa only [CellScheme.grade, added_index] using d.2.2))

theorem source_supported
    (hlower : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.source a d) := by
  have h := WeightedSourcePrefixLayer.master_supported I.data I.weight I.weight_visible
    I.weight_kind (fun q d hg hn => by
      obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height d hn
      change OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd)
        (I.fields (I.member q).1) (I.lowerVector _ (I.old x))
      rw [lowerVector_old]
      exact hlower _ x (by simpa only [CellScheme.grade, old_index] using hg))
    (I.controller (a, false)) d hd
  simpa only [source, data, member_controller] using h

theorem source_prefix (a b : Q) {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.fields a) (I.fields b) h) :
    Agree (fun d : I.carrier.below (A, N) => I.source a d.1)
      (fun d => I.source b d.1) h := by
  apply WeightedSourcePrefixLayer.master_prefix I.data I.weight hh
  simpa only [data, member_controller] using hag

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    I.rows.E (I.old c) (SeparatedSourceLayerCarrier.ownerEquiv D (Node (Q := Q))
      N I.positive I.height I.separated c d) = I.sem.E c d := by
  rw [WeightedSourcePrefixLayer.row_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ I.separated _ c d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent := by
  apply WeightedSourcePrefixLayer.consistent I.data I.weight I.weight_visible I.parent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N I.positive I.height c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff D (Node (Q := Q)) N
    I.positive I.height I.separated I.sem x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using hs x

theorem decode_source_prefix
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (a b : Q) {h : ExtOrd} (hh : h ∈ I.grid) (hpos : h ≠ ⊥)
    (hag : Agree (I.fields b) (I.fields a) h)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop N) ν) (hreach : h ≤ ν h)
    (hgrid : ∀ z ∈ I.grid, z < h → ν z = z)
    (hfields : ∀ x, I.fields a x < h → ν (I.fields a x) = I.fields a x) :
    RespectsSemanticsBelow I.rows (A, N) (fun d => ν (I.source b d.1)) ∧
      ∀ d : I.carrier.below (A, N),
        min (ν (I.source b d.1)) h = min (I.source a d.1) h :=
  OrbitPrefixSupport.decode_respects_of_positive_cut hν
    (I.source_lawful a) (I.source_lawful b) (fun d => d.2.2)
    (I.grid_visible h hh) hpos hreach hgrid hfields
    (fun d => I.source_supported hsupport a d.1 d.2.2) (I.source_prefix b a hh hag)

theorem source_short
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (hfields : ∀ a x, Short N (I.fields a x))
    (hgrid : ∀ z ∈ I.grid, Short N z)
    (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    Short N (I.source a d) := by
  rcases I.source_supported hsupport a d hd with hz | hg | ⟨x, i, hi, he⟩
  · exact Or.inl hz
  · exact hgrid _ hg
  · rw [he]; exact PrivateRowFactorization.short_replace (hfields a x) le_rfl hi

theorem decoded_respects
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (hfields : ∀ a x, Short N (I.fields a x))
    (hgrid : ∀ z ∈ I.grid, Short N z)
    (a : Q) {ν : ExtOrd → ExtOrd} (hν : Witness (gTop N) ν)
    (hlower : RespectsSemanticsBelow I.sem (A, N) (fun d => ν (I.lower a d.1))) :
    RespectsSemanticsBelow I.rows (A, N) (fun d => ν (I.source a d.1)) := by
  have hr := I.source_lawful a
  refine ⟨fun d => ?_, fun c => ?_, fun c t hs hg => ?_⟩
  · have hh := hν.clause5 (I.source a d.1) (I.carrier.grade d.1)
      (by rw [gTop_of_le (show I.carrier.grade d.1 ≤ N from d.2.2)]; exact le_top)
      (I.carrier.grade d.1) le_rfl
    rwa [← hr.orderly d] at hh
  · by_cases hc : I.carrier.cell c.1 = (A, N)
    · apply map_capped_locality
        (X := I.carrier.below (I.carrier.cell c.1))
        (c := (⟨c.1, GradedLe.refl _⟩ : I.carrier.below (I.carrier.cell c.1)))
        (grade := fun d => I.carrier.grade d.1) (E := I.rows.E c.1)
        (p := fun d => I.source a (CellScheme.below.incl c d).1)
        (fun d => d.2.2) c.2.2 _ (hr.orderly c).symm (hr.locality c) hν
      intro d
      change Short (I.carrier.cell c.1).2 (I.rows.E c.1 d)
      rw [hc]
      let q : Controller I.carrier N := ⟨c.1, hc⟩
      change Short N (I.rows.E q.1 d)
      rw [WeightedSourcePrefixLayer.row_new]
      have hm : WeightedSourcePrefixLayer.master I.data I.weight q d.1 =
          I.source (I.member q).1 d.1 := by
        unfold source WeightedSourcePrefixLayer.master ScopedSourcePrefixLayer.Data.profile
        simp only [data, member_controller]
      rw [hm]
      have hs := I.source_short hsupport hfields hgrid (I.member q).1 d.1
        (d.2.2.trans (congrArg Prod.snd hc).le)
      rcases le_total (I.source (I.member q).1 d.1) (I.weight q) with h | h
      · rwa [min_eq_left h]
      · rw [min_eq_right h]
        rcases I.weight_kind q with hw | ⟨x, hw⟩
        · rw [hw]; exact hgrid _ I.ceiling_mem
        · rw [hw]; exact hfields (I.member q).1 x
    · obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
        I.positive I.height c.1 hc
      have hxc : GradedLe (D.cell x) (A, N) := by simpa only [hx, I.old_index] using c.2
      have ho : RespectsSemanticsBelow I.rows (I.carrier.cell (I.old x))
          (fun d => ν (I.source a d.1)) := by
        apply (WeightedSourcePrefixLayer.old_respects_iff I.data I.weight I.weight_visible
          (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated x)).mpr
        apply (SeparatedSourceLayerCarrier.base_respects_iff D (Node (Q := Q)) N
          I.positive I.height I.separated I.sem x _).mpr
        simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
          I.source_old, CellScheme.below.mono] using hlower.mono hxc
      rcases c with ⟨c, _⟩; dsimp only at hx; subst c
      exact ho.locality ⟨I.old x, GradedLe.refl _⟩
  · obtain ⟨w, hw, hle⟩ := hr.availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩

abbrev addedAt (a : Q) (marked : Bool) : I.carrier.below (A, N) :=
  ⟨I.added a marked, by rw [I.added_index]; exact GradedLe.refl _⟩

theorem exists_serving_chart {v : I.carrier.below (A, N) → ExtOrd}
    (hv : RespectsSemanticsBelow I.rows (A, N) v)
    (c : I.carrier.below (A, N)) (hc : I.carrier.grade c.1 = N) (seed : Q) :
    ∃ a : Q, v c ≤ v (I.addedAt a false) ∧
      ∃ τ : ExtOrd → ExtOrd, Witness (gTop N) τ ∧
        (∀ x, τ x ≤ v (I.addedAt a false)) ∧
        ∀ d : I.carrier.below (A, N),
          τ (I.source a d.1) = min (v d) (v (I.addedAt a false)) := by
  obtain ⟨e, he, hce⟩ := hv.availability c (I.addedAt seed false)
    (by simpa only [CellScheme.scope, addedAt, I.added_index] using c.2.1)
    (by simpa only [CellScheme.grade, addedAt, I.added_index] using hc)
  let q : Controller I.carrier N := ⟨e.1, he.trans (I.added_index seed false)⟩
  rcases hm : I.member q with ⟨a, marked⟩
  have heq : e = I.addedAt a marked := by
    apply Subtype.ext
    have hh := (congrArg Subtype.val
      ((SeparatedSourceLayerCarrier.controllerEquiv D (Node (Q := Q)) N
        I.positive I.height I.separated).apply_symm_apply q)).symm
    change e.1 = I.added (I.member q).1 (I.member q).2 at hh
    simpa only [hm] using hh
  have hnle : v (I.addedAt a marked) ≤ v (I.addedAt a false) := by
    apply WeightedSourcePrefixLayer.le_parent I.data I.weight I.weight_visible I.weight_bound
      (GradedLe.refl _) hv (I.controller (a, marked)) (I.controller (a, false))
    · change I.fields (I.member (I.controller (a, false))).1 =
        I.fields (I.member (I.controller (a, marked))).1
      rw [I.member_controller, I.member_controller]
    · simp only [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]; rfl
  let c₀ := I.addedAt a false
  have hv' : SelfVis (I.carrier.grade c₀.1) (v c₀) := (hv.orderly c₀).symm
  have hg : I.carrier.grade c₀.1 = N := congrArg Prod.snd (I.added_index a false)
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := (⟨c₀.1, GradedLe.refl _⟩ : I.carrier.below (I.carrier.cell c₀.1)))
    (p := fun d => v (CellScheme.below.incl c₀ d))
    (fun d => d.2.2) hv' (hv.locality c₀)
  refine ⟨a, hce.trans (heq ▸ hnle), τ, hg ▸ hτ, hb, fun d => ?_⟩
  let e' : I.carrier.below (I.carrier.cell (I.added a false)) :=
    ⟨d.1, by rw [I.added_index]; exact d.2⟩
  exact (congrArg τ (I.leaf_row a e')).symm.trans (hr e')

theorem exists_active_chart {v : I.carrier.below (A, N) → ExtOrd}
    (hv : RespectsSemanticsBelow I.rows (A, N) v)
    (c : I.carrier.below (A, N)) (hc : I.carrier.grade c.1 = N)
    (hpos : v c ≠ ⊥) (b : Q) (hz : v (I.addedAt b true) ≠ ⊥) :
    ∃ a : Q, v c ≤ v (I.addedAt a false) ∧ I.fields a I.gate ≠ ⊥ ∧
      ∃ τ : ExtOrd → ExtOrd, Witness (gTop N) τ ∧
        (∀ x, τ x ≤ v (I.addedAt a false)) ∧
        ∀ d : I.carrier.below (A, N),
          τ (I.source a d.1) = min (v d) (v (I.addedAt a false)) := by
  obtain ⟨a, hca, τ, hτ, hb, hr⟩ := I.exists_serving_chart hv c hc b
  have hh : v (I.addedAt a false) ≠ ⊥ := fun he => hpos (le_bot_iff.mp (hca.trans_eq he))
  refine ⟨a, hca, fun hzero => ?_, τ, hτ, hb, hr⟩
  have hs : I.source a (I.added b true) = ⊥ :=
    le_bot_iff.mp ((I.source_marked_le a b).trans_eq hzero)
  have he := hr (I.addedAt b true)
  rw [show I.source a (I.addedAt b true).1 = ⊥ from hs, hτ.bot] at he
  exact (min_ne_bot hz hh) he.symm

theorem exists_cap_chart {v : I.carrier.below (A, N) → ExtOrd}
    (hv : RespectsSemanticsBelow I.rows (A, N) v)
    (c : I.carrier.below (A, N)) (hc : I.carrier.grade c.1 = N) (seed : Q)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hreach : γ ≤ v c) :
    ∃ a τ, Witness (gTop N) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ d : I.carrier.below (A, N), τ (I.source a d.1) = min (v d) γ := by
  obtain ⟨a, hca, τ, hτ, -, hr⟩ := I.exists_serving_chart hv c hc seed
  exact ⟨a, fun x => min (τ x) γ, FreeDiagonal.clip_witness hτ hγ, fun _ => min_le_right _ _,
    fun d => (congrArg (fun x => min x γ) (hr d)).trans
      (by rw [min_assoc, min_eq_right (hreach.trans hca)])⟩

def inheritedBelow (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, N) J) :
    D.below J ≃ I.carrier.below J :=
  Equiv.ofBijective (fun d => ⟨I.old d.1, by rw [I.old_index]; exact d.2⟩)
    ⟨fun _ _ he => Subtype.ext (I.old_strictMono.injective (congrArg Subtype.val he)), fun d => by
      obtain ⟨e, he⟩ := SourceLayerCarrier.old_occurrence D (Node (Q := Q)) N
        I.positive I.height d.1 fun he => hJ (he ▸ d.2)
      exact ⟨⟨e, by simpa only [he, I.old_index] using d.2⟩, Subtype.ext he.symm⟩⟩

theorem inheritedBelow_respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, N) J)
    (p : I.carrier.below J → ExtOrd) :
    RespectsSemanticsBelow I.rows J p ↔
      RespectsSemanticsBelow I.sem J (p ∘ I.inheritedBelow J hJ) := by
  have h := respects_iff_of_equiv (sem' := I.sem) (sem := I.rows)
    (I.inheritedBelow J hJ) (fun d => (congrArg Prod.snd (I.old_index d.1)).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔ (I.carrier.cell (I.old d.1)).1 ⊆ (I.carrier.cell (I.old e.1)).1
      rw [I.old_index, I.old_index]; rfl)
    (fun c d _ => (I.inherited_row c.1 d).symm) (p ∘ I.inheritedBelow J hJ)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

theorem inherited_lift {I₀ J : Finset ι × ℕ} (h : GradedLe I₀ J)
    (hJ : ¬ GradedLe (A, N) J) (hlift : CappedLift I.sem h) : CappedLift I.rows h := by
  let hI : ¬ GradedLe (A, N) I₀ := fun he => hJ (he.trans h)
  let eI := I.inheritedBelow I₀ hI
  let eJ := I.inheritedBelow J hJ
  have hm (d : D.below I₀) : eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hcaps, hread⟩ := hlift (p ∘ eI) (q ∘ eJ) γ
    ((I.inheritedBelow_respects_iff I₀ hI p).mp hp)
    ((I.inheritedBelow_respects_iff J hJ q).mp hq) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (I.inheritedBelow_respects_iff J hJ _).mpr ?_,
    fun d => by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcaps (eJ.symm d),
    fun d => ?_⟩
  · have he : (r ∘ eJ.symm) ∘ eJ = r := funext fun x => by simp [Equiv.symm_apply_apply]
    exact he.symm ▸ hr
  · have he : eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) :=
      eJ.injective (by rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply])
    rw [Function.comp_apply, he, hread]
    exact congrArg p (eI.apply_symm_apply d)

theorem restore {S : Finset ι} (hS : S ⊆ A)
    (hlift : CappedLift I.sem (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p : I.carrier.below (S, N) → ExtOrd} (hp : RespectsSemanticsBelow I.rows (S, N) p)
    {u : I.carrier.below (A, N) → ExtOrd} (hu : RespectsSemanticsBelow I.rows (A, N) u)
    {M : ExtOrd} (hM : SelfVis N M)
    (hread : ∀ e, u (CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) =
      min (p e) M)
    (hhigh : ∀ e : I.carrier.below (S, N), I.carrier.grade e.1 = N → p e ≤ M) :
    ∃ r : I.carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow I.rows (A, N) r ∧
      (∀ e, r (CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e) ∧
      (∀ d, min (r d) M = min (u d) M) ∧
      ∀ d, N - 1 < I.carrier.grade d.1 → r d ≤ M := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt I.positive)
  exact SingleFaceTailRestoration.exists_restore I.rows hS
    (I.inherited_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩)
      (fun he => not_le_of_gt (Nat.lt_succ_self j) he.2) hlift) hp hu hM hread hhigh

theorem lift_inactive {S : Finset ι} (hS : S ⊆ A)
    (hlift : CappedLift I.sem (show GradedLe (S, N - 1) (A, N - 1) from ⟨hS, le_rfl⟩))
    {p : I.carrier.below (S, N) → ExtOrd} (hp : RespectsSemanticsBelow I.rows (S, N) p)
    {q : I.carrier.below (A, N) → ExtOrd} (hq : RespectsSemanticsBelow I.rows (A, N) q)
    {γ : ExtOrd} (hγ : SelfVis N γ)
    (hag : ∀ e, min (q (CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e)) γ =
      min (p e) γ)
    (hhigh : ∀ e : I.carrier.below (S, N), I.carrier.grade e.1 = N → p e ≤ γ) :
    ∃ r : I.carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow I.rows (A, N) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ e, r (CellScheme.below.mono (show GradedLe (S, N) (A, N) from ⟨hS, le_rfl⟩) e) = p e := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt I.positive)
  exact SingleFaceTailRestoration.exists_inactive I.rows hS
    (I.inherited_lift (show GradedLe (S, j) (A, j) from ⟨hS, le_rfl⟩)
      (fun he => not_le_of_gt (Nat.lt_succ_self j) he.2) hlift) hp hq hγ hag hhigh

def inheritedFace {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : S ⊆ A) (hne : S ≠ A) (E : ExactSemanticFace sem₀ I.sem) :
    ExactSemanticFace sem₀ I.rows where
  map := ⟨I.old ∘ E.map, I.old_strictMono.injective.comp E.map.injective⟩
  index d := (I.old_index (E.map d)).trans (E.index d)
  exhaustive z hz := by
    obtain ⟨d, hd⟩ := I.proper_occurrence hS hne
      (⟨z, hz, le_rfl⟩ : I.carrier.below (S, I.carrier.grade z))
    obtain ⟨e, he⟩ := E.exhaustive d.1 d.2.1
    exact ⟨e, (congrArg I.old he).trans hd.symm⟩
  row c d := (I.inherited_row (E.map c) (E.belowMap c d)).trans (E.row c d)

theorem grade_bound (hD : ∀ d : Cell D, D.grade d ≤ N) (d : Cell I.carrier) :
    I.carrier.grade d ≤ N := by
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration D (Node (Q := Q)) N
    I.positive I.height).surjective d
  change (I.carrier.cell (SourceLayerCarrier.toCell D (Node (Q := Q)) N I.positive I.height x)).2 ≤ N
  rw [SourceLayerCarrier.cell_toCell]
  cases x with
  | inl c => exact hD c
  | inr _ => exact le_rfl

theorem coded (hc : I.sem.IsCoded)
    (hfields : ∀ a f, IsCodedLabel N (I.fields a f))
    (hgrid : ∀ z ∈ I.grid, IsCodedLabel N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d)) :
    I.rows.IsCoded := by
  apply CanonicalCodingSupport.layer D (Node (Q := Q)) N I.positive I.height I.separated
    I.sem I.rows hc I.inherited_row
  rintro ⟨a, marked⟩ d
  have hm : WeightedSourcePrefixLayer.master I.data I.weight (I.controller (a, marked)) d.1 =
      I.source a d.1 := by
    simp only [source, WeightedSourcePrefixLayer.master, ScopedSourcePrefixLayer.Data.profile,
      data, member_controller]
  have hrow : (WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible).E
      (I.controller (a, marked)).1 d = min (I.source a d.1) (I.nodeWeight (a, marked)) :=
    (WeightedSourcePrefixLayer.row_new I.data I.weight I.weight_visible
      (I.controller (a, marked)) d).trans (by rw [hm]; simp only [weight, member_controller])
  change IsCodedLabel N ((WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible).E
    (I.controller (a, marked)).1 d)
  rw [hrow]
  have hs : IsCodedLabel N (I.source a d.1) := CanonicalCodingSupport.supported
    hgrid (hfields a) (I.source_supported hsupport a d.1
      (by simpa only [CellScheme.grade, I.added_index] using d.2.2))
  have hw : IsCodedLabel N (I.nodeWeight (a, marked)) := by
    unfold nodeWeight; split; exact hfields a I.gate; exact hgrid _ I.ceiling_mem
  rcases le_total (I.source a d.1) (I.nodeWeight (a, marked)) with he | he
  · rwa [min_eq_left he]
  · rwa [min_eq_right he]

theorem complete_through (seed : Q)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N → J ≠ (A, N) → ∃ d, D.cell d = J) :
    ∀ J ∈ Plan.gradedPlan I.carrier.plan, J.2 ≤ N → ∃ d, I.carrier.cell d = J := fun J hJ hJN => by
  by_cases he : J = (A, N)
  · exact ⟨I.added seed false, (I.added_index seed false).trans he.symm⟩
  · obtain ⟨d, hd⟩ := hc J hJ hJN he
    exact ⟨I.old d, (I.old_index d).trans hd⟩
end Input
end
end VaughtConjecture.Knight.FinalGateLayer

namespace VaughtConjecture.Knight.FinalGateApex
open Transform Value ExtOrd AmalgamationPlan
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
  {A : Finset ι} {D : CellScheme A} {N : ℕ}
  (F : FinalGateLayer.Input D N X Q)
  (hD : ∀ d : Cell D, D.grade d ≤ N) (hcard : A.card = N + 1)

abbrev scheme := MaximalFullLayer.scheme F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
abbrev old := MaximalFullLayer.old F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
abbrev rows := MaximalFullLayer.base F.carrier F.rows N (N + 1) (F.grade_bound hD)
  (Nat.lt_succ_self N) hcard.ge
abbrev ownerEquiv := MaximalFullLayer.ownerEquiv F.carrier N (N + 1) (F.grade_bound hD)
  (Nat.lt_succ_self N) hcard.ge

theorem old_index (d : Cell F.carrier) : (scheme F hcard).cell (old F hcard d) =
    F.carrier.cell d := MaximalFullLayer.old_index _ _ _ _ _ _
theorem old_order : StrictMono (old F hcard) := SourceLayerCarrier.old_order _ _ _ _ _
theorem old_row (c : Cell F.carrier) (d : F.carrier.below (F.carrier.cell c)) :
    (rows F hD hcard).E (old F hcard c) (ownerEquiv F hD hcard c d) = F.rows.E c d :=
  MaximalFullLayer.inherited_row _ _ _ _ _ _ _ c d

theorem complete (seed : Q)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N → J ≠ (A, N) → ∃ d, D.cell d = J) :
    (scheme F hcard).IsComplete := by
  refine MaximalFullLayer.complete F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge fun J hJ hne =>
    F.complete_through seed hc J hJ ?_
  obtain ⟨hmem, _, hj⟩ := Plan.mem_gradedPlan.mp hJ
  have hs := F.carrier.isPlan.subset_of_mem hmem
  have hc' := Finset.card_le_card hs
  by_contra hn
  exact hne (Prod.ext (Finset.eq_of_subset_of_card_le hs (by rw [hcard] at hc' ⊢; omega))
    (by rw [hcard] at hc'; omega))

theorem consistent (hc : F.sem.IsConsistent) : (rows F hD hcard).IsConsistent :=
  MaximalFullLayer.consistent _ _ _ _ _ _ _ (F.consistent hc)
theorem coded (hc : F.rows.IsCoded) : (rows F hD hcard).IsCoded :=
  MaximalFullLayer.coded _ _ _ _ _ _ _ hc
theorem bountiful (hb : F.rows.IsBountiful) : (rows F hD hcard).IsBountiful :=
  MaximalFullLayer.bountiful _ _ _ _ _ _ _ F.positive hb

abbrev lowerEquiv : F.carrier.below (A, N) ≃ (scheme F hcard).below (A, N) :=
  HighLayerBountiful.equiv F.carrier Unit (N + 1) (by omega) hcard.ge (A, N)
    fun h => (Nat.not_succ_le_self N) h.2

def display (p : F.carrier.below (A, N) → ExtOrd) : Cell (scheme F hcard) → ExtOrd :=
  CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm)

theorem display_old (p : F.carrier.below (A, N) → ExtOrd) (d : F.carrier.below (A, N)) :
    display F hcard p (old F hcard d.1) = p d := by
  change CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm) ((lowerEquiv F hcard) d).1 = p d
  rw [CellScheme.zeroAbove_low]; exact congrArg p ((lowerEquiv F hcard).symm_apply_apply d)

theorem display_lawful {p : F.carrier.below (A, N) → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows (A, N) p) :
    RespectsSemantics (rows F hD hcard) (display F hcard p) :=
  RespectsSemanticsBelow.zeroAbove ((HighLayerBountiful.respects_iff F.carrier Unit (N + 1)
    (by omega) hcard.ge N (F.grade_bound hD) (Nat.lt_succ_self N) F.rows (rows F hD hcard)
    (old_row F hD hcard) (A, N) (fun h => (Nat.not_succ_le_self N) h.2) p).mp hp)

theorem restrict_lawful {q : Cell (scheme F hcard) → ExtOrd}
    (hq : RespectsSemantics (rows F hD hcard) q) :
    RespectsSemanticsBelow F.rows (A, N) (fun d => q (old F hcard d.1)) :=
  HighLayerBountiful.pullback_respects F.carrier Unit (N + 1) (by omega) hcard.ge N
    (F.grade_bound hD) (Nat.lt_succ_self N) F.rows (rows F hD hcard)
    (old_row F hD hcard) (fun h => (Nat.not_succ_le_self N) h.2) (hq.toBelow (A, N))

def properFace {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : ¬ A ⊆ S) (E : ExactSemanticFace sem₀ F.rows) :
    ExactSemanticFace sem₀ (rows F hD hcard) where
  map := ⟨old F hcard ∘ E.map, (old_order F hcard).injective.comp E.map.injective⟩
  index d := (old_index F hcard _).trans (E.index d)
  exhaustive z hz := by
    obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence F.carrier Unit (N + 1) (by omega) hcard.ge z
      fun he => hS (by change ((scheme F hcard).cell z).1 ⊆ S at hz; simpa only [he] using hz)
    obtain ⟨d, hd⟩ := E.exhaustive x (by
      change ((scheme F hcard).cell z).1 ⊆ S at hz; rwa [hx, old_index] at hz)
    exact ⟨d, (congrArg (old F hcard) hd).trans hx.symm⟩
  row c d := (old_row F hD hcard (E.map c) (E.belowMap c d)).trans (E.row c d)
end
end VaughtConjecture.Knight.FinalGateApex
