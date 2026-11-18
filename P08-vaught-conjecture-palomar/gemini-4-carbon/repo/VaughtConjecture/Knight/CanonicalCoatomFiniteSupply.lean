/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveInput
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections
public import VaughtConjecture.Knight.CanonicalRecursiveCoding
public import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
public import VaughtConjecture.Knight.CanonicalOneCoatom
public import VaughtConjecture.Knight.MaximalFullLayer
public import VaughtConjecture.Knight.Coface

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalCoatomSupply
open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open CoatomBoundaryExtension
noncomputable section

private theorem typeMap_of_pointImage_face {α : Ordinal.{0}} {m n : ℕ}
    (t : S α n) (p : S α m) (f : Fin m ↪ Fin n) {B : Finset (Fin n)}
    (hB : Finset.univ.image f = B)
    (F : ExactSemanticFace (PointImageSemantics.rows p.scheme.scheme f hB p.scheme.rows)
      t.scheme.rows) (hmono : StrictMono F.map)
    (hplan : Plan.restrictPlan t.scheme.scheme.plan B = p.scheme.scheme.plan.image (Finset.image f))
    (hlabel : ∀ d, t.label (F.map d) = p.label d) : typeMap f t = some p := by
  have hv : Finset.univ.image f ∈ t.scheme.scheme.plan := by
    have hh : B ∈ Plan.restrictPlan t.scheme.scheme.plan B := by
      rw [hplan, ← hB]
      exact Finset.mem_image.mpr ⟨_, p.scheme.scheme.isPlan.domain_mem, rfl⟩
    exact hB ▸ (Finset.mem_inter.mp hh).1
  have hvis (c : Cell p.scheme.scheme) : t.scheme.scheme.scope (F.map c) ⊆ Finset.univ.image f := by
    change (t.scheme.scheme.cell (F.map c)).1 ⊆ _
    rw [F.index c]
    exact Finset.image_subset_image (Finset.subset_univ _)
  apply typeMap_eq_some_of_emb f t p hv F.map hmono hvis
    (fun d hd => F.exhaustive d (hB ▸ hd))
  · apply Finset.image_injective (Finset.image_injective f.injective)
    rw [image_restrictFace_plan, hB, hplan]
  · intro c
    refine Prod.ext (Finset.image_injective f.injective ?_)
      (show t.scheme.scheme.grade (F.map c) = p.scheme.scheme.grade c from
        congrArg Prod.snd (F.index c))
    rw [CellScheme.image_pullCell_fst _ _ (hvis c)]
    exact congrArg Prod.fst (F.index c)
  · exact hlabel
  · intro c d d' hd
    exact (congrArg (t.scheme.rows.E (F.map c)) (Subtype.ext hd)).trans
      (F.row c (PointImageSemantics.belowEquiv p.scheme.scheme f hB c d))

section SeedInstall
variable {n m : ℕ} {s : Step (Finset.univ : Finset (Fin (n + 2)))}
  (I : Input s m (n + 1) (n + 1))

structure Seed where
  scheme : CellScheme (ι := Fin (n + 2)) Finset.univ
  rows : Semantics scheme
  plan : scheme.plan = I.boundary.plan
  boundary : Cell I.boundary ↪o Cell scheme
  index : ∀ d, scheme.cell (boundary d) = I.boundary.cell d
  exhaustive : ∀ (B : Finset (Fin (n + 2))), ¬ Finset.univ ⊆ B →
    ∀ z, scheme.scope z ⊆ B → ∃ d, boundary d = z
  row : ∀ c (d : I.boundary.below (I.boundary.cell c)),
    rows.E (boundary c) ⟨boundary d.1, by rw [index, index]; exact d.2⟩ = I.rows.E c d
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  bountiful : rows.IsBountiful
  grade : ∀ d, scheme.grade d ≤ n + 1
  complete : ∀ J ∈ Plan.gradedPlan scheme.plan, J.2 ≤ n + 1 → ∃ d, scheme.cell d = J
  extend_whole : ∀ p, RespectsSemantics I.rows p →
    ∃ q, RespectsSemantics rows q ∧ ∀ d, q (boundary d) = p d

variable (F : Seed I)
abbrev height : n + 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp
abbrev seedScheme := MaximalFullLayer.scheme F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
abbrev seedOld := MaximalFullLayer.old F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
abbrev seedApex := MaximalFullLayer.apex F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
abbrev seedOwnerEquiv := MaximalFullLayer.ownerEquiv F.scheme (n + 1) (n + 2) F.grade
  (by omega) (height (n := n))
abbrev seedBoundary (d : Cell I.boundary) := seedOld I F (F.boundary d)

private theorem boundary_index (d : Cell I.boundary) :
    (seedScheme I F).cell (seedBoundary I F d) = I.boundary.cell d :=
  (MaximalFullLayer.old_index _ _ _ _ _ _).trans (F.index d)

private theorem boundary_order : StrictMono (seedBoundary I F) :=
  (SourceLayerCarrier.old_order _ _ _ _ _).comp F.boundary.strictMono

private theorem seed_complete : (seedScheme I F).IsComplete := by
  apply MaximalFullLayer.complete F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
  intro J hJ hne
  apply F.complete J hJ
  have hg := (Plan.mem_gradedPlan.mp hJ).2.2
  have hs := F.scheme.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hJ).1
  have hc := Finset.card_le_card hs
  have ha : (Finset.univ : Finset (Fin (n + 2))).card = n + 2 := by simp
  by_contra hh
  have he : J.1 = Finset.univ := Finset.eq_of_subset_of_card_le hs (by omega)
  exact hne (Prod.ext he (by dsimp only; omega))

private def seedFace {B : Finset (Fin (n + 2))} {D : CellScheme B} {sem : Semantics D}
    (G : ExactSemanticFace sem I.rows) (hB : ¬ Finset.univ ⊆ B)
    (out : Semantics (seedScheme I F))
    (hrow : ∀ c d, out.E (seedOld I F c) (seedOwnerEquiv I F c d) = F.rows.E c d) :
    ExactSemanticFace sem out where
  map := ⟨fun d => seedBoundary I F (G.map d), (boundary_order I F).injective.comp G.map.injective⟩
  index d := (boundary_index I F _).trans (G.index d)
  exhaustive z hz := by
    have hn : (seedScheme I F).cell z ≠ (Finset.univ, n + 2) := fun hh => hB (by
      change ((seedScheme I F).cell z).1 ⊆ B at hz; simpa only [hh] using hz)
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence F.scheme Unit (n + 2)
      (by omega) (height (n := n)) z hn
    have hx : F.scheme.scope x ⊆ B := by
      change ((seedScheme I F).cell (seedOld I F x)).1 ⊆ B at hz
      rwa [MaximalFullLayer.old_index] at hz
    obtain ⟨d, rfl⟩ := F.exhaustive B hB x hx
    have hd : I.boundary.scope d ⊆ B := by
      change ((seedScheme I F).cell (seedBoundary I F d)).1 ⊆ B at hz
      rwa [boundary_index] at hz
    obtain ⟨x', rfl⟩ := G.exhaustive d hd
    exact ⟨x', rfl⟩
  row c d := by
    let e := G.belowMap c d
    exact (hrow (F.boundary (G.map c)) ⟨F.boundary e.1, by rw [F.index, F.index]; exact e.2⟩).trans
      ((F.row (G.map c) e).trans (G.row c d))

include F in
private theorem install {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ t : S α (n + 2),
      typeMap I.placeLeft t = some (⟨I.left, p, hpb, hp⟩ : S α (n + 1)) ∧
      typeMap I.placeRight t = some (⟨I.right, q, hqb, hq⟩ : S α (n + 1)) ∧
      t.HasMaximalFullCell := by
  have hl0 := (PointImageSemantics.respects_iff I.left.scheme I.placeLeft I.imageLeft
    I.left.rows p).mpr hp
  have hr0 := (PointImageSemantics.respects_iff I.right.scheme I.placeRight I.imageRight
    I.right.rows q).mpr hq
  obtain ⟨u₀, hu₀, hul, hur⟩ :=
    (AmalgamatedBoundarySemantics.section_iff s I.leftScheme I.rightScheme I.shared
      I.planLeft I.planRight I.leftRows I.rightRows I.compatible hl0 hr0).mpr ha
  obtain ⟨r, hr, he0⟩ := F.extend_whole u₀ hu₀
  obtain ⟨out, u, hc, hb, hcode, hu, he, hread, htop⟩ :=
    MaximalFullLayer.exists_active F.scheme F.rows (n + 1) (n + 2) F.grade
      (by omega) (height (n := n)) (by omega) F.consistent F.bountiful F.coded hr
  let t : S α (n + 2) :=
    ⟨⟨seedScheme I F, out, hcode, hc, hb, seed_complete I F⟩,
      fun d => truncExt α (u d), fun _ => truncExt_bound _ _, hu.truncate hα⟩
  have hpL : ¬ (Finset.univ : Finset (Fin (n + 2))) ⊆ Finset.univ.erase s.a :=
    fun h => Finset.notMem_erase s.a Finset.univ (h s.ha)
  have hpR : ¬ (Finset.univ : Finset (Fin (n + 2))) ⊆ Finset.univ.erase s.b :=
    fun h => Finset.notMem_erase s.b Finset.univ (h s.hb)
  refine ⟨t, ?_, ?_, seedApex I F,
    congrArg Prod.snd (MaximalFullLayer.apex_index _ _ _ _ _), fun d => ?_⟩
  · apply typeMap_of_pointImage_face t ⟨I.left, p, hpb, hp⟩ I.placeLeft I.imageLeft
      (seedFace I F I.leftFace hpL out he)
      ((boundary_order I F).comp (AmalgamatedBoundary.left_order s I.leftScheme I.rightScheme
        I.shared I.planLeft I.planRight))
    · change Plan.restrictPlan F.scheme.plan (Finset.univ.erase s.a) = _
      rw [F.plan, show I.boundary.plan = s.plan from rfl, restrict_left, ← I.planLeft]
    · intro d
      exact (congrArg (truncExt α) ((hread _).trans ((he0 _).trans (hul d)))).trans
        (truncExt_id_of_bound (hpb d))
  · apply typeMap_of_pointImage_face t ⟨I.right, q, hqb, hq⟩ I.placeRight I.imageRight
      (seedFace I F I.rightFace hpR out he)
      ((boundary_order I F).comp (AmalgamatedBoundary.right_order s I.leftScheme I.rightScheme
        I.shared I.planLeft I.planRight))
    · change Plan.restrictPlan F.scheme.plan (Finset.univ.erase s.b) = _
      rw [F.plan, show I.boundary.plan = s.plan from rfl, restrict_right, ← I.planRight]
    · intro d
      exact (congrArg (truncExt α) ((hread _).trans ((he0 _).trans (hur d)))).trans
        (truncExt_id_of_bound (hqb d))
  · change truncExt α (u d) ≤ truncExt α (u (seedApex I F))
    rw [htop, truncExt_id_of_bound (Or.inr rfl)]; exact le_top
end SeedInstall

private def bottomProfile {ι X : Type*} [DecidableEq ι] [Fintype X]
    {A : Finset ι} {D : CellScheme A} (sem : Semantics D) (j : ℕ) (occ : Cell D → X) :
    CanonicalFieldLayer.Profile sem j X occ :=
  ⟨fun _ => ⊥, ⟨fun _ => (extVisibilityReplace_bot _ _).symm,
    fun c => by simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot (sem.E c),
    fun _ b _ _ => ⟨b, rfl, le_rfl⟩⟩, rfl, fun _ => bot_ne_top⟩

private def one {s : Step (Finset.univ : Finset (Fin 2))} {m : ℕ} (I : Input s m 1 1) : Seed I :=
  have oneH : 1 ≤ (Finset.univ : Finset (Fin 2)).card := by simp
  have oneG (d : Cell I.boundary) : I.boundary.grade d ≤ 1 := by simpa only [max_self] using I.grade_le d
  { scheme := CanonicalOneCoatom.scheme I.rows oneH
    rows := CanonicalOneCoatom.rows I.rows oneH I.proper oneG
    plan := rfl
    boundary := OrderEmbedding.ofStrictMono (CanonicalOneCoatom.old I.rows oneH)
      (SourceLayerCarrier.old_order _ _ _ _ _)
    index := fun d => SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)
    exhaustive := fun B hB z hz => by
      have hn : (CanonicalOneCoatom.scheme I.rows oneH).cell z ≠ (Finset.univ, 1) :=
        fun he => hB (by
          change ((CanonicalOneCoatom.scheme I.rows oneH).cell z).1 ⊆ B at hz; simpa only [he] using hz)
      obtain ⟨d, hd⟩ := SourceLayerCarrier.old_occurrence I.boundary
        (CanonicalFieldLayer.Profile I.rows 1 (Cell I.boundary) id) 1 (by decide) oneH z hn
      exact ⟨d, hd.symm⟩
    row := fun c d => CanonicalFieldLayer.inherited_row I.rows 1 (Cell I.boundary) id (by decide)
      oneH I.proper oneG c d
    consistent := CanonicalFieldLayer.consistent I.rows 1 (Cell I.boundary) id (by decide)
      oneH I.proper oneG I.consistent
    coded := CanonicalSeedCoding.fieldLayer I.rows 1 (Cell I.boundary) id (by decide)
      oneH I.proper oneG I.coded
    bountiful := CanonicalOneCoatom.bountiful I.rows oneH I.proper oneG
      (CoatomRecursiveInput.oldLifts I) I.left_visible I.right_visible
      (fun h => Finset.notMem_erase s.a Finset.univ (h.symm ▸ s.ha))
      (fun h => Finset.notMem_erase s.b Finset.univ (h.symm ▸ s.hb))
      (by rw [I.card_left]) (by rw [I.card_right]) I.intersection_visible
      (fun _ hC hCA => I.proper_scope_cover hC hCA)
      (fun C hC hCA hCc => I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), hCc⟩) hCA)
    grade := (CanonicalFieldLayer.data I.rows 1 (Cell I.boundary) id (by decide)
      oneH I.proper oneG).max_grade
    complete := fun J hJ hj => by
      have hj1 : J.2 = 1 := by have := (Plan.mem_gradedPlan.mp hJ).2.1; omega
      by_cases hfull : J.1 = Finset.univ
      · let q := bottomProfile I.rows 1 id
        exact ⟨(CanonicalFieldLayer.controller I.rows 1 (Cell I.boundary) id (by decide) oneH q).1,
          (CanonicalFieldLayer.controller I.rows 1 (Cell I.boundary) id
            (by decide) oneH q).2.trans (Prod.ext hfull.symm hj1.symm)⟩
      · obtain ⟨d, hd⟩ := I.complete_proper hJ hfull
        exact ⟨CanonicalOneCoatom.old I.rows oneH d,
          (SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)).trans hd⟩
    extend_whole := fun _ hp => CanonicalOneCoatom.exists_whole I.rows oneH I.proper oneG hp }

private def two {s : Step (Finset.univ : Finset (Fin 3))} {m : ℕ} (I : Input s m 2 2) : Seed I :=
  have twoH : 2 ≤ (Finset.univ : Finset (Fin 3)).card := by simp
  have twoG (d : Cell I.boundary) : I.boundary.grade d ≤ 2 := by simpa only [max_self] using I.grade_le d
  { scheme := CanonicalPairLocalSections.carrier I.rows twoH
    rows := CanonicalPairLocalSections.semantics I.rows twoH I.proper
    plan := rfl
    boundary := CanonicalRecursiveInventory.boundary I.rows 2 twoH
    index := CanonicalRecursiveInventory.boundary_cell I.rows 2 twoH
    exhaustive := fun B hB z hz => by
      rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
        2 twoH z with ⟨d, hd⟩ | ⟨j, _, _, he⟩
      · exact ⟨d, hd⟩
      · exact False.elim (hB (by
          change ((CanonicalPairLocalSections.carrier I.rows twoH).cell z).1 ⊆ B at hz
          have he' : (CanonicalPairLocalSections.carrier I.rows twoH).cell z = (Finset.univ, j) := he
          simpa only [he'] using hz))
    row := fun c d => GradeCutPairRows.old_row I.boundary _ _ 1 2 (by decide)
      (CanonicalPairLocalSections.one_le twoH) (by decide) twoH I.proper (by decide)
      I.rows (CanonicalPairLocalSections.smallRows I.rows twoH I.proper) c d
    consistent := CanonicalPairBoundary.consistent I.rows 1 2 (by decide)
      (CanonicalPairLocalSections.one_le twoH) (by decide) twoH I.proper (by decide) I.consistent
    coded := CanonicalSeedCoding.pair I.rows twoH I.proper I.coded
    bountiful := EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound I.rows 2 twoH twoG) (by decide : 0 < 2)
      (fun C B j hC hB hj hCB => CanonicalPairLowerLifting.lower_lift I.rows I.proper twoH
        (CoatomRecursiveInput.oldLifts I) I.left_visible I.right_visible
        (fun h => Finset.notMem_erase s.a Finset.univ (h.symm ▸ s.ha))
        (fun h => Finset.notMem_erase s.b Finset.univ (h.symm ▸ s.hb))
        (by rw [I.card_left]) (by rw [I.card_right]) I.intersection_visible
        (fun _ hC hCA => I.proper_scope_cover hC hCA)
        (fun C hC hCA i hi hiC _ => I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, hi, hiC⟩) hCA)
        hC hB ⟨hCB, le_rfl⟩ hj)
    grade := CanonicalRecursiveCoverage.grade_bound I.rows 2 twoH twoG
    complete := CanonicalRecursiveCoverage.complete_through I.rows 2 twoH
      (fun _ hJ hproper => I.complete_proper hJ hproper)
    extend_whole := fun _ hp => CanonicalPairBoundary.exists_whole I.rows 1 2 (by decide)
      (CanonicalPairLocalSections.one_le twoH) (by decide) twoH I.proper (by decide) hp }

private def higher {k m : ℕ} {s : Step (Finset.univ : Finset (Fin (k + 4)))}
    (I : Input s m (k + 3) (k + 3)) : Seed (n := k + 2) I :=
  have hle := CoatomRecursiveInput.height_le I
  { scheme := CoatomRecursiveInput.scheme I
    rows := CoatomRecursiveInput.rows I
    plan := CanonicalRecursiveBoundaryTransport.plan_eq I.rows (k + 3) hle
    boundary := CanonicalRecursiveContract.boundary I.rows k hle
    index := CanonicalRecursiveInventory.boundary_cell I.rows (k + 3) hle
    exhaustive := fun B hB z hz => by
      rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
        (k + 3) hle z with ⟨d, hd⟩ | ⟨j, _, _, he⟩
      · exact ⟨d, hd⟩
      · exact False.elim (hB (by
          change ((CoatomRecursiveInput.scheme I).cell z).1 ⊆ B at hz
          have he' : (CoatomRecursiveInput.scheme I).cell z = (Finset.univ, j) := he
          simpa only [he'] using hz))
    row := fun c d => CanonicalRecursiveLiteralRows.row I.rows I.proper k hle c d
    consistent := CoatomRecursiveInput.consistent I
    coded := CanonicalRecursiveCoding.coatom I
    bountiful := CoatomRecursiveInput.bountiful I
    grade := CoatomRecursiveInput.grade_bound I
    complete := CoatomRecursiveInput.complete_through I
    extend_whole := fun p hp => by
      have oldG (d : Cell I.boundary) : I.boundary.grade d ≤ k + 3 := by
        simpa only [max_self] using I.grade_le d
      let all (d : Cell (CoatomRecursiveInput.scheme I)) :
          (CoatomRecursiveInput.scheme I).below (Finset.univ, k + 3) :=
        ⟨d, Finset.subset_univ _, CoatomRecursiveInput.grade_bound I d⟩
      obtain ⟨r, hr, he⟩ := CanonicalRecursiveTopSections.exists_section I.rows I.proper
        k hle (hp.toBelow (Finset.univ, k + 3))
      exact ⟨fun d => r (all d), hr.toRespects (fun d => (all d).2),
        fun d => he ⟨d, Finset.subset_univ _, oldG d⟩⟩ }

private theorem faceMap_label {α : Ordinal.{0}} {a b : ℕ}
    (p : S α b) (r : S α a) (f : Fin a ↪ Fin b)
    (hv : Finset.univ.image f ∈ p.scheme.scheme.plan)
    (hs : p.scheme.restrictFace f hv = r.scheme) (h : typeMap f p = some r)
    (d : Cell r.scheme.scheme) :
    p.label (SemSchemeBoundaryInput.faceMap p.scheme r.scheme f hv hs d) = r.label d := by
  obtain rfl : p.restrictFace f hv = r := Option.some.inj ((typeMap_eq_some f p hv).symm.trans h)
  rfl

private theorem amalgam_of_seed {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) {n : ℕ}
    (C : CoatomPair n) {pa pb : S α (n + 1)} (h : C.Compatible pa pb)
    (F : Seed (CoatomBoundaryPresentation.of_compatible C h).input) :
    ∃ t : S α (n + 2), C.IsAmalgam pa pb t ∧ t.HasMaximalFullCell := by
  let I := (CoatomBoundaryPresentation.of_compatible C h).input
  let r := Classical.choose h
  have ha (i : Cell I.common.scheme) : pa.label (I.shared.f i) = pb.label (I.shared.g i) :=
    (faceMap_label pa r C.g₁ _ _ (Classical.choose_spec h).1 i).trans
      (faceMap_label pb r C.g₂ _ _ (Classical.choose_spec h).2 i).symm
  obtain ⟨t, hl, hr, hm⟩ := install I F hα pa.respects pb.respects pa.label_bound pb.label_bound ha
  exact ⟨t, ⟨hl, hr⟩, hm⟩

theorem supply {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) :
    MaximalCoatomAmalgamationSupply α := by
  intro n C pa pb h
  rcases n with _ | _ | k
  · exact amalgam_of_seed hα C h (one _)
  · exact amalgam_of_seed hα C h (two _)
  · exact amalgam_of_seed hα C h (higher _)

end
end VaughtConjecture.Knight.CanonicalCoatomSupply
