/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeIteration
public import VaughtConjecture.Knight.FinalGateLayer
public import VaughtConjecture.Knight.CappedDonorRetarget
public import VaughtConjecture.Knight.CappedDonorRelease
public import VaughtConjecture.Knight.CappedDonorContext
public import VaughtConjecture.Knight.CappedDonorCatalogue
public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.CappedDonorFace
public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.EffectiveGradeLifting
public import VaughtConjecture.Knight.OrderedFaceRestriction
public import VaughtConjecture.Knight.WholeDonorAttachment
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.CapObservation
public import VaughtConjecture.Knight.LowOnlyPaddedLegal

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryModelReceiving
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan
open Transform CappedDonor CappedDonor.Ref SourcePrefixRows OrbitPrefixSupport
open PairedSlotComparison SharpWitnessComposition CanonicalPairedInverse
open CoatomBoundaryExtension CellScheme.restrictFace SemSchemeBoundaryInput
noncomputable section
universe w

private theorem cut_actual_lt_cap {I : Type*} [Fintype I] {nP N J : ℕ}
    {P : SemScheme (nP + 1)} {C : SemScheme J} (R : Ref I nP N J P C) :
    R.cut R.vactL < R.vact R.cap := by
  rw [R.cut_actual]; exact (Finset.sup_lt_iff R.cap_pos).mpr fun i _ => R.margin i

private theorem ref_capped_readback {I : Type*} [Fintype I] {nP N J : ℕ}
    {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
    {j : ℕ} (hj : N ≤ j) {st : R.State j} (hst : R.Admissible st)
    {Kσ : ℕ} (hK : N ≤ Kσ) {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop Kσ) σ)
    {m : ExtOrd} (hm : R.vact R.cap ≤ m) {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : ∀ d, σ (st.u d) = min (u d) m)
    (hcap : σ (st.v (R.capC hj)) = R.vact R.cap)
    (href : ∀ i, σ (st.v (CellScheme.below.mono (R.capLe hj) (R.lowRef i))) = R.vact (R.ref i))
    (hg : st.gate ≠ ⊥) (d : P.scheme.below (effP nP j)) :
    min (u d) (R.cut R.vactL) = min (R.p d.1) (R.cut R.vactL) := by
  have hvcap : st.v (R.capC hj) ≠ ⊥ := fun hz =>
    (ne_bot_of_gt R.cap_pos) (by rw [hz, hσ.bot] at hcap; exact hcap.symm)
  have h := congrArg σ (hst.relation hj hg hvcap d)
  have hcut : σ (R.cut (R.lowC hj st.v)) = R.cut R.vactL := by
    rw [← cut_map hσ hK]; exact cut_congr hcap href
  have hsel : σ (R.sel (R.lowC hj st.v) d.1) = min (R.p d.1) (R.cut R.vactL) := by
    rw [← sel_map hσ hK,
      sel_congr (v₁ := fun e => σ (R.lowC hj st.v e)) (v₂ := R.vactL) hcap href, sel_actual]
  rw [hσ.mono.map_min, hu, hcut, hsel] at h
  rwa [min_assoc, min_eq_right ((cut_actual_lt_cap R).le.trans hm)] at h

section Catalogue
variable {I : Type*} [Fintype I] {nP N : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

abbrev Member := ↥R.Catalogue
instance : Fintype (Member R) := R.catalogue_finite.fintype

private theorem member_short (a : Member R) (f : Field P C) : Short N (a.val f) :=
  CanonicalPairedProfiles.inventory_short _ _ a.property.1 f

theorem member_bound (a : Member R) (f : Field P C) :
    a.val f ≤ CanonicalFieldLayer.ceiling N (Field P C) :=
  (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 f).trans
    (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl))

private theorem member_coded (a : Member R) (f : Field P C) : IsCodedLabel N (a.val f) := by
  rcases mem_codedAlphabet_iff.mp
    (CanonicalPairedProfiles.inventory_coded (Field P C) N a.property.1 f)
    with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩

include R in
private theorem req_grade_le (d : Cell P.scheme) : P.scheme.grade d ≤ N :=
  (Ref.gradeP_le d).trans R.arity_lt.le

private theorem profile_present (st : R.State N) (f : Field P C) :
    st.sourceProfile f = st.numeric f (by
      cases f with
      | req d => exact req_grade_le R d
      | priv d => exact gradeC_le d
      | gate => exact R.one_le_N) :=
  st.sourceProfile_of_present _

private theorem exists_actual_member_reflecting :
    ∃ (a : Member R) (δ : ExtOrd → ExtOrd), Witness (gTop N) δ ∧
      (∀ d : Cell P.scheme, δ (a.val (.req d)) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (a.val (.priv d)) = R.vact d) ∧
      δ (a.val .gate) = ⊤ ∧
      ∀ f, δ (a.val f) = ⊥ ↔ a.val f = ⊥ := by
  let st := resync (R.actualState N)
  have hadm : R.Admitted st.sourceProfile :=
    ⟨st, (R.actual_admissible N).resync, resync_synchronized (R.actual_admissible N),
      TopSupport.selfVis_top_ext N, rfl⟩
  obtain ⟨b, -, -, hprefix, -, hb, hcan, δ, hδ, hr⟩ := hadm.exists_terminal 0
  refine ⟨⟨PairedSlotEncoding.normalize N b, hcan, hb⟩, δ, hδ,
    fun d => (hr (.req d)).trans (profile_present R st (.req d)),
    fun d => (hr (.priv d)).trans (profile_present R st (.priv d)),
    (hr .gate).trans (profile_present R st .gate), fun f => ?_⟩
  rw [hr, PairedSlotEncoding.normalize_bot_iff]
  exact (bottom_pattern_of_cap_agreement (ofOrd_ne_bot 0) hprefix f).symm

private abbrev privateCell (c : Cell C.scheme) : C.scheme.below (effC N N) :=
  Ref.privCell c (gradeC_le c)

private theorem exists_factorization (c : Cell C.scheme) (hc : C.scheme.grade c = N)
    (a : Member R) {p : C.scheme.below (effC N N) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC N N) p)
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd} (hσ : Witness (gTop N) σ)
    (hγ : SelfVis N γ) (hpos : ⊥ < γ) (hpc : γ < p (privateCell c))
    (hag : ∀ d, min (σ (a.val (.priv d.1))) γ = min (p d) γ) :
    ∃ B : ℕ, grid N B ∈ sourceGrid N (Fintype.card (Field P C)) ∧
      ∃ (f : C.scheme.below (effC N N) → ExtOrd) (ν : ExtOrd → ExtOrd),
        RespectsSemanticsBelow C.rows (effC N N) f ∧ (∀ d, f d ≠ ⊤) ∧
        (∀ d, min (f d) (grid N B) = min (a.val (.priv d.1)) (grid N B)) ∧
        Witness (gTop N) ν ∧ (∀ x, ν x ≤ p (privateCell c)) ∧
        (∀ d, ν (f d) = min (p d) (p (privateCell c))) ∧
        γ ≤ ν (grid N B) ∧ ∀ x, Short N x → min (ν x) γ = min (σ x) γ := by
  classical
  have hi : C.scheme.cell c = effC N N := by
    have hh := C.scheme.grade_le_card_scope c; rw [hc] at hh
    exact Prod.ext (Finset.eq_univ_of_card (C.scheme.scope c)
      (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hh)))
      (hc.trans (min_self N).symm)
  let toEff := CellScheme.below.mono (D := C.scheme)
    (show GradedLe (C.scheme.cell c) (effC N N) from hi ▸ GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := C.scheme)
    (show GradedLe (effC N N) (C.scheme.cell c) from hi ▸ GradedLe.refl _)
  obtain ⟨st, hst, -, -, hprofile⟩ := a.property.2
  have hsource (e : C.scheme.below (C.scheme.cell c)) : st.v (toEff e) = a.val (.priv e.1) :=
    (profile_present R st (.priv e.1)).symm.trans (congrFun hprofile (.priv e.1))
  obtain ⟨δ, hδ, hδpos, -, -, ⟨fac⟩⟩ :=
    PrivateRowFactorization.exists_factorization c (Fintype.card (Field P C))
      (hst.v_respects.mono _) (hp.mono _)
      (fun e => by
        change st.v (toEff e) ∈ _; rw [hsource, hc]
        exact CanonicalPairedProfiles.inventory_coded _ _ a.property.1 _)
      (fun e => by change Short _ (st.v (toEff e)); rw [hsource, hc]; exact member_short R a _)
      (by simpa only [hc] using hσ) (by simpa only [hc] using hγ) hpos hpc
      (fun e => by change min (σ (st.v (toEff e))) γ = _; rw [hsource]; exact hag (toEff e))
  rw [hc] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hm
  · exact (not_lt_of_ge (le_of_eq hz) hδpos).elim
  obtain ⟨B, hB, he⟩ := Finset.mem_image.mp hm
  change grid N B = δ at he; subst δ
  exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨B, hB, rfl⟩),
    fac.source ∘ fromEff, fac.outgoing, fac.lawful.mono _, fun d => fac.proper (fromEff d),
    fun d => (fac.prefix_eq (fromEff d)).trans (congrArg (fun x => min x (grid N B)) (hsource _)),
    by simpa only [hc] using fac.witness, fac.bounded, fun d => fac.readback (fromEff d),
    fac.reaches, by simpa only [hc] using fac.caps⟩

section Installed
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : N ≤ A.card)
  (hsep : ∀ d : Cell D, ¬ GradedLe (A, N) (D.cell d))
  (lower : Member R → Cell D → ExtOrd)
  (hlaw : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1))
  (hbound : ∀ a d, D.grade d ≤ N → lower a d ≤ CanonicalFieldLayer.ceiling N (Field P C))
  (hprefix : ∀ a b h, h ∈ sourceGrid N (Fintype.card (Field P C)) →
    Agree a.val b.val h → ∀ d, D.grade d ≤ N → min (lower a d) h = min (lower b d) h)

include sem hA hsep lower hlaw hbound hprefix

def install : FinalGateLayer.Input D N (Field P C) (Member R) where
  sem := sem
  positive := R.one_le_N
  height := hA
  separated := hsep
  fields a := a.val
  gate := .gate
  grid := sourceGrid N (Fintype.card (Field P C))
  bot_mem := sourceGrid_bot _ _
  ceiling := CanonicalFieldLayer.ceiling N (Field P C)
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound N (Field P C) hh
  grid_visible _ hh := sourceGrid_visible hh
  lower := lower
  lower_lawful := hlaw
  lower_bound := hbound
  lower_prefix := hprefix
  gate_visible a := by
    obtain ⟨st, -, -, hg, he⟩ := a.property.2
    rw [← he, st.sourceProfile_of_present (f := .gate) R.one_le_N]; exact hg
  gate_bound a := member_bound R a .gate

local notation "F" => install R sem hA hsep lower hlaw hbound hprefix

abbrev oldAt (d : Cell D) (hd : D.grade d ≤ N) : (F).carrier.below (A, N) :=
  ⟨(F).old d, by rw [(F).old_index]; exact ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩⟩

private theorem layer_capped_readback
    (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
    (hreqGrade : ∀ d, D.grade (req d) = P.scheme.grade d)
    (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)
    (hreq : ∀ a d, lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, lower a (priv d) = a.val (.priv d))
    {v : (F).carrier.below (A, N) → ExtOrd}
    (hv : RespectsSemanticsBelow (F).rows (A, N) v)
    (hretain : ∀ d, v (oldAt R sem hA hsep lower hlaw hbound hprefix (priv d)
      ((hprivGrade d).trans_le (gradeC_le d))) = R.vact d)
    (b : Member R) (hpositive : v ((F).addedAt b true) ≠ ⊥) (d : Cell P.scheme) :
    min (v (oldAt R sem hA hsep lower hlaw hbound hprefix (req d)
      ((hreqGrade d).trans_le (req_grade_le R d)))) (R.cut R.vactL) =
      min (R.p d) (R.cut R.vactL) := by
  let privAt' (e : Cell C.scheme) :=
    oldAt R sem hA hsep lower hlaw hbound hprefix (priv e) ((hprivGrade e).trans_le (gradeC_le e))
  let reqAt' (e : Cell P.scheme) :=
    oldAt R sem hA hsep lower hlaw hbound hprefix (req e) ((hreqGrade e).trans_le (req_grade_le R e))
  let c := privAt' R.cap
  have hc : (F).carrier.grade c.1 = N :=
    (congrArg Prod.snd ((F).old_index (priv R.cap))).trans
      ((hprivGrade R.cap).trans (congrArg Prod.snd R.cap_cell))
  have hpos : v c ≠ ⊥ := by rw [hretain]; exact ne_bot_of_gt R.cap_pos
  obtain ⟨a, hca, hga, τ, hτ, -, hr⟩ := (F).exists_active_chart hv c hc hpos b hpositive
  have hm : R.vact R.cap ≤ v ((F).addedAt a false) := (hretain R.cap).symm.trans_le hca
  obtain ⟨st, hst, -, -, hp⟩ := a.property.2
  have hsu (e : P.scheme.below (effP nP N)) : a.val (.req e.1) = st.u e :=
    (congrFun hp (.req e.1)).symm.trans (profile_present R st (.req e.1))
  have hsv (e : C.scheme.below (effC N N)) : a.val (.priv e.1) = st.v e :=
    (congrFun hp (.priv e.1)).symm.trans (profile_present R st (.priv e.1))
  have hg : st.gate ≠ ⊥ := fun hz =>
    hga ((congrFun hp .gate).symm.trans ((profile_present R st .gate).trans hz))
  have hread (e : C.scheme.below (effC N N)) (he : R.vact e.1 ≤ R.vact R.cap) :
      τ (st.v e) = R.vact e.1 :=
    (congrArg τ (((F).source_old a _).trans ((hpriv a e.1).trans (hsv e)))).symm.trans
      ((hr (privAt' e.1)).trans ((congrArg (fun x => min x _) (hretain e.1)).trans
        (min_eq_left (he.trans hm))))
  exact ref_capped_readback le_rfl hst le_rfl hτ hm
    (fun e => (congrArg τ (((F).source_old a _).trans ((hreq a e.1).trans (hsu e)))).symm.trans
      (hr (reqAt' e.1)))
    (hread (R.capC le_rfl) le_rfl)
    (fun i => hread (CellScheme.below.mono (R.capLe le_rfl) (R.lowRef i)) (R.ref_lt_cap i).le)
    hg (Ref.reqCell d (req_grade_le R d))

private theorem exists_owner_capped_lift
    (hsupport : ∀ a d, D.grade d ≤ N →
      Supported N ((sourceGrid N (Fintype.card (Field P C))) : Set ExtOrd) a.val (lower a d))
    (priv : Cell C.scheme ↪ Cell D) (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)
    (hpriv : ∀ a d, lower a (priv d) = a.val (.priv d))
    (c : Cell C.scheme) (hc : C.scheme.grade c = N)
    {p : C.scheme.below (effC N N) → ExtOrd} (hp : RespectsSemanticsBelow C.rows (effC N N) p)
    {q : (F).carrier.below (A, N) → ExtOrd} (hq : RespectsSemanticsBelow (F).rows (A, N) q)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hpos : ⊥ < γ) (hpc : γ < p (privateCell c))
    (hag : ∀ d, min (q (oldAt R sem hA hsep lower hlaw hbound hprefix (priv d.1)
      ((hprivGrade d.1).trans_le (gradeC_le d.1)))) γ = min (p d) γ) :
    ∃ w : (F).carrier.below (A, N) → ExtOrd,
      RespectsSemanticsBelow (F).rows (A, N) w ∧
      (∀ d : C.scheme.below (effC N N),
        w (oldAt R sem hA hsep lower hlaw hbound hprefix (priv d.1)
          ((hprivGrade d.1).trans_le (gradeC_le d.1))) = min (p d) (p (privateCell c))) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  let privAt' (e : Cell C.scheme) :=
    oldAt R sem hA hsep lower hlaw hbound hprefix (priv e) ((hprivGrade e).trans_le (gradeC_le e))
  let c' := privAt' c
  have hc' : (F).carrier.grade c'.1 = N :=
    (congrArg Prod.snd ((F).old_index (priv c))).trans ((hprivGrade c).trans hc)
  have hreach : γ ≤ q c' := min_eq_right_iff.mp ((hag (privateCell c)).trans (min_eq_right hpc.le))
  let seed : Member R := ⟨PairedSlotEncoding.normalize N (fun _ => ⊥),
    (Ref.Admitted.zero R).normalize_mem_catalogue (fun _ => bot_ne_top)⟩
  obtain ⟨a, σ, hσ, hb, hchart⟩ := (F).exists_cap_chart hq c' hc' seed hγ hreach
  obtain ⟨B, hB, f, ν, hf, hproper, hpref, hν, _, hprivate, hνreach, hνcaps⟩ :=
    exists_factorization R c hc a hp hσ hγ hpos hpc fun d => by
      rw [min_eq_left (hb _),
        show σ (a.val (.priv d.1)) = min (q (privAt' d.1)) γ from
          (congrArg σ (((F).source_old a _).trans (hpriv a d.1))).symm.trans (hchart (privAt' d.1))]
      exact hag d
  obtain ⟨b₀, -, -, hpriv_b, hpref_b, hcat, hnorm, κ, hκ, hread_b, hfix, hreach_κ, -⟩ :=
    positive_cap_repair a.property hf hproper hpref
  let b : Member R := ⟨PairedSlotEncoding.normalize N b₀, hcat⟩
  obtain ⟨_, hsource⟩ := (F).decode_source_prefix hsupport a b hB (ofOrd_ne_bot _) hnorm hκ hreach_κ
    (fix_sourceGrid hκ.bot hfix _)
    (fun f₀ hf₀ => (congrArg κ (PairedSlotEncoding.eq_of_cap_eq_lt (hnorm f₀).symm hf₀)).trans
      ((hread_b f₀).trans (PairedSlotEncoding.eq_of_cap_eq_lt (hpref_b f₀).symm hf₀).symm))
  let w := fun d : (F).carrier.below (A, N) => ν (κ ((F).source b d.1))
  have hcaps (d : (F).carrier.below (A, N)) : min (w d) γ = min (q d) γ := by
    have hpre (z) : min (ν (min z (grid N B))) γ = min (ν z) γ := by
      rw [hν.mono.map_min, min_assoc, min_eq_right hνreach]
    exact ((hpre _).symm.trans ((congrArg (fun z => min (ν z) γ) (hsource d)).trans (hpre _))).trans
      ((hνcaps _ ((F).source_short hsupport (member_short R)
        (fun _ hz => CanonicalFieldLayer.grid_short N (Field P C) hz) a d.1 d.2.2)).trans
        (by rw [hchart d, min_assoc, min_self]))
  refine ⟨w, map_respects_of_positive_cap_agreement ((F).source_lawful b) hq
    (fun d => d.2.2) (bounded_comp hκ hν le_rfl) hpos.ne' hcaps, fun d => ?_, hcaps⟩
  change ν (κ ((F).source b ((F).old (priv d.1)))) = _
  rw [(F).source_old]
  change ν (κ (lower b (priv d.1))) = _
  rw [hpriv, show b.val (.priv d.1) = PairedSlotEncoding.normalize N b₀ (.priv d.1) from rfl,
    hread_b, hpriv_b, hprivate]

private theorem final_bountiful {S : Finset ι} (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
    (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) sem)
    (hsupport : ∀ a d, D.grade d ≤ N →
      Supported N ((sourceGrid N (Fintype.card (Field P C))) : Set ExtOrd) a.val (lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, lower a d.1 = a.val f))
    (hpriv : ∀ a d, lower a (E.map d) = a.val (.priv d))
    (hcard : A.card = N + 1)
    (hmute : ∀ x : Cell D, D.grade x = N → D.scope x ≠ S → sem.E x ⟨x, GradedLe.refl _⟩ = ⊥)
    (hpred : ∀ (I₀ J : Finset ι × ℕ), I₀ ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan →
      (h : GradedLe I₀ J) → ¬ GradedLe (A, N) J → CappedLift sem h) :
    (F).rows.IsBountiful := by
  have hS_card : S.card = N := by
    rw [← hS, Finset.card_image_of_injective _ place.injective, Finset.card_univ, Fintype.card_fin]
  apply EffectiveGradeLifting.bountiful_of_same_grade
  intro B B' i hB hB' hsub
  by_cases hBB : B = B'
  · subst hBB; exact lift_refl
  by_cases hJ : GradedLe (A, N) (B', i)
  · have hB'A : A = B' := (Finset.Subset.antisymm (D.isPlan.subset_of_mem
      (Plan.mem_gradedPlan.mp hB').1) hJ.1).symm
    subst hB'A
    have hBcard : B.card ≤ N := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hBB⟩); omega
    have hiN : N = i := (le_antisymm ((Plan.mem_gradedPlan.mp hB).2.2.trans hBcard) hJ.2).symm
    subst hiN
    have hN2 : 2 ≤ N := by have := R.arity_lt; omega
    have hlift : CappedLift sem (show GradedLe (B, N - 1) (A, N - 1) from ⟨hsub, le_rfl⟩) :=
      hpred (B, N - 1) (A, N - 1)
        (Plan.mem_gradedPlan.mpr ⟨(Plan.mem_gradedPlan.mp hB).1, by dsimp; omega,
          (Nat.sub_le _ _).trans (Plan.mem_gradedPlan.mp hB).2.2⟩)
        (Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, by dsimp; omega, (Nat.sub_le _ _).trans hA⟩)
        ⟨hsub, le_rfl⟩ (fun h => by have := h.2; dsimp at this; omega)
    by_cases hBS : S = B
    · subst hBS
      intro p q γ hp hq hγ hag
      let e := NativePrivateFace.fullEquiv C place hS ((F).inheritedFace hsub hBB E)
      have hpn := (NativePrivateFace.respects_iff C place hS
        ((F).inheritedFace hsub hBB E) p).mp hp
      by_cases hbot : γ = ⊥
      · obtain ⟨a₀, ha₀, hprivate, -, -⟩ := bottom_supply (R := R) hpn
        obtain ⟨b₀, _, _, hpref_b, _, hadm, hcan, δ, hδ, hread⟩ := ha₀.exists_terminal 0
        let b : Member R := ⟨PairedSlotEncoding.normalize N b₀, hcan, hadm⟩
        have hrefl (f : Field P C) : δ (b.val f) = ⊥ ↔ b.val f = ⊥ := by
          change δ (PairedSlotEncoding.normalize N b₀ f) = ⊥ ↔ _
          rw [hread, PairedSlotEncoding.normalize_bot_iff]
          exact (bottom_pattern_of_cap_agreement (ofOrd_ne_bot 0) hpref_b f).symm
        have hlower : RespectsSemanticsBelow sem (A, N) (fun d => δ (lower b d.1)) :=
          map_respects_of_short_or_reflecting ((F).lower_lawful b) (fun d => d.2.2) hδ fun c =>
            (howners b c).imp id fun ho d => by
              obtain ⟨f, hf⟩ := ho d
              change δ (lower b d.1) = ⊥ ↔ lower b d.1 = ⊥
              rw [hf]; exact hrefl f
        refine ⟨fun d => δ ((F).source b d.1),
          (F).decoded_respects hsupport (member_short R)
            (fun _ hz => CanonicalFieldLayer.grid_short N (Field P C) hz) b hδ hlower,
          fun _ => by simp only [hbot, min_eq_right bot_le], fun d => ?_⟩
        obtain ⟨x, rfl⟩ := e.surjective d
        change δ ((F).source b ((F).old (E.map x.1))) = p (e x)
        rw [(F).source_old]
        exact (congrArg δ (hpriv b x.1)).trans ((hread (.priv x.1)).trans (hprivate x))
      · classical
        by_cases hhigh : ∀ e' : (F).carrier.below (S, N), (F).carrier.grade e'.1 = N → p e' ≤ γ
        · exact (F).lift_inactive hsub hlift hp hq hγ hag hhigh
        push Not at hhigh
        obtain ⟨e₀, he₀, hpe₀⟩ := hhigh
        let pn := p ∘ e
        have hg (d : C.scheme.below (effC N N)) :
            (F).carrier.grade (e d).1 = C.scheme.grade d.1 :=
          NativePrivateFace.fullEquiv_grade C place hS ((F).inheritedFace hsub hBB E) d
        let : Fintype (Cell C.scheme) := Fintype.ofFinite _
        let s := Finset.univ.filter fun c : Cell C.scheme => C.scheme.grade c = N
        have hs : (e.symm e₀).1 ∈ s := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by rw [← hg, e.apply_symm_apply, he₀]⟩
        obtain ⟨c, hc, hm⟩ := Finset.exists_max_image s (fun c => pn (privateCell c)) ⟨_, hs⟩
        have hpc : γ < pn (privateCell c) := hpe₀.trans_le
          ((show pn (privateCell (e.symm e₀).1) = p e₀ from by
              change p (e (e.symm e₀)) = p e₀; rw [e.apply_symm_apply]) ▸ hm _ hs)
        have hcn : C.scheme.grade c = N := (Finset.mem_filter.mp hc).2
        obtain ⟨u, hu, hread, hcaps⟩ := exists_owner_capped_lift R sem hA hsep lower hlaw hbound
          hprefix hsupport E.map (fun d => congrArg Prod.snd (E.index d)) hpriv c hcn
          hpn hq hγ (bot_lt_iff_ne_bot.mpr hbot) hpc fun d => hag (e d)
        have hM : SelfVis N (pn (privateCell c)) := by
          have hh : SelfVis (C.scheme.grade c) (pn (privateCell c)) :=
            (hpn.orderly (privateCell c)).symm
          rwa [hcn] at hh
        obtain ⟨r, hr, hprivate, hcap, -⟩ := (F).restore hsub hlift hp hu hM
          (fun d => by obtain ⟨b, rfl⟩ := e.surjective d; exact hread b)
          (fun d hd => by
            obtain ⟨b, rfl⟩ := e.surjective d
            exact hm b.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hg b).symm.trans hd⟩))
        exact ⟨r, hr, fun d => (GradeTailRestoration.cap_below (hcap d) hpc.le).trans (hcaps d),
          hprivate⟩
    · intro p q γ hp hq hγ hag
      refine (F).lift_inactive hsub hlift hp hq hγ hag fun e he => ?_
      obtain ⟨x, hx⟩ := (F).proper_occurrence hsub hBB e
      have hxg : D.grade x.1 = N := by
        have h := congrArg Prod.snd ((F).old_index x.1)
        change (F).carrier.grade ((F).old x.1) = D.grade x.1 at h
        rw [← hx, he] at h; exact h.symm
      have hxS : D.scope x.1 ≠ S := fun hxs => by
        have hlt : B.card < A.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hBB⟩)
        exact (Ne.symm hBS) (Finset.eq_of_subset_of_card_le (hxs ▸ x.2.1) (by omega)).symm
      have hdiag : (F).rows.E e.1 ⟨e.1, GradedLe.refl _⟩ = ⊥ := by
        rcases e with ⟨e, _⟩; change e = (F).old x.1 at hx; subst hx
        exact ((F).inherited_row x.1 ⟨x.1, GradedLe.refl _⟩).trans (hmute x.1 hxg hxS)
      rw [hp.eq_bot_of_diagonal e hdiag]; exact bot_le
  · exact (F).inherited_lift (I₀ := (B, i)) (J := (B', i)) ⟨hsub, le_rfl⟩ hJ
      (hpred (B, i) (B', i) hB hB' ⟨hsub, le_rfl⟩ hJ)
end Installed
end Catalogue

private theorem card_S {ι : Type*} [DecidableEq ι] {N : ℕ} {S : Finset ι}
    (place : Fin N ↪ ι) (hS : Finset.univ.image place = S) : S.card = N := by
  rw [← hS, Finset.card_image_of_injective _ place.injective, Finset.card_univ, Fintype.card_fin]

private theorem faceMap_cast {m k : ℕ} (D : SemScheme k) (Q : SemScheme m)
    (f : Fin m ↪ Fin k) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (he : D.restrictFace f hv = Q) (d : Cell Q.scheme) :
    faceMap D Q f hv he d = toCell D.scheme f hv (SemScheme.castCell he.symm d) := by
  subst Q; rfl

theorem finiteCutReceiving {M : Type w} {α : LimitStage} {R : KnightRealization α M}
    (hM : R.IsModel) : FiniteCutReceiving R := by
  intro n t p hp P hP δ hδbot hδα
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact absurd hδbot (lt_irrefl _)
    · exact absurd hδα (not_lt.mpr le_top)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
  let reqs : List BlockRequest := ⟨limitPart ν, finitePart ν⟩ :: donorRequests P
  have hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1 := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨isNonSuccessor_limitPart ν, (limitPart_le ν).trans_lt hν⟩
    · exact donorRequests_ok P r hr
  obtain ⟨C₀, hmax, hcap_pos, hmargin, hm⟩ :=
    exists_referenceContext_margin' hM p hp reqs hreqs (max (n + 1) 3)
  have hNmin : n + 1 < C₀.N := (le_max_left _ _).trans_lt hmax
  have h3N : 3 < C₀.N := (le_max_right _ _).trans_lt hmax
  obtain ⟨_, Rf, hRp, hRv, -, hK, hA', hA, hμ, -, -, -, hface_ex⟩ :=
    ref_of_referenceContext' hM p hp P hP hreqs (fun r hr => List.mem_cons_of_mem _ hr) C₀ hNmin
      hcap_pos hmargin
  have hlt : ofOrd ν < Rf.cut Rf.vactL := by
    have hmem : limitPart ν ∈ blocksOf reqs := mem_blocksOf.mpr ⟨_, List.mem_cons_self, rfl⟩
    have hoff : finitePart ν < C₀.N := C₀.offset_lt _ List.mem_cons_self
    rw [Rf.cut_actual]
    refine lt_of_lt_of_le ?_ (Finset.le_sup (f := fun i : ↥(blocksOf reqs) =>
      ofOrd (Rf.μ i + C₀.N)) (Finset.mem_univ ⟨limitPart ν, hmem⟩))
    rw [hμ]; change ofOrd ν < ofOrd (limitPart ν + C₀.N); rw [ofOrd_lt_ofOrd]
    exact (decomposition ν).symm.trans_lt ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hoff))
  obtain ⟨hvP, hPf, hvC, hCf, hface⟩ := hface_ex
  have hN4 : 4 ≤ C₀.N := by omega
  obtain ⟨k, hk⟩ : ∃ k, C₀.N = k + 4 := ⟨C₀.N - 4, by omega⟩
  have hmk : C₀.m = k + 4 := hm.trans hk
  let u := C₀.ctx
  let p₀ := C₀.p₀
  let e := C₀.proj
  have hu : R.eval u = some p₀ := C₀.eval_ctx
  have hut : e.trans u = t := C₀.proj_ctx
  -- Transport `C₀.m = k + 4` and `C₀.N = k + 4` cleanly via an auxiliary generalizing `m, N`
  suffices ∀ {N J : ℕ} (hJ : J = N) (_ : N = k + 4) {u' : Fin J ↪ M} {p₀' : S α.1 J}
      (_ : R.eval u' = some p₀') (e' : Fin n ↪ Fin J) (_ : e'.trans u' = t)
      (hvC' : Finset.univ.image e' ∈ p₀'.scheme.scheme.plan)
      (hC' : p₀'.scheme.restrictFace e' hvC' = p.scheme)
      (Rf' : Ref ↥(blocksOf reqs) n N J P.scheme p₀'.scheme),
      Rf'.p = P.label → Rf'.vact = p₀'.label → Rf'.KA = n →
      Rf'.A' = Finset.univ.image e' → Rf'.A = Finset.univ.image Fin.castSuccEmb →
      HEq Rf'.face (commonFace Fin.castSuccEmb hvP hPf e' hvC' hC' n) →
      ofOrd ν ≤ Rf'.cut Rf'.vactL →
      ∃ (y : M) (hy : y ∉ Set.range t) (q' : S α.1 (n + 1)), R.eval (snoc t y hy) = some q' ∧
        ∃ h : q'.scheme = P.scheme,
          ∀ d, min (q'.label d) (ofOrd ν) = min (P.label (SemScheme.castCell h d)) (ofOrd ν) from
    this hm hk hu e hut hvC hCf Rf hRp hRv hK hA' hA hface hlt.le
  rintro N J rfl rfl u' p₀' hu' e' hut' hvC' hC' Rf' hRp' hRv' hK' hA'' hA₀ hface' hδ
  subst hut'
  let W := WholeDonorAttachment.input e' p₀'.scheme P.scheme p.scheme hvC' hvP hC' hPf
  have hf : ∀ i : Cell W.common.scheme,
      ∃ d : W.right.scheme.below (Rf'.A, Rf'.KA),
        d.1 = W.shared.g i ∧ (Rf'.face d).1 = W.shared.f i := fun i => by
    have halign : ∀ {AP : Finset (Fin (n + 1))} {AC : Finset (Fin (k + 4))} {ka : ℕ}
        (φ : P.scheme.scheme.below (AP, ka) ≃ p₀'.scheme.scheme.below (AC, ka)),
        AP = Finset.univ.image Fin.castSuccEmb → AC = Finset.univ.image e' → ka = n →
        HEq φ (commonFace Fin.castSuccEmb hvP hPf e' hvC' hC' n) →
        ∃ d : P.scheme.scheme.below (AP, ka),
          d.1 = faceMap P.scheme p.scheme Fin.castSuccEmb hvP hPf i ∧
          (φ d).1 = faceMap p₀'.scheme p.scheme e' hvC' hC' i
      | _, _, _, φ, rfl, rfl, rfl, hφ => by
        obtain rfl := eq_of_heq hφ
        let q : p.scheme.scheme.below (Finset.univ, n) := ⟨i, Finset.subset_univ _, gradeC_le i⟩
        refine ⟨bP Fin.castSuccEmb hvP n (castBelow hPf.symm (Finset.univ, n) q), ?_, ?_⟩
        · change toCell P.scheme.scheme Fin.castSuccEmb hvP (castBelow hPf.symm _ q).1 = _
          rw [castBelow_val]; exact (faceMap_cast P.scheme p.scheme Fin.castSuccEmb hvP hPf i).symm
        · rw [commonFace_apply, Equiv.symm_apply_apply, castBelow_castBelow_symm]
          change toCell p₀'.scheme.scheme e' hvC' (castBelow hC'.symm _ q).1 = _
          rw [castBelow_val]; exact (faceMap_cast p₀'.scheme p.scheme e' hvC' hC' i).symm
    exact halign Rf'.face hA₀ hA'' hK' hface'
  have hBcard : (WholeDonorAttachment.privateScope (N := k + 4)).card = k + 4 :=
    card_S W.placeLeft W.imageLeft
  have hTcard : (WholeDonorAttachment.donorScope e').card = n + 1 :=
    card_S W.placeRight W.imageRight
  have hBne : WholeDonorAttachment.privateScope (N := k + 4) ≠ Finset.univ := fun he => by
    have h := hBcard; rw [he, Finset.card_univ, Fintype.card_fin] at h; omega
  have hTne : WholeDonorAttachment.donorScope e' ≠ Finset.univ := fun he => by
    have h := hTcard; rw [he, Finset.card_univ, Fintype.card_fin] at h
    have := Rf'.arity_lt; omega
  let Ggrid := sourceGrid (k + 4) (Fintype.card (Field W.right W.left))
  let θ := CanonicalFieldLayer.ceiling (k + 4) (Field W.right W.left)
  let O := OrdinaryPredecessorSupply.build (G := Ggrid) (θ := θ) W k hBne hTne
    (WholeDonorAttachment.union e') (Finset.card_fin _) hBcard (hTcard ▸ Rf'.arity_lt)
    (fun _ hz => sourceGrid_visible hz) (sourceGrid_visible (sourceGrid_endpoint le_rfl))
    (ofOrd_ne_top _) (sourceGrid_endpoint le_rfl)
  have hshared (a : Member Rf') (i : Cell W.common.scheme) :
      a.val (.priv (W.shared.f i)) = a.val (.req (W.shared.g i)) := by
    obtain ⟨d, hd, he⟩ := hf i; rw [← hd, ← he]
    obtain ⟨st, hs, -, -, he'⟩ := a.property.2
    rw [← he', profile_present, profile_present]
    exact (hs.face d (req_grade_le Rf' d.1)).symm
  let bnd (a : Member Rf') : Cell W.boundary → ExtOrd :=
    W.paste (fun d => a.val (.priv d)) (fun d => a.val (.req d))
  have hbnd_law (a : Member Rf') : RespectsSemantics W.rows (bnd a) := by
    obtain ⟨st, hs, -, -, he⟩ := a.property.2
    have hprivL : RespectsSemantics W.left.rows (fun d => a.val (.priv d)) := by
      have hfn : (fun d : Cell W.left.scheme => a.val (.priv d)) =
          fun d => st.v ⟨d, (present_priv_iff (k + 4) d).mpr (gradeC_le d)⟩ := by
        funext d; rw [← he, profile_present]; rfl
      rw [hfn]; exact hs.v_respects.toRespects _
    have hreqL : RespectsSemantics W.right.rows (fun d => a.val (.req d)) := by
      have hfn : (fun d : Cell W.right.scheme => a.val (.req d)) =
          fun d => st.u ⟨d, (present_req_iff (k + 4) d).mpr (req_grade_le Rf' d)⟩ := by
        funext d; rw [← he, profile_present]; rfl
      rw [hfn]; exact hs.u_respects.toRespects _
    exact W.paste_respects hprivL hreqL (hshared a)
  have hbnd_bnd (a : Member Rf') (d : Cell W.boundary) : bnd a d ≤ θ :=
    WholeDonorOrdinarySections.paste_bound W (fun _ => member_bound Rf' a _)
      (fun _ => member_bound Rf' a _) (hshared a) d
  have hbnd_fld (a : Member Rf') (d : Cell W.boundary) :
      ∃ f : Field W.right W.left, bnd a d = a.val f := by
    rcases WholeDonorOrdinarySections.covered W d with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨.priv c, W.paste_left _ _ c⟩
    · exact ⟨.req c, W.paste_right _ _ (hshared a) c⟩
  let lower (a : Member Rf') : Cell O.carrier → ExtOrd := O.render (hbnd_law a) (hbnd_bnd a)
  have hlow_priv (a : Member Rf') (d : Cell W.left.scheme) :
      lower a (O.leftFace.map d) = a.val (.priv d) :=
    (congrArg (lower a) (O.left_map d)).trans ((O.readback _ _ _).trans (W.paste_left _ _ d))
  have hlow_req (a : Member Rf') (d : Cell W.right.scheme) :
      lower a (O.rightFace.map d) = a.val (.req d) :=
    (congrArg (lower a) (O.right_map d)).trans
      ((O.readback _ _ _).trans (W.paste_right _ _ (hshared a) d))
  have hsep : ∀ d : Cell O.carrier, ¬ GradedLe (Finset.univ, k + 4) (O.carrier.cell d) :=
    fun d hd => (not_le_of_gt (O.full_below d (Finset.Subset.antisymm (Finset.subset_univ _) hd.1))) hd.2
  have hlow_law (a : Member Rf') := (O.lawful (hbnd_law a) (hbnd_bnd a)).toBelow (Finset.univ, k + 4)
  have hlow_bnd (a : Member Rf') (d : Cell O.carrier) (_ : O.carrier.grade d ≤ k + 4) :=
    O.bound (hbnd_law a) (hbnd_bnd a) d
  have hlow_pref (a b : Member Rf') (h : ExtOrd) (hh : h ∈ Ggrid)
      (hab : Agree a.val b.val h) (d : Cell O.carrier) (_ : O.carrier.grade d ≤ k + 4) :=
    O.agreement (hbnd_law a) (hbnd_bnd a) (hbnd_law b) (hbnd_bnd b) hh
      (CanonicalFieldLayer.grid_bound _ _ hh)
      (WholeDonorOrdinarySections.paste_agreement W (hshared a) (hshared b)
        (fun _ => hab _) (fun _ => hab _)) d
  let F := install Rf' O.rows (by simp) hsep lower hlow_law hlow_bnd hlow_pref
  have hsupp (a : Member Rf') (d : Cell O.carrier) (_ : O.carrier.grade d ≤ k + 4) :
      Supported (k + 4) (Ggrid : Set ExtOrd) a.val (lower a d) :=
    (O.support _ _ d).substitute (fun _ hz => sourceGrid_visible hz) fun x => by
      obtain ⟨f, hfx⟩ := hbnd_fld a x; rw [hfx]; exact supported_field (k + 4) _ a.val f
  have howners (a : Member Rf') (c : O.carrier.below (Finset.univ, k + 4)) :
      (∀ d, Short (O.carrier.grade c.1) (O.rows.E c.1 d)) ∨
      (∀ d : O.carrier.below (O.carrier.cell c.1),
        ∃ f : Field W.right W.left, lower a d.1 = a.val f) :=
    (O.classification c.1).imp id fun ho d => by
      obtain ⟨x, hx⟩ := ho d; obtain ⟨f, hfx⟩ := hbnd_fld a x
      exact ⟨f, hx ▸ (O.readback _ _ x).trans hfx⟩
  have hpred_lift (CI BJ : Finset (Fin (k + 5)) × ℕ)
      (hi : CI ∈ Plan.gradedPlan O.carrier.plan) (hj : BJ ∈ Plan.gradedPlan O.carrier.plan)
      (h : GradedLe CI BJ) (hne : ¬ GradedLe (Finset.univ, k + 4) BJ) :
      CappedLift O.rows h := by
    rw [O.plan] at hi hj
    by_cases hs : BJ.1 = Finset.univ
    · exact O.lower_lift CI BJ hi hj h (by by_contra hn; exact hne ⟨hs ▸ Finset.Subset.refl _, by omega⟩)
    · exact O.proper_lift CI BJ hi hj hs h
  have hbount : F.rows.IsBountiful :=
    final_bountiful Rf' O.rows (by simp) hsep lower hlow_law hlow_bnd hlow_pref
      W.placeLeft W.imageLeft O.leftFace hsupp howners hlow_priv (Finset.card_fin _)
      O.mute hpred_lift
  have hcard5 : (Finset.univ : Finset (Fin (k + 5))).card = k + 4 + 1 := Finset.card_fin _
  obtain ⟨a, δ, hδw, _, hC_a, hg_a, hrefl_a⟩ := exists_actual_member_reflecting Rf'
  let D : SemScheme (k + 5) :=
    { scheme := FinalGateApex.scheme F hcard5
      rows := FinalGateApex.rows F O.grade_bound hcard5
      rows_coded := FinalGateApex.coded F O.grade_bound hcard5
        (F.coded O.coded (member_coded Rf')
          (fun _ hz => CanonicalCodingSupport.grid (k + 4) _ hz) hsupp)
      consistent := FinalGateApex.consistent F O.grade_bound hcard5 O.consistent
      bountiful := FinalGateApex.bountiful F O.grade_bound hcard5 hbount
      complete := FinalGateApex.complete F hcard5 a fun J hJ hg hne => by
        refine O.complete J (by rwa [O.plan] at hJ) ?_
        by_cases hs : J.1 = Finset.univ
        · exact Or.inr (by by_contra hn; exact hne (Prod.ext hs (by omega)))
        · exact Or.inl hs }
  let privFace : ExactSemanticFace W.leftRows D.rows :=
    FinalGateApex.properFace F O.grade_bound hcard5
      (fun h => hBne (Finset.Subset.antisymm (Finset.subset_univ _) h))
      (F.inheritedFace (Finset.subset_univ _) hBne O.leftFace)
  let reqFace : ExactSemanticFace W.rightRows D.rows :=
    FinalGateApex.properFace F O.grade_bound hcard5
      (fun h => hTne (Finset.Subset.antisymm (Finset.subset_univ _) h))
      (F.inheritedFace (Finset.subset_univ _) hTne O.rightFace)
  have hpriv_ord : StrictMono privFace.map :=
    (FinalGateApex.old_order F hcard5).comp (F.old_strictMono.comp O.left_order)
  have hreq_ord : StrictMono reqFace.map :=
    (FinalGateApex.old_order F hcard5).comp (F.old_strictMono.comp O.right_order)
  have hpplan : Plan.restrictPlan D.scheme.plan WholeDonorAttachment.privateScope =
      p₀'.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb) := by
    change Plan.restrictPlan O.carrier.plan _ = _; rw [O.plan]; exact W.planLeft
  have hrplan : Plan.restrictPlan D.scheme.plan (WholeDonorAttachment.donorScope e') =
      P.scheme.scheme.plan.image (Finset.image (onePointProj e')) := by
    change Plan.restrictPlan O.carrier.plan _ = _; rw [O.plan]; exact W.planRight
  have hvis := OrderedFaceRestriction.visible p₀'.scheme D.scheme Fin.castSuccEmb W.imageLeft hpplan
  have hvreq := OrderedFaceRestriction.visible P.scheme D.scheme (onePointProj e') W.imageRight hrplan
  have hres : D.restrictFace Fin.castSuccEmb hvis = p₀'.scheme :=
    LowOnlyPaddedLegal.restrict_eq_of_face p₀'.scheme D Fin.castSuccEmb W.imageLeft
      privFace hpriv_ord hpplan
  have hrreq : D.restrictFace (onePointProj e') hvreq = P.scheme :=
    LowOnlyPaddedLegal.restrict_eq_of_face P.scheme D (onePointProj e') W.imageRight
      reqFace hreq_ord hrplan
  have hpriv_toCell (d : Cell p₀'.scheme.scheme) :
      toCell D.scheme Fin.castSuccEmb hvis (SemScheme.castCell hres.symm d) = privFace.map d :=
    OrderedFaceRestriction.toCell_eq p₀'.scheme D.scheme D.rows Fin.castSuccEmb W.imageLeft
      privFace hpriv_ord hpplan d
  have hreq_toCell (d : Cell P.scheme.scheme) :
      toCell D.scheme (onePointProj e') hvreq (SemScheme.castCell hrreq.symm d) = reqFace.map d :=
    OrderedFaceRestriction.toCell_eq P.scheme D.scheme D.rows (onePointProj e') W.imageRight
      reqFace hreq_ord hrplan d
  -- Raw display `r` for `hM.bottomPattern`
  have hlower_a : RespectsSemanticsBelow O.rows (Finset.univ, k + 4) (fun d => δ (lower a d.1)) :=
    map_respects_of_short_or_reflecting (F.lower_lawful a) (fun d => d.2.2) hδw fun c =>
      (howners a c).imp id fun ho d => by
        obtain ⟨f, hfx⟩ := ho d
        change δ (lower a d.1) = ⊥ ↔ lower a d.1 = ⊥
        rw [hfx]; exact hrefl_a f
  let p_disp := fun d : F.carrier.below (Finset.univ, k + 4) => δ (F.source a d.1)
  let r_disp := FinalGateApex.display F hcard5 p_disp
  have hr_law : RespectsSemantics D.rows r_disp :=
    FinalGateApex.display_lawful F O.grade_bound hcard5
      (F.decoded_respects hsupp (member_short Rf')
        (fun _ hz => CanonicalFieldLayer.grid_short _ _ hz) a hδw hlower_a)
  let gateCell : Cell D.scheme := FinalGateApex.old F hcard5 (F.added a true)
  have hgate_top : r_disp gateCell = ⊤ :=
    (FinalGateApex.display_old F hcard5 p_disp (F.addedAt a true)).trans
      (by dsimp [p_disp]; rw [F.source_own_marked]; exact hg_a)
  obtain ⟨y, hy, q₁, ⟨h₁, hpat⟩, hcof, hev⟩ :=
    hM.bottomPattern u' p₀' hu' D ⟨hvis, hres⟩ r_disp hr_law fun d => by
      rw [ExtendsDomain.cellOf, hpriv_toCell d]
      refine ((FinalGateApex.display_old F hcard5 p_disp
        (oldAt Rf' O.rows (by simp) hsep lower hlow_law hlow_bnd hlow_pref
          (O.leftFace.map d) (O.grade_bound _))).trans ?_).trans (congrFun hRv' d)
      dsimp [p_disp]; rw [F.source_old]; exact (congrArg δ (hlow_priv a d)).trans (hC_a d)
  let qq : Cell D.scheme → ExtOrd := fun c => q₁.label (SemScheme.castCell h₁.symm c)
  have hqq : RespectsSemantics D.rows qq := by
    obtain ⟨s, _, _, hr⟩ := q₁; change s = D at h₁; subst h₁; exact hr
  let t' : S α.1 (k + 5) := ⟨D, qq, fun _ => q₁.label_bound _, hqq⟩
  have ht' : q₁ = t' := by
    obtain ⟨s₂, _, _, _⟩ := q₁; change s₂ = D at h₁; subst h₁
    exact StageType.ext rfl HEq.rfl
  rw [ht'] at hcof hev
  have hretain (d : Cell p₀'.scheme.scheme) : qq (privFace.map d) = Rf'.vact d := by
    have key := (typeMap_eq_some_iff_labels Fin.castSuccEmb t' p₀' hvis hres).mp hcof
      (SemScheme.castCell hres.symm d)
    exact (congrArg qq (hpriv_toCell d)).symm.trans
      (key.trans ((congrArg p₀'.label (Fin.ext rfl)).trans (congrFun hRv'.symm d)))
  have hgate_gr : D.scheme.grade gateCell = k + 4 :=
    congrArg Prod.snd ((FinalGateApex.old_index F hcard5 (F.added a true)).trans
      (F.added_index a true))
  have hgate_pos : qq gateCell ≠ ⊥ := fun hb =>
    top_ne_bot (hgate_top ▸ (hpat ⟨gateCell, Finset.subset_univ _, hgate_gr.le⟩).mp hb)
  have hy' : y ∉ Set.range (e'.trans u') := fun ⟨j, hj⟩ => hy ⟨e' j, hj⟩
  refine ⟨y, hy', t'.restrictFace (onePointProj e') hvreq, ?_, hrreq, fun d => ?_⟩
  · have h := hM.consistent (snoc u' y hy) t' (onePointProj e') hev
    rw [onePointProj_trans_snoc e' u' y hy hy'] at h
    exact h.trans (typeMap_eq_some (onePointProj e') t' hvreq)
  · have hcap := layer_capped_readback Rf' O.rows (by simp) hsep lower hlow_law hlow_bnd hlow_pref
      O.rightFace.map O.leftFace.map
      (fun x => congrArg Prod.snd (O.rightFace.index x))
      (fun x => congrArg Prod.snd (O.leftFace.index x))
      hlow_req hlow_priv
      (FinalGateApex.restrict_lawful F O.grade_bound hcard5 hqq)
      hretain a hgate_pos (SemScheme.castCell hrreq d)
    have key := GradeTailRestoration.cap_below hcap hδ
    have hd : toCell D.scheme (onePointProj e') hvreq d = reqFace.map (SemScheme.castCell hrreq d) :=
      (congrArg (toCell D.scheme (onePointProj e') hvreq) (Fin.ext rfl)).trans
        (hreq_toCell (SemScheme.castCell hrreq d))
    exact (congrArg (fun x => min (qq x) (ofOrd ν)) hd).trans
      (key.trans (congrArg (fun x => min x (ofOrd ν)) (congrFun hRp' _)))

end
end VaughtConjecture.Knight.OrdinaryModelReceiving
