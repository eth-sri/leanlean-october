/- Copyright (c) 2026 Cameron Freer. Released under Apache 2.0. -/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient
public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.TopSupport
public import VaughtConjecture.Knight.AlignedCutEncoding

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalOwnerLift

open CoatomBoundaryExtension Transform Value ExtOrd SharpWitnessComposition CanonicalPairedInverse

open OwnerLocalEndpoint CanonicalPairedProfiles

noncomputable section

private theorem endpoint_grid {X : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (d : X) (hd : a d ≠ ⊥) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧
      endpoint j (a d) = CanonicalPairedInverse.grid j b := by
  rcases mem_codedAlphabet_iff.mp (inventory_coded X j ha d) with hb | ⟨b, n, hb, _, he⟩
  · lia
  have hn : n ≤ j := by
    rcases inventory_short X j ha d with hz | ht | ⟨v, hv, hshort⟩
    · lia
    · exact (ha.2 d ht).elim
    · have heq := ofOrd_inj.mp (he.symm.trans hv)
      simpa [← heq, finitePart_mul_add] using hshort
  refine ⟨b, hb, ?_⟩
  rcases lt_or_eq_of_le hn with hn | hn
  · rw [endpoint, he, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rwa [finitePart_mul_add]), ordinalReplace, limitPart_mul_add]
    rfl
  · rw [endpoint, he, hn, extVisibilityReplace_of_le_finitePart
      (by simp [finitePart_mul_add, le_refl])]
    rfl

private theorem local_endpoint_grid {X Y : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (occ : Y → X)
    {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j (a ∘ occ) τ γ h) (hpos : ⊥ < h) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧ h = CanonicalPairedInverse.grid j b := by
  obtain ⟨d, _, hd⟩ := H.exists_witness
  have hbot : a (occ d) ≠ ⊥ := by
    intro hb
    aesop
  obtain ⟨b, hb, he⟩ := endpoint_grid ha (occ d) hbot
  grind

/-- Complete the old owner boundary, preserving the cut, and decode its
extension in the new source layer. The layer supplies only the source chart
and extension of bounded prefixes. -/
private theorem exists_lift {ι : Type*} [DecidableEq ι] {A : Finset ι} {D E : CellScheme A}
    {sem : Semantics D} {rows : Semantics E} {k : ℕ} {X : Type*} [Fintype X]
    (occ : Cell D → X) (old : Cell D → E.below (A, k))
    (hg : ∀ d : Cell D, D.grade d ≤ k)
    (c : Cell D) (hc : D.grade c = k)
    {p : D.below (D.cell c) → ExtOrd} (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : E.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow rows (A, k) q)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ = min (q (old e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (W : CutCover sem (D.cell c) k)
    {a : X → ExtOrd} (ha : a ∈ CanonicalPairedProfiles.inventory X k)
    (haLaw : RespectsSemantics sem (a ∘ occ))
    (s : E.below (A, k) → ExtOrd)
    (hshort : ∀ d, Short k (s d)) (hread : ∀ d, s (old d) = a (occ d))
    {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop k) τ) (hbound : ∀ z, τ z ≤ γ)
    (hambient : ∀ d, τ (s d) = min (q d) γ)
    (extend : ∀ {v : Cell D → ExtOrd} {B : ℕ},
      RespectsSemantics sem v → (∀ d, v d ≠ ⊤) → B ≤ 2 * Fintype.card X + 1 →
      (∀ d, min (a (occ d)) (grid k B) = min (v d) (grid k B)) →
      ∃ w, RespectsSemanticsBelow rows (A, k) w ∧ (∀ d, w (old d) = v d) ∧
        ∀ d, min (w d) (grid k B) = min (s d) (grid k B)) :
    ∃ r, RespectsSemanticsBelow rows (A, k) r ∧
      (∀ e : D.below (D.cell c), r (old e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c))
  subst k
  let pp := fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)
  have hface (e : D.below (D.cell c)) : τ (a (occ e.1)) = min (p e) γ :=
    (congrArg τ (hread e.1).symm).trans ((hambient (old e.1)).trans (hag e).symm)
  obtain ⟨h, ρ, δ, f, H, hhpos, hvis, _, hroom, hρ, hγδ, hδM, hδvis,
      hρh, hf, hfcap, hfeq, _, hr, hretune⟩ :=
    OwnerLocalAlignment.exists_coded_face c (haLaw.toBelow (D.cell c)) hp
      (fun e => inventory_short X (D.grade c) ha (occ e.1))
      (Fintype.card X) (inventory_bound X (D.grade c) ha (occ c))
      hτ hγ (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  obtain ⟨B, hB, hBeq⟩ := local_endpoint_grid ha (fun e : D.below (D.cell c) => occ e.1) H hhpos
  change f = AlignedCutEncoding.encode (fun e => a (occ e.1)) pp
    (D.grade c) (2 * Fintype.card X + 1) h δ at hfeq
  obtain ⟨u, hu, hucap, huface⟩ := W.extend hg haLaw hf hvis (fun d => (hfcap d).symm)
  have huEq (d : D.below (D.cell c)) : u d.1 = f d := huface d
  let S := Finset.univ.sup fun e => extVisibilityReplace (f e) (D.grade c) (D.grade c)
  let C := max h S
  have hhC : h ≤ C := le_max_left _ _
  have hfC (d : D.below (D.cell c)) : u d.1 ≤ C := by
    rw [huEq]
    exact (TopSupport.le_evr_self _ _).trans ((Finset.le_sup (Finset.mem_univ d) : _ ≤ S).trans (le_max_right _ _))
  have hCt : C ≠ ⊤ := ne_of_lt (max_lt (hroom.trans (ofOrd_lt_top _)) (by
    apply (Finset.sup_lt_iff bot_lt_top).mpr
    intro e _
    apply lt_top_iff_ne_top.mpr
    apply TopSupport.evr_ne_top
    rw [hfeq]
    exact AlignedCutEncoding.encode_ne_top hroom e))
  let v : Cell D → ExtOrd := fun d => min (u d) C
  have hv : RespectsSemantics sem v := ((hu.toBelow (A, D.grade c)).cap
    (TopSupport.selfVis_max_of hvis (TopSupport.selfVis_sup_evr _ _ _))).toRespects
      (fun d => ⟨D.scope_subset d, hg d⟩)
  have hvt (d : Cell D) : v d ≠ ⊤ := fun hd => hCt (min_eq_top.mp hd).2
  have hvcap (d) : min (v d) h = min (a (occ d)) h := by
    rw [show v d = min (u d) C from rfl, min_assoc, min_eq_right hhC, hucap]
    rfl
  obtain ⟨w, hw, hwold, hwcap⟩ := extend hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact (hvcap d).symm)
  refine AlignedCutEncoding.decode_lift s pp (fun e => old e.1) hw hq
    (fun d => d.2.2) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hBeq ▸ hwcap d) ?_ ?_ ?_
  · intro d
    exact (hretune _ (hshort d)).trans ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    simpa only [pp, min_assoc, min_eq_right hδM, hread, Function.comp_apply] using hr e
  · have he : (s ∘ fun e : D.below (D.cell c) => old e.1) = fun e => a (occ e.1) :=
      funext fun e => hread e.1
    intro e
    rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huEq, hfeq, he]

/-- Capped lifting at an active owner of the new grade. -/
abbrev Capped {ι : Type*} [DecidableEq ι] {A : Finset ι} {D E : CellScheme A} {k : ℕ}
    (sem : Semantics D) (rows : Semantics E) (old : Cell D → E.below (A, k)) : Prop :=
  ∀ (c : Cell D), D.grade c = k →
    ∀ {p : D.below (D.cell c) → ExtOrd}, RespectsSemanticsBelow sem (D.cell c) p →
    ∀ {q : E.below (A, k) → ExtOrd}, RespectsSemanticsBelow rows (A, k) q →
    ∀ {γ : ExtOrd}, SelfVis k γ → γ ≠ ⊥ →
    (∀ e : D.below (D.cell c), min (p e) γ = min (q (old e.1)) γ) →
    γ < p ⟨c, GradedLe.refl _⟩ →
    CutCover sem (D.cell c) k →
    ∃ r, RespectsSemanticsBelow rows (A, k) r ∧
      (∀ e : D.below (D.cell c), r (old e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ

/-- A scoped source layer need only supply bounded-prefix repair on its old occurrences. -/
theorem of_layer {ι : Type*} [DecidableEq ι] {A : Finset ι} {D E : CellScheme A}
    {sem : Semantics D} {k : ℕ} {X : Type*} [Fintype X]
    (F : ScopedSourcePrefixLayer.Data E k X) (occ : Cell D → X)
    (e : CanonicalFieldLayer.Profile sem k X occ ≃ SourcePrefixLayer.Controller E k)
    (old : Cell D → E.below (A, k))
    (hg : ∀ d, D.grade d ≤ k) (hold : ∀ d, E.grade (old d).1 = D.grade d)
    (hshort : ∀ a d, Short k (F.profile (e a) d))
    (hread : ∀ a d, F.profile (e a) (old d).1 = a.val (occ d))
    (extend : ∀ a {v : Cell D → ExtOrd} {B : ℕ},
      RespectsSemantics sem v → (∀ d, v d ≠ ⊤) → B ≤ 2 * Fintype.card X + 1 →
      (∀ d, min (a.val (occ d)) (grid k B) = min (v d) (grid k B)) →
      ∃ w : Cell E → ExtOrd, RespectsSemanticsBelow F.rows (A, k) (fun d => w d.1) ∧
        (∀ d, w (old d).1 = v d) ∧ ∀ d, min (w d) (grid k B) = min (F.profile (e a) d) (grid k B)) :
    Capped sem F.rows old := by
  intro c hc p hp q hq γ hγ hb hag hpc W
  have hactive := (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  let seed := CanonicalFieldLayer.encode sem k X occ hg (p := fun _ => ⊥)
    (RespectsSemantics.bot sem) (fun _ => bot_ne_top)
  obtain ⟨s, τ, hτ, hbound, hr⟩ := ScopedSourcePrefixAmbient.exists_active_source F (e seed) hq
    (old c) ((hold c).trans hc) hγ hactive
  let a := e.symm s
  have he : e a = s := e.apply_symm_apply s
  refine exists_lift occ old hg c hc hp hq hγ hb hag hpc W
    a.property.2 a.property.1 (fun d => F.profile (e a) d.1)
    (fun d => hshort a d.1) (hread a) hτ hbound (he.symm ▸ hr) ?_
  intro v B hv htop hB hpre
  obtain ⟨w, hw, hv, hcap⟩ := extend a hv htop hB hpre
  exact ⟨fun d => w d.1, hw, hv, fun d => hcap d.1⟩

end

end VaughtConjecture.Knight.CanonicalOwnerLift
