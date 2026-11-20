/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.LawfulCapping
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.RootedKarp

/-! # Globally top-rigid cores: classification and the residual acquisition

The rigid-core reduction of newapproach17 new33 §§1–2, on the finite top-support criterion
(`TopSupport`) and finite-cover receiving (`FiniteCoverReceiving`):

* **Support extension through a literal coface** (`exists_admissible_extension`): an admissible
  top support of the root type extends to an admissible top support of any coface, with the old
  restriction unchanged — lower the root's other tops to a cap visible at the coface's point
  count (`respects_lower`), extend by bountifulness at that cap
  (`exists_respects_extends_capped`), and take the top set of the result.
* **A finite globally top-rigid core** (`RigidCore`): a tuple `B` such that on **every** actual
  finite cover of `B` (a realized tuple containing `B` as a coordinate face), every admissible
  top support of the cover's type containing all of `B`'s tops is the whole top set.  "Globally"
  is the quantification over all actual covers; the core is finite.  This is distinct from
  rigidity of one supplied finite context.
* **Classification** (`nonempty_iso_of_rigidCores_of_receiving`): two countable nonempty
  realizations at the same stage, with consistency, covering, finite-cut receiving and globally
  rigid cores of the same finite type, are isomorphic.  The common-chart chain is built
  by `nonempty_iso_of_restrictedCommonChartStepSupply` with the invariant that both cores are
  coordinate faces of the chart (`CoreChart`); one step covers the scheduled point by an actual
  finite labelled cover (initial-segment covering), receives that cover's type over the other
  side's chart by finite-cover receiving above every proper label, so the received type agrees
  with the cover's type off the tops; its top set is then an admissible support containing the
  core's tops (retained since the chart is received literally), and rigidity of the **source**
  model's core makes it the whole top set: the received type is the cover's type literally.
* **The residual acquisition** (`exists_flexible_cover_of_not_rigidCore`): without such a core,
  every actual root has an actual finite cover with a proper admissible support retaining the
  root's tops.

Nothing here constructs the three-shadow coupling of new34; that physical construction is out of
scope. -/

@[expose] public section

namespace VaughtConjecture.Knight.TopSupportRigidCore

open TypeTower StageType KnightRealization Value ExtOrd TopSupport CellScheme.restrictFace

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-! ## Support extension through a literal coface -/

/-! ## Globally top-rigid cores -/

/-- **A finite globally top-rigid core**: on every actual finite cover of `B` (a realized tuple
`C` with `B` as the coordinate face `e`), every admissible top support of the cover's type that
contains every top cell of the face `e` is the whole top set. -/
def RigidCore (R : KnightRealization α M) {k : ℕ} (B : Fin k ↪ M) : Prop :=
  ∀ {m : ℕ} (C : Fin m ↪ M) (c : S α.1 m), R.eval C = some c →
    ∀ (e : Fin k ↪ Fin m), e.trans C = B →
      ∀ H : Set (Cell c.scheme.scheme), Admissible c.scheme.rows c.label H →
        (∀ x : Cell c.scheme.scheme, c.scheme.scheme.scope x ⊆ Finset.univ.image e →
          c.label x = ⊤ → x ∈ H) →
        H = topSet c.label

/-- **The residual acquisition**: a root that is not a globally rigid core has an actual finite
cover with a proper admissible top support containing the root's tops. -/
theorem exists_flexible_cover_of_not_rigidCore {k : ℕ} {B : Fin k ↪ M} (h : ¬ RigidCore R B) :
    ∃ (m : ℕ) (C : Fin m ↪ M) (c : S α.1 m), R.eval C = some c ∧
      ∃ (e : Fin k ↪ Fin m), e.trans C = B ∧
        ∃ H : Set (Cell c.scheme.scheme), Admissible c.scheme.rows c.label H ∧
          (∀ x : Cell c.scheme.scheme, c.scheme.scheme.scope x ⊆ Finset.univ.image e →
            c.label x = ⊤ → x ∈ H) ∧ H ≠ topSet c.label := by
  by_contra hcon
  apply h
  intro m C c hc e he H hH htops
  by_contra hne
  exact hcon ⟨m, C, c, hc, e, he, H, hH, htops, hne⟩

/-! ## Classification of models with globally rigid cores -/

section Classification

variable {M₁ M₂ : Type w} {R₁ : KnightRealization α M₁} {R₂ : KnightRealization α M₂}

/-- The chart invariant: both cores are coordinate faces of the common chart, at the same
coordinates. -/
def CoreChart {k : ℕ} (B₁ : Fin k ↪ M₁) (B₂ : Fin k ↪ M₂)
    (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂)) : Prop :=
  ∃ e : Fin k ↪ Fin nd.arity, e.trans nd.tuple₁ = B₁ ∧ e.trans nd.tuple₂ = B₂

/-- A common chart with the sides exchanged. -/
def swapNode (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂)) :
    CommonChartNode (A₁ := R₂) (A₂ := R₁) :=
  ⟨nd.arity, nd.tuple₂, nd.tuple₁, nd.type, nd.eval₂, nd.eval₁⟩

theorem coreChart_swapNode {k : ℕ} {B₁ : Fin k ↪ M₁} {B₂ : Fin k ↪ M₂}
    {nd : CommonChartNode (A₁ := R₁) (A₂ := R₂)} (h : CoreChart B₁ B₂ nd) :
    CoreChart B₂ B₁ (swapNode nd) := by
  obtain ⟨e, h₁, h₂⟩ := h
  exact ⟨e, h₂, h₁⟩

/-- **One forth step**: a common chart containing both cores extends to one containing a
scheduled point of the first model, by covering it in the first model, receiving the cover's
type over the second side above every proper label, and reading the tops back from rigidity of
the first model's core. -/
theorem exists_step_left_of_receiving (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ :
    R₁.IsInitialSegmentCovering)
    (hcons₂ : R₂.IsExactParentConsistent) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
    {B₂ : Fin k ↪ M₂} (r₁ : RigidCore R₁ B₁) (nd : CommonChartNode (A₁ := R₁) (A₂ := R₂))
    (hnd : CoreChart B₁ B₂ nd) (x : M₁) :
    ∃ (next : CommonChartNode (A₁ := R₁) (A₂ := R₂)) (emb : Fin nd.arity ↪ Fin next.arity),
      emb.trans next.tuple₁ = nd.tuple₁ ∧ emb.trans next.tuple₂ = nd.tuple₂ ∧
      (∃ i, next.tuple₁ i = x) ∧ CoreChart B₁ B₂ next := by
  obtain ⟨e, he₁, he₂⟩ := hnd
  by_cases hx : x ∈ Set.range nd.tuple₁
  · obtain ⟨i, hi⟩ := hx
    exact ⟨nd, Function.Embedding.refl _, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, ⟨i, hi⟩, e, he₁, he₂⟩
  -- cover `nd.tuple₁ ⌢ x` in the first model
  obtain ⟨j, s, hs, hsome⟩ := hcov₁ (snoc nd.tuple₁ x hx)
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
  set f : Fin nd.arity ↪ Fin (nd.arity + 1 + j) := Fin.castSuccEmb.trans (Fin.castAddEmb j)
    with hfdef
  have hfs : f.trans s = nd.tuple₁ := by
    rw [hfdef, Function.Embedding.trans_assoc, hs, castSuccEmb_trans_snoc]
  have hfP : typeMap f P = some nd.type := by
    have h := hcons₁ s P f hP
    rw [hfs, nd.eval₁] at h
    exact h.symm
  -- receive the cover's type over the second side, above every proper label
  obtain ⟨δ, hδbot, hδα, hδgt⟩ := exists_proper_cutoff P
  obtain ⟨u, Q', hfu, hu, h, hagree⟩ := FiniteCoverReceiving.finiteCoverReceiving_of_receiving
    hcons₂ hFC₂ P f
    nd.tuple₂ nd.type hfP nd.eval₂ δ hδbot hδα
  let Q'' : Cell P.scheme.scheme → ExtOrd := fun d => Q'.label (SemScheme.castCell h.symm d)
  have hQ'' : RespectsSemantics P.scheme.rows Q'' := respects_castCell h Q'.respects
  let T' : S α.1 (nd.arity + 1 + j) := ⟨P.scheme, Q'', fun d => Q'.label_bound _, hQ''⟩
  have hT' : Q' = T' := StageType.eq_of_label h (fun _ => rfl)
  have hoff : ∀ d, P.label d ≠ ⊤ → Q'' d = P.label d := fun d hd =>
    label_eq_of_agree h hagree d (hδgt d hd)
  -- the chart is received literally: both types restrict to `nd.type` along `f`
  have hvf : Finset.univ.image f ∈ P.scheme.scheme.plan :=
    (typeMap_isSome_iff f P).mp (by rw [hfP]; rfl)
  have hsP : P.scheme.restrictFace f hvf = nd.type.scheme :=
    congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some f P hvf).symm.trans hfP))
  have hPr := (typeMap_eq_some_iff_labels f P nd.type hvf hsP).mp hfP
  have hT'f : typeMap f T' = some nd.type := by
    have h := hcons₂ u Q' f hu
    rw [hfu, nd.eval₂, hT'] at h
    exact h.symm
  have hQr := (typeMap_eq_some_iff_labels f T' nd.type hvf hsP).mp hT'f
  have hroot : ∀ i, Q'' (toCell P.scheme.scheme f hvf i) =
      P.label (toCell P.scheme.scheme f hvf i) := fun i => (hQr i).trans (hPr i).symm
  -- rigidity of the first model's core on the cover `s`
  set e' : Fin k ↪ Fin (nd.arity + 1 + j) := e.trans f with he'def
  have he's : e'.trans s = B₁ := by rw [he'def, Function.Embedding.trans_assoc, hfs, he₁]
  have hQP : Q'' = P.label := by
    refine eq_of_unique_admissible hQ''
      (TB := {y | P.scheme.scheme.scope y ⊆ Finset.univ.image e' ∧ P.label y = ⊤}) ?_ hoff ?_
    · intro H hTB hH
      exact r₁ s P hP e' he's H hH (fun y hy hytop => hTB ⟨hy, hytop⟩)
    · rintro y ⟨hy, hytop⟩
      have hyf : P.scheme.scheme.scope y ⊆ Finset.univ.image f := hy.trans fun z hz => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image_of_mem f (Finset.mem_univ _)
      obtain ⟨i, rfl⟩ := exists_toCell_eq (D := P.scheme.scheme) (f := f) (hr := hvf) hyf
      rw [hroot i]
      exact hytop
  have hQ'P : Q' = P := by
    rw [hT']
    exact StageType.eq_of_label rfl (fun d => congrFun hQP d)
  refine ⟨⟨nd.arity + 1 + j, s, u, P, hP, by rw [← hQ'P]; exact hu⟩, f, hfs, hfu,
    ⟨Fin.castAddEmb j (Fin.last nd.arity), ?_⟩, e', he's, ?_⟩
  · have hlast := congrArg (fun g : Fin (nd.arity + 1) ↪ M₁ => g (Fin.last nd.arity)) hs
    simpa only [Function.Embedding.trans_apply, snoc_apply_last] using hlast
  · rw [he'def, Function.Embedding.trans_assoc, hfu, he₂]

/-- The chart invariant is preserved by density on both sides. -/
theorem restrictedStepSupply_of_receiving (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ :
    R₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving R₁) (hcons₂ : R₂.IsExactParentConsistent)
    (hcov₂ : R₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
    {B₂ : Fin k ↪ M₂} (r₁ : RigidCore R₁ B₁) (r₂ : RigidCore R₂ B₂) :
    RestrictedCommonChartStepSupply (A₁ := R₁) (A₂ := R₂) (CoreChart B₁ B₂) := by
  intro nd hnd z
  rcases z with x | y
  · obtain ⟨next, emb, h₁, h₂, hx, hgood⟩ := exists_step_left_of_receiving hcons₁ hcov₁ hcons₂
      hFC₂ r₁ nd hnd x
    exact ⟨⟨⟨next, emb, h₁, h₂, fun _ hx' => (Sum.inl.inj hx') ▸ hx,
      fun _ hy => absurd hy Sum.inl_ne_inr⟩, hgood⟩⟩
  · obtain ⟨next, emb, h₁, h₂, hy, hgood⟩ :=
      exists_step_left_of_receiving hcons₂ hcov₂ hcons₁ hFC₁ r₂ (swapNode nd) (coreChart_swapNode
        hnd) y
    exact ⟨⟨⟨swapNode next, emb, h₂, h₁, fun _ hx => absurd hx Sum.inr_ne_inl,
      fun _ hy' => (Sum.inr.inj hy') ▸ hy⟩, coreChart_swapNode hgood⟩⟩

/-- **Root-preserving classification**: two countable models at the same stage with globally
rigid cores of the same finite type are isomorphic by an isomorphism carrying one core onto the
other coordinatewise. -/
theorem exists_iso_of_rigidCores_of_receiving [Countable M₁] [Countable M₂] [Nonempty M₁]
    [Nonempty M₂] (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ : R₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving R₁) (hcons₂ : R₂.IsExactParentConsistent)
    (hcov₂ : R₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
      {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : ∃ e : R₁.Iso R₂, ∀ i, e.1 (B₁ i) = B₂ i :=
  exists_iso_of_restrictedCommonChartStepSupply hcons₁ hcons₂ (CoreChart B₁ B₂)
    ⟨k, B₁, B₂, b, h₁, h₂⟩
    ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _, Function.Embedding.refl_trans _⟩
    (restrictedStepSupply_of_receiving hcons₁ hcov₁ hFC₁ hcons₂ hcov₂ hFC₂ r₁ r₂)

/-- **Classification**: two countable models at the same stage with globally rigid cores of the
same finite type are isomorphic. -/
theorem nonempty_iso_of_rigidCores_of_receiving [Countable M₁] [Countable M₂] [Nonempty M₁]
    [Nonempty M₂] (hcons₁ : R₁.IsExactParentConsistent) (hcov₁ : R₁.IsInitialSegmentCovering)
    (hFC₁ : FiniteCutReceiving R₁) (hcons₂ : R₂.IsExactParentConsistent)
    (hcov₂ : R₂.IsInitialSegmentCovering) (hFC₂ : FiniteCutReceiving R₂) {k : ℕ} {B₁ : Fin k ↪ M₁}
      {B₂ : Fin k ↪ M₂} {b : S α.1 k}
    (h₁ : R₁.eval B₁ = some b) (h₂ : R₂.eval B₂ = some b) (r₁ : RigidCore R₁ B₁)
    (r₂ : RigidCore R₂ B₂) : Nonempty (R₁.Iso R₂) :=
  let ⟨e, _⟩ := exists_iso_of_rigidCores_of_receiving hcons₁ hcov₁ hFC₁ hcons₂ hcov₂ hFC₂ h₁ h₂ r₁
    r₂
  ⟨e⟩

end Classification

end VaughtConjecture.Knight.TopSupportRigidCore
