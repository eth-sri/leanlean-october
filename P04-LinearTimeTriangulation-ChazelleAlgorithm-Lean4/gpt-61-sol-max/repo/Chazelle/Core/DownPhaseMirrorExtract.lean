module

public import Chazelle.Core.DownPhaseMirrorChain
public import Chazelle.Core.DownPhaseMirrorInterior
public import Chazelle.Core.DownPhaseDrvOrient

/-!
# Mirror symmetry (F-D7), part 7: extraction for both orientations of `Q`

The extraction theorems X1–X3 (`DownPhaseExtractMain`) are proved for the host chain
`hostChain Q S R g` (host points in increasing key order of the interior walk of `Q`).  When `Q`
is clockwise, the interior walk runs in decreasing index order, and a host written with
increasing runs (the only runs `Host.poly` has) is the host of the *mirrored* region, mirrored
back.  This file packages the extraction facts in an orientation-free predicate and transports
it through the mirror isomorphisms `modelMir_interior`, `modelMir_chain`:

* `ExtractOK Q S R C`: the extraction facts (X1 localization, regions, X2 weights, X3 degrees)
  for the chain model of an arbitrary chain `C`;
* `extractOK_host`: they hold for `C = hostChain Q S R g` (`g` a chord gap);
* `extractOK_of_mir`: they transfer from the mirrored data `(Q.mir, mirF S, mir '' R, C.mir)`
  to `(Q, S, R, C)`;
* `extractOK_cw`: hence they hold for every chain `C` whose mirror is the host chain of the
  mirrored region (`C.mir = hostChain Q.mir (mirF S) (mir '' R) g`);
* `kept_iff_host_cw`: the kept-chord test (X-R1) in that case, stated on `C.P` itself: at the
  right end `(b, y)` of the chord, the direction `(-1, 0)` lies in the sector from the next to the
  previous host point (the region lies to the right of the host walk);
* `ctx_mir`: the region hypotheses transfer to the mirror image.
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set
open Chazelle.Chain (sidePt sidePrev sideNext sideCcw IsHChordIn)
open Chazelle.Visibility (hseg)
open DownHost Mir

/-! ## The orientation-free extraction predicate -/

/-- **The extraction facts for the chain `C` of the region `R` of `S`**: for every family `F₁` of
admissible chords of `chainModel C`, the kept chords `kept R F₁` (those meeting `R`) are
admissible chords of the interior of `Q` meeting its domain only in `R` (X1); every region
`V ⊆ R` of `S ∪ kept R F₁` lies in a region `U` of `F₁`; and for `V ⊆ R`, `V ⊆ U`, `U` a region of
`F₁`, the weight of `V` is at most that of `U` (X2) and its degree at most that of `U` plus that
of `R` (X3). -/
structure ExtractOK (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (C : Chain) : Prop where
  loc : ∀ {F₁ : Set (Set Point)}, F₁ ⊆ (chainModel C).Adm → ∀ c ∈ Extract.kept R F₁,
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ R
  region : ∀ {F₁ : Set (Set Point)} {V : Set Point},
    V ∈ (interiorModel Q).regions (S ∪ Extract.kept R F₁) → V ⊆ R →
      ∃ U ∈ (chainModel C).regions F₁, V ⊆ U
  weight : ∀ {F₁ : Set (Set Point)}, F₁ ⊆ (chainModel C).Adm → F₁.Finite →
    ∀ {U : Set Point}, U ∈ (chainModel C).regions F₁ → ∀ {V : Set Point}, V ⊆ R → V ⊆ U →
      (interiorModel Q).weight (S ∪ Extract.kept R F₁) V ≤ (chainModel C).weight F₁ U
  deg : ∀ {F₁ : Set (Set Point)}, F₁ ⊆ (chainModel C).Adm → F₁.Finite →
    ∀ {U V : Set Point}, V ⊆ R → V ⊆ U →
      (interiorModel Q).deg (S ∪ Extract.kept R F₁) V ≤
        (chainModel C).deg F₁ U + (interiorModel Q).deg S R

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The extraction facts for the host chain** (counterclockwise orientation of the host). -/
theorem extractOK_host (X : Extract.Ctx Q S R) {g : ℕ} (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) :
    ExtractOK Q S R (hostChain Q S R g X.three) where
  loc := fun hF₁ _c hc => Extract.kept_local X hg hgc hF₁ hc
  region := fun hV hVR => Extract.exists_chain_region X hV hVR
  weight := fun {_} hF₁ hfin {_} hU {_} hVR hVU => Extract.weight_kept X hg hgc hF₁ hfin hU hVR hVU
  deg := fun {_} hF₁ hfin {_ _} hVR hVU => Extract.deg_kept X hg hgc hF₁ hfin hVR hVU

/-! ## Transport through the mirror -/

/-- **Kept chords of the mirrored family** are the mirrored kept chords. -/
theorem kept_mir (R : Set Point) (F : Set (Set Point)) :
    mirF (Extract.kept R F) = Extract.kept (mir '' R) (mirF F) := by
  ext c
  rw [mem_mirF]
  unfold Extract.kept
  simp only [mem_ofPred_eq, mem_mirF]
  have e : mir '' (c ∩ mir '' R) = mir '' c ∩ R := by
    rw [image_inter mir_injective, image_mir_image_mir]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← e] at h2
    exact h2.of_image
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← e]; exact h2.image _⟩

/-- The mirrored family after extraction. -/
theorem mirF_step (S : Set (Set Point)) (R : Set Point) (F : Set (Set Point)) :
    mirF (S ∪ Extract.kept R F) = mirF S ∪ Extract.kept (mir '' R) (mirF F) := by
  rw [mirF_union, kept_mir]

/-- **The region hypotheses of the mirror image.** -/
theorem ctx_mir (X : Extract.Ctx Q S R) : Extract.Ctx Q.mir (mirF S) (mir '' R) := by
  have hI := modelMir_interior X.hQ
  refine ⟨mir_simple Q X.hQ, (hI.chordFamily Q S).2 X.hFam, mirF_nonempty.2 X.hne, ?_⟩
  rw [hI.regions]
  exact image_mem_mirF.2 X.hR

/-- **Extraction transfers from the mirror image.** -/
theorem extractOK_of_mir {C : Chain} (hQ : Q.Simple) (hP : C.P.Simple)
    (h : ExtractOK Q.mir (mirF S) (mir '' R) C.mir) : ExtractOK Q S R C := by
  have hI := modelMir_interior hQ
  have hC := modelMir_chain C hP
  have hadm : ∀ {F₁ : Set (Set Point)}, F₁ ⊆ (chainModel C).Adm →
      mirF F₁ ⊆ (chainModel C.mir).Adm := fun hF₁ => by
    rw [hC.Adm]; exact mirF_subset.2 hF₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F₁ hF₁ c hc
    have hc' : mir '' c ∈ Extract.kept (mir '' R) (mirF F₁) := by
      rw [← kept_mir]; exact image_mem_mirF.2 hc
    obtain ⟨h1, h2⟩ := h.loc (hadm hF₁) _ hc'
    rw [hI.Adm, image_mem_mirF] at h1
    refine ⟨h1, fun x ⟨hxc, hxD⟩ => ?_⟩
    have := h2 ⟨mem_image_of_mem mir hxc, by rw [hI.D]; grind⟩
    grind [mem_image_mir, mir_mir]
  · intro F₁ V hV hVR
    have hV' : mir '' V ∈ (interiorModel Q.mir).regions (mirF S ∪ Extract.kept (mir '' R)
        (mirF F₁)) := by
      rw [← mirF_step, hI.regions]; exact image_mem_mirF.2 hV
    obtain ⟨U', hU', hVU'⟩ := h.region hV' (image_mono hVR)
    rw [hC.regions] at hU'
    refine ⟨mir '' U', mem_mirF.1 hU', ?_⟩
    rw [← image_mir_image_mir V]
    grind
  · intro F₁ hF₁ hfin U hU V hVR hVU
    have hU' : mir '' U ∈ (chainModel C.mir).regions (mirF F₁) := by
      rw [hC.regions]; exact image_mem_mirF.2 hU
    have := h.weight (hadm hF₁) (mirF_finite.2 hfin) hU' (image_mono hVR) (image_mono hVU)
    rwa [← mirF_step, hI.weight, hC.weight] at this
  · intro F₁ hF₁ hfin U V hVR hVU
    have := h.deg (hadm hF₁) (mirF_finite.2 hfin) (U := mir '' U) (image_mono hVR)
      (image_mono hVU)
    rwa [← mirF_step, hI.deg, hC.deg, hI.deg] at this

/-! ## The kept test for a clockwise host -/

/-! ## Host descriptions of the mirrored polygon -/

end

end DownDrv

end Chazelle.Core
