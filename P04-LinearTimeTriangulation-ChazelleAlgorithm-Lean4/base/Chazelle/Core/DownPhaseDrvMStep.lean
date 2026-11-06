module

public import Chazelle.Core.DownPhaseMirrorExtract
public import Chazelle.Core.DownPhaseStepMain

/-!
# Down-phase driver math: one level for arbitrary region chains (both orientations)

`DownStep.downStep` is stated for the host chains `hostChain Q S R (g R)`.  The driver writes, for
each region `R`, a chain `C R` over its host (a list of increasing runs and points); when `Q` is
clockwise that chain is the mirror of the host chain of the mirrored region (F-D7).  The level
theorem only needs the extraction facts `ExtractOK Q S R (C R)` (`DownPhaseMirrorExtract`):

* `downStepG`: X1–X4 for all regions at once, for any region chains with `ExtractOK`;
* `downStepG_level`: the level instance (`d₀ = 4`, `D = D_H`, `γ₁ = gamma1 μ`);
* `extractOK_region`: `ExtractOK` for a chain of either orientation (the counterclockwise host
  chain, or a chain whose mirror is the host chain of the mirrored region).
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)
open DownHost DownStep Mir

variable {Q : Polygon} {S : Set (Set Point)}

/-- **The down step for arbitrary region chains** (X1–X4 for all regions at once): given, for
every region `R` of `S`, a chain `C R` with the extraction facts and a chord family `F R` of
`chainModel (C R)` of degree `≤ D`, `γ`-semigranular, the family `stepFam Q S F` is an interior
chord family of degree `≤ D + d₀`, `γ`-semigranular, whose new chords come from the `F R`. -/
theorem downStepG (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    {d₀ D γ : ℕ} (hdeg : (interiorModel Q).DegLe S d₀) (C : Set Point → Chain)
    (F : Set Point → Set (Set Point))
    (hEx : ∀ R ∈ (interiorModel Q).regions S, ExtractOK Q S R (C R))
    (hF : ∀ R ∈ (interiorModel Q).regions S,
      (chainModel (C R)).ChordFamily Q (F R) ∧ (chainModel (C R)).DegLe (F R) D ∧
        (chainModel (C R)).Semigranular (F R) γ) :
    (interiorModel Q).ChordFamily Q (stepFam Q S F) ∧
      (interiorModel Q).DegLe (stepFam Q S F) (D + d₀) ∧
      (interiorModel Q).Semigranular (stepFam Q S F) γ ∧
      stepFam Q S F \ S ⊆ ⋃ R ∈ (interiorModel Q).regions S, F R := by
  set I := interiorModel Q with hI
  set T := stepFam Q S F with hT
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hRfin : (I.regions S).Finite :=
    (hM.sys S hFam.2.1 hFam.1).regionsIn_finite hM.preconn hM.nonempty subset_rfl
  have hloc : ∀ R (hR : R ∈ I.regions S), ∀ c ∈ Extract.kept R (F R), c ∈ I.Adm ∧ c ∩ I.D ⊆ R :=
    fun R hR c hc => (hEx R hR).loc (hF R hR).1.2.1 c hc
  have hmem : ∀ c, c ∈ T → c ∈ S ∨ ∃ R ∈ I.regions S, c ∈ Extract.kept R (F R) := by
    rintro c (hc | hc)
    · exact Or.inl hc
    · obtain ⟨R, hR, hcR⟩ := mem_iUnion₂.1 hc
      exact Or.inr ⟨R, hR, hcR⟩
  have hkT : ∀ R ∈ I.regions S, Extract.kept R (F R) ⊆ T := fun R hR c hc =>
    Or.inr (mem_iUnion₂.2 ⟨R, hR, hc⟩)
  have hTfin : T.Finite :=
    hFam.1.union (hRfin.biUnion fun R hR => (hF R hR).1.1.subset fun c hc => hc.1)
  have hTadm : T ⊆ I.Adm := fun c hc => by
    rcases hmem c hc with hcS | ⟨R, hR, hcR⟩
    · exact hFam.2.1 hcS
    · exact (hloc R hR c hcR).1
  have hX1 : I.ChordFamily Q T := by
    refine ⟨hTfin, hTadm, fun c hc => ?_⟩
    rcases hmem c hc with hcS | ⟨R, hR, hcR⟩
    · exact hFam.2.2 c hcS
    · exact (hF R hR).1.2.2 c hcR.1
  have hX4 : T \ S ⊆ ⋃ R ∈ I.regions S, F R := by
    rintro c ⟨hc, hcS⟩
    rcases hmem c hc with h | ⟨R, hR, hcR⟩
    · exact absurd h hcS
    · exact mem_iUnion₂.2 ⟨R, hR, hcR.1⟩
  have hST : S ⊆ T := subset_union_left
  have key : ∀ V ∈ I.regions T, I.deg T V ≤ D + d₀ ∧ I.weight T V ≤ γ := by
    intro V hV
    obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
    have hVS : V ⊆ freeIn I.D S :=
      (Chazelle.Chain.regionsIn_subset hV).trans (Chazelle.Chain.freeIn_anti I.D hST)
    set R := connectedComponentIn (freeIn I.D S) v with hRdef
    have hR : R ∈ I.regions S := ⟨v, hVS hv, rfl⟩
    have hVR : V ⊆ R :=
      (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVS
    set G := S ∪ Extract.kept R (F R) with hG
    have hSG : S ⊆ G := subset_union_left
    have hGT : G ⊆ T := union_subset hST (hkT R hR)
    have hK : OutOther I.D S G T R := by
      intro c hc hcG
      rcases hmem c hc with hcS | ⟨R', hR', hcR'⟩
      · exact absurd (Or.inl hcS) hcG
      · refine ⟨R', hR', fun e => hcG (Or.inr (e ▸ hcR')), (hloc R' hR' c hcR').2⟩
    have hVG : V ∈ I.regions G := region_restrict hSG hGT hR hK hV hVR
    obtain ⟨U, hU, hVU⟩ := (hEx R hR).region hVG hVR
    have hsys := hM.sys T hTadm hTfin
    refine ⟨?_, ?_⟩
    · have hdegTG : I.deg T V = I.deg G V := by
        unfold Model.deg
        rw [exits_restrict hsys hST hGT hR hK hVR]
      rw [hdegTG]
      have h1 : I.deg G V ≤ (chainModel (C R)).deg (F R) U + I.deg S R :=
        (hEx R hR).deg (hF R hR).1.2.1 (hF R hR).1.1 hVR hVU
      have h2 := (hF R hR).2.1 U hU
      have h3 := hdeg R hR
      omega
    · rw [weight_restrict hM hTadm hTfin hSG hGT hR hK hV hVR]
      exact ((hEx R hR).weight (hF R hR).1.2.1 (hF R hR).1.1 hU hVR hVU).trans
        ((hF R hR).2.2 U hU)
  exact ⟨hX1, fun V hV => (key V hV).1, fun V hV => (key V hV).2, hX4⟩

end

end DownDrv

end Chazelle.Core
