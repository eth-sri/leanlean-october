module

public import Chazelle.Core.FactsFullDegInt

/-!
# Down-phase driver, B-M1: a missing vertex chord lies in one region

At the base of the down phase, the driver completes the interior family `S` by the vertex chords
it misses, region by region.  **B-M1** (`full_in_region`): a vertex chord of `Q` not in `S` meets
no chord of `S` inside the domain (two interior chords sharing a domain point are equal), so its
domain part lies in one region of `S`.  Design: `docs/design-downphase-driver.md` §4.4.
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set
open Chazelle.Chain (IsHChordIn freeIn regionsIn)
open Chazelle.Visibility (hseg chords)

variable {Q : Polygon} {S : Set (Set Point)}

/-- **B-M1: a vertex chord not in `S` lies in one region of `S`.** -/
theorem full_in_region (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    {c : Set Point} (hc : c ∈ chords Q) (hcS : c ∉ S) :
    ∃ R ∈ (interiorModel Q).regions S, c ∩ (interiorModel Q).D ⊆ R ∧
      (c ∩ (interiorModel Q).D).Nonempty := by
  set D := (interiorModel Q).D with hD
  have hHC := FullDegInt.hc_full hQ hc
  obtain ⟨y, a, b, hch, rfl⟩ := hHC
  have hab := hch.lt
  -- the domain part of the chord is its open part
  have hopen : hseg y a b ∩ D ⊆ (fun x : ℝ => ((x, y) : Point)) '' Ioo a b := by
    rintro w ⟨hw, hwD⟩
    obtain ⟨h1, h2⟩ := FullDegInt.open_of_mem hch hw hwD
    exact ⟨w.1, ⟨h1, h2⟩, Prod.ext rfl hw.1.symm⟩
  have hsubD : (fun x : ℝ => ((x, y) : Point)) '' Ioo a b ⊆ hseg y a b ∩ D := by
    rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨rfl, h1.le, h2.le⟩, hch.open_mem x h1 h2⟩
  -- it avoids the chords of `S`
  have hfree : (fun x : ℝ => ((x, y) : Point)) '' Ioo a b ⊆ freeIn D S := by
    intro w hw
    obtain ⟨hwc, hwD⟩ := hsubD hw
    refine ⟨hwD, ?_⟩
    rintro ⟨e, he, hwe⟩
    obtain ⟨y', a', b', hch', rfl⟩ := hFam.2.1 he
    have := FullDegInt.eq_of_common ⟨y, a, b, hch, rfl⟩ ⟨y', a', b', hch', rfl⟩ hwc hwe hwD
    exact hcS (this ▸ he)
  have hpre : IsPreconnected ((fun x : ℝ => ((x, y) : Point)) '' Ioo a b) :=
    isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => ((x, y) : Point)).continuousOn
  set z₀ : Point := ((a + b) / 2, y)
  have hz₀ : z₀ ∈ (fun x : ℝ => ((x, y) : Point)) '' Ioo a b :=
    ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  refine ⟨connectedComponentIn (freeIn D S) z₀, ⟨z₀, hfree hz₀, rfl⟩, ?_, ⟨z₀, hsubD hz₀⟩⟩
  exact hopen.trans (hpre.subset_connectedComponentIn hz₀ hfree)

end

end DownDrv

end Chazelle.Core
