module

public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF RAF.Polymer RAF.Concrete

/-- A RAF in a bounded ambient closure has a bounded catalyst for a seed
reaction. This is deterministic and uses no conditional independence. -/
theorem bounded_raf_has_seed_catalyst {n K : ℕ} (ω : AmbientCoord n → Prop)
    (hbounded : ∀ x ∈ temporaryReactionClosure 2 (catalystActive ω Finset.univ),
      molLength x ≤ K)
    (hraf : ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S) :
    ∃ x : Molecule n, ∃ r : Reaction n,
      molLength x ≤ K ∧ RevSeedReaction (binaryPolymerCRS n 2) r ∧ ω (x,r) := by
  obtain ⟨S, hne, hfg, hcat⟩ := hraf
  obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated _ S hne hfg
  obtain ⟨x, k, hx, hxr⟩ := hcat r hr
  exact ⟨x, r, hbounded x (temporaryReactionClosure_mono
    (fun _ hr' => let ⟨y, _, _, hy⟩ := hcat _ hr'; (mem_catalystActive ω Finset.univ _).mpr ⟨y, Finset.mem_univ _, hy⟩)
    ((mem_temporaryReactionClosure S x).mpr ⟨k, hx⟩)), hseed, hxr⟩

end HordijkSteelThreshold
