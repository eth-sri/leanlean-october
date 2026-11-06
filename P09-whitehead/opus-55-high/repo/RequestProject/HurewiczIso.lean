import RequestProject.HurewiczDictionary
import RequestProject.PresentationDictionary


/-!
# The Hurewicz dictionary as an explicit isomorphism `H₁(K_N) ≅ N/[N, N]`

`RequestProject/HurewiczDictionary.lean` proves the two membership statements that identify
the first homology of the cover.  Here they are assembled into honest isomorphisms of
groups.

For a presentation `⟨x | ρ⟩` with free group `F`, relator subgroup `R = ⟪ρ⟫`, a normal
subgroup `Ñ ◁ F` containing the relators and cover group `Q = F/Ñ`:

* `FiniteChains.CoverH1` is the first homology `ker ∂₁ / im ∂₂` of the chain complex of the
  cover `K_N`;
* `FiniteChains.coverH1Equiv : (Ñ ⧸ (R·[Ñ, Ñ])) ≃* Multiplicative (H₁(K_N))` — the Crowell
  sequence (surjectivity) plus the Magnus theorem (the kernel);
* `FiniteChains.quotRelCommEquivAbelianization : (Ñ ⧸ (R·[Ñ, Ñ])) ≃* Abelianization N`,
  where `N = Ñ/R ◁ G = F/R`;
* `FiniteChains.coverH1EquivAbelianization : Abelianization N ≃* Multiplicative (H₁(K_N))`,
  the Hurewicz dictionary `H₁(K_N) = N/[N, N]` of Section 2.
-/
