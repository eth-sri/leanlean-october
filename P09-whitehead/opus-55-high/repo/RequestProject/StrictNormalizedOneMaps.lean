import RequestProject.NormalizedStrictBoundary
import RequestProject.Tac


bwd

namespace FiniteChains.Comb.StrictNormalized
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The normalized strict edge-chain map of an arbitrary monotone map. -/
noncomputable def mapOne (f : P → Q) (hf : Monotone f) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

theorem mapOne_single (f : P → Q) hf e n :
    mapOne f hf (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(f e.1.1, f e.1.2), hf e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  aesop

theorem mapOne_strict (f : P → Q) hf c :
    mapOne f hf.monotone c = chain1 (strictOrderCxMap f hf) c := by
  classical
  lin_ind c e n =>
    rw [mapOne_single]
    simp [normalizeOrdEdge, (hf e.2).ne, chain1, strictOrderCxMap]

theorem mapOne_id (c : StrictOrdEdge P →₀ ℤ) : mapOne id monotone_id c = c :=
  normalizedStrictChain1_id c

theorem mapOne_comp f hf (g : Q → R) hg
    (c : StrictOrdEdge P →₀ ℤ) :
    mapOne g hg (mapOne f hf c) = mapOne (g ∘ f) (hg.comp hf) c := by
  classical
  lin_ind c e n =>
    by_cases h : f e.1.1 = f e.1.2
    · simp [normalizeOrdEdge, h, mapOne_single, Function.comp_def]
    · simp [show normalizeOrdEdge ⟨(f e.1.1, f e.1.2), hf e.2.le⟩ =
        Finsupp.single ⟨(f e.1.1, f e.1.2), lt_of_le_of_ne (hf e.2.le) h⟩ 1 by
          simp [normalizeOrdEdge, h], mapOne_single, one_smul]

/-- Exact naturality of normalization under a strict change of coordinates. -/
theorem mapOne_semiconj e he
    g hg (h : Q → Q) hh
    (hs : ∀ x, e (g x) = h (e x)) (c : StrictOrdEdge P →₀ ℤ) :
    chain1 (strictOrderCxMap e he) (normalizedStrictChain1 g hg c) =
      normalizedStrictChain1 h hh (chain1 (strictOrderCxMap e he) c) := by
  change chain1 (strictOrderCxMap e he) (mapOne g hg c) =
    mapOne h hh (chain1 (strictOrderCxMap e he) c)
  rw [← mapOne_strict e he, ← mapOne_strict e he, mapOne_comp, mapOne_comp]
  have heq : e ∘ g = h ∘ e := funext hs
  simp_all
