import Mathlib.Tactic

import RequestProject.NormalizedStrictBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.StrictNormalized
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

  (f : P → Q)
  (hf : Monotone f)
/-- The normalized strict edge-chain map of an arbitrary monotone map. -/
noncomputable def mapOne   :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

theorem mapOne_single   (e : StrictOrdEdge P) (n : ℤ) :
    mapOne f hf (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(f e.1.1, f e.1.2), hf e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
  rfl

theorem mapOne_strict  (hf : StrictMono f) (c : StrictOrdEdge P →₀ ℤ) :
    mapOne f hf.monotone c = chain1 (strictOrderCxMap f hf) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
    rw [mapOne_single]
    simp [normalizeOrdEdge, (hf e.2).ne, chain1, strictOrderCxMap]

theorem mapOne_id (c : StrictOrdEdge P →₀ ℤ) : mapOne id monotone_id c = c :=
  normalizedStrictChain1_id c

theorem mapOne_comp   (g : Q → R) (hg : Monotone g)
    (c : StrictOrdEdge P →₀ ℤ) :
    mapOne g hg (mapOne f hf c) = mapOne (g ∘ f) (hg.comp hf) c := by
  induction c using Finsupp.induction_linear <;> aesop (add simp [mapOne_single, normalizeOrdEdge])

/-- Exact naturality of normalization under a strict change of coordinates. -/
theorem mapOne_semiconj (e : P → Q) (he : StrictMono e)
    (g : P → P) (hg : Monotone g) (h : Q → Q) (hh : Monotone h)
    (hs : ∀ x, e (g x) = h (e x)) (c : StrictOrdEdge P →₀ ℤ) :
    chain1 (strictOrderCxMap e he) (normalizedStrictChain1 g hg c) =
      normalizedStrictChain1 h hh (chain1 (strictOrderCxMap e he) c) := by
  change chain1 (strictOrderCxMap e he) (mapOne g hg c) =
    mapOne h hh (chain1 (strictOrderCxMap e he) c)
  rw [← mapOne_strict e he, ← mapOne_strict e he, mapOne_comp, mapOne_comp]
  have heq  := funext hs
  have mapEq (f g : P → Q) (hf : Monotone f) (hg : Monotone g) (he : f = g) :
      mapOne f hf c = mapOne g hg c := by
    subst g
    rfl
  exact mapEq _ _ _ _ heq

end FiniteChains.Comb.StrictNormalized
