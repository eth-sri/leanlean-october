module

public import RequestProject.NormalizedStrictBoundary

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.StrictNormalized
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

variable (f : P → Q)

variable (hf : Monotone f)

/-- The normalized strict edge-chain map of an arbitrary monotone map. -/
noncomputable def mapOne :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

theorem mapOne_single (e : StrictOrdEdge P) (n : ℤ) :
    mapOne f hf (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(f _, f _), hf e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain _
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  aesop

theorem mapOne_strict (hf : StrictMono f) (c : StrictOrdEdge P →₀ ℤ) :
    mapOne f hf.monotone c = chain1 (strictOrderCxMap f hf) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [mapOne_single]
    simp [normalizeOrdEdge, (hf e.2).ne, chain1, strictOrderCxMap]

theorem mapOne_id (c : StrictOrdEdge P →₀ ℤ) : mapOne id monotone_id c = c :=
  normalizedStrictChain1_id c

theorem mapOne_comp (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (c : StrictOrdEdge P →₀ ℤ) :
    mapOne g hg (mapOne f hf c) = mapOne _ (hg.comp hf) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [mapOne_single, map_smul]
    by_cases h : f e.1.1 = f e.1.2
    · simp [normalizeOrdEdge, h, mapOne_single, Function.comp_def]
    · rw [show normalizeOrdEdge (⟨(f _, f _), hf e.2.le⟩) =
        Finsupp.single ⟨(f _, f _), lt_of_le_of_ne (hf e.2.le) h⟩ 1 by
          simp [normalizeOrdEdge, h]]
      simp [mapOne_single, one_smul]

/-- Exact naturality of normalization under a strict change of coordinates. -/
theorem mapOne_semiconj (e : P → Q) (he : StrictMono e)
    (g : P → P) (hg : Monotone g) (h : Q → Q) (hh : Monotone h)
    (hs : ∀ x, e (g x) = h (e x)) (c : StrictOrdEdge P →₀ ℤ) :
    chain1 (strictOrderCxMap e he) (normalizedStrictChain1 g hg c) =
      normalizedStrictChain1 h hh (chain1 (strictOrderCxMap e he) c) := by
  change chain1 (strictOrderCxMap e he) (mapOne g hg c) =
    mapOne h hh _
  rw [← mapOne_strict e he, ← mapOne_strict e he, mapOne_comp, mapOne_comp]
  have heq : e ∘ g = h ∘ e := funext hs
  simp_all

end FiniteChains.Comb.StrictNormalized
