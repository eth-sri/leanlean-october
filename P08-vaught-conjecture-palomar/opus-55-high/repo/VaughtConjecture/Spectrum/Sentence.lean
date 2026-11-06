/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.ModelTheory.MorleyCounting
public import Mathlib.Topology.MetricSpace.CantorScheme
public import InfinitaryLogic.Descriptive.PerfectAntichain
public import InfinitaryLogic.Descriptive.Polish
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import Architect
public import InfinitaryLogic.OrdinalUtil
public import InfinitaryLogic.Scott.BackAndForth
public import Mathlib.SetTheory.Cardinal.Aleph
public import InfinitaryLogic.Lomega1omega.Theory
public import InfinitaryLogic.Scott.Formula
public import InfinitaryLogic.Lomega1omega.QuantifierRank
public import InfinitaryLogic.Karp.CarrierTheorem
public import InfinitaryLogic.Scott.Sentence
public import InfinitaryLogic.Scott.RefinementCount
public import Mathlib.SetTheory.Cardinal.Regular
public import InfinitaryLogic.Karp.PotentialIso
public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Bases
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import InfinitaryLogic.Descriptive.AnalyticClosure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # The countable spectrum of an `L_{ω₁,ω}` sentence

We take the notion of "countable models up to isomorphism" from
`InfinitaryLogic`.  Two counts are kept apart:

* `natModelSpectrum φ := #(Quotient (isoSetoid φ))` — isomorphism classes of `ℕ`-models,
  i.e. models of cardinality exactly `ℵ₀`.  This is the standard `I(φ, ℵ₀)`.
* `allCountableSpectrum φ := #(AllCodedIsoClasses φ)` — all carrier tiers (`ℕ` and every
  `Fin n`), faithfully representing all countable models by `codeModel`,
  `codeModel_eq_of_iso`, `iso_of_codeModel_eq`, `codeModel_surjective`.

The two agree when `φ` has no finite models (`HasNoFiniteModels`,
`allCountableSpectrum_eq_natModelSpectrum`).  Conventional names
(`CardinalVaughtConjectureFor`, and `VaughtConjecturePerfectSetFor` in `Spectrum.Thinness`)
refer to the `ℕ`-tier forms; the all-tier variants carry the prefix `AllCountable`.

* Morley's theorem (`morley_counting_coded` / `morley_counting`, unconditional in
  `InfinitaryLogic` via its proof of the Silver–Burgess dichotomy) gives
  `I(φ,ℵ₀) ≤ ℵ₁ ∨ I(φ,ℵ₀) = 2^ℵ₀` in both forms.  The witnessed refinements
  (`morley_counting_coded_or_perfect` / `morley_counting_or_perfect`) put a perfect set of
  pairwise non-isomorphic models in the second alternative; their spectrum-named adapters are
  `natModelSpectrum_le_aleph_one_or_perfectSet` /
  `allCountableSpectrum_le_aleph_one_or_perfectSet`.
* `natModelSpectrum_eq_aleph_one_of_rank` / `allCountableSpectrum_eq_aleph_one_of_rank`: the
  shape of Knight's headline — a total rank into `ω₁` with countable fibres and cofinal range
  on the isomorphism classes forces exactly `ℵ₁` classes.
* `not_cardinalVaughtConjectureFor_of_eq_aleph_one`: under `¬CH`, `I(φ,ℵ₀) = ℵ₁` refutes the
  cardinal form.  The CH-independent (perfect-set) form needs the separate thinness statement;
  see `Spectrum.Thinness` and `docs/DESIGN.md`. -/

@[expose] public section

namespace VaughtConjecture.Spectrum

open FirstOrder Language Cardinal

universe u v w

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

section
variable (φ : L.Sentenceω)

/-- The standard `I(φ, ℵ₀)`: isomorphism classes of `ℕ`-models of `φ` (models of cardinality
exactly `ℵ₀`). -/
noncomputable def natModelSpectrum  : Cardinal :=
  #(Quotient (isoSetoid φ))

/-- `φ` has no finite models (every `Fin n` tier of coded models is empty). -/
def HasNoFiniteModels  : Prop :=
  ∀ n : ℕ, ModelsOfOn (α := Fin n) φ = ∅

end

end VaughtConjecture.Spectrum
