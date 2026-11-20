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

@[expose] public section

namespace VaughtConjecture.Spectrum

open FirstOrder Language Cardinal

universe u v w

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The standard `I(φ, ℵ₀)`: isomorphism classes of `ℕ`-models of `φ` (models of cardinality
exactly `ℵ₀`). -/
noncomputable def natModelSpectrum (φ : L.Sentenceω) : Cardinal :=
  #(Quotient (isoSetoid φ))

/-- `φ` has no finite models (every `Fin n` tier of coded models is empty). -/
def HasNoFiniteModels (φ : L.Sentenceω) : Prop :=
  ∀ n : ℕ, ModelsOfOn (α := Fin n) φ = ∅

end VaughtConjecture.Spectrum
