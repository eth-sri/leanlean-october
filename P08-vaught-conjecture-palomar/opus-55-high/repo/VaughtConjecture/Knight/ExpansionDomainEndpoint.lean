/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainUniform
public import VaughtConjecture.Knight.BFBoundednessThinness
public import VaughtConjecture.Knight.ConstructedTerminalCountability
public import VaughtConjecture.Knight.ConstructedTerminalLoss
public import VaughtConjecture.Knight.ExpansionDomainCertificate
public import InfinitaryLogic.Descriptive.PerfectAntichain
public import InfinitaryLogic.OrdinalUtil
public import Architect
public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import InfinitaryLogic.Descriptive.Polish
public import InfinitaryLogic.Descriptive.SatisfactionBorelOn
public import InfinitaryLogic.Descriptive.SatisfactionBorel
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
public import Mathlib.SetTheory.Cardinal.Continuum
public import InfinitaryLogic.Descriptive.StructureSpace
public import Mathlib.GroupTheory.Perm.Basic
public import VaughtConjecture.Spectrum.Sentence

/-! # Spectrum and thinness without global termination

Countable terminal losses and limit continuity give countable exceptions to
uniform logical comparison. Scott separation makes the persistent core a subsingleton;
counting that core and the `ℵ₁` countable complements gives the upper bound without Morley.
Locally constructed top-free terminal models supply nonempty successor losses and the lower
bound. Direct analytic BF boundedness supplies thinness separately.

This is the recommended combined spectrum/thinness entry point. It never needs
to prove that every counted class eventually stops. Historical cardinality
proofs remain separate; the old perfect-set names delegate here. The theorem
is about the repository's infinitary sentence and defined spectrum, not a
first-order Vaught statement; mathematical definitional review remains separate.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ExpansionDomainEndpoint

open FirstOrder Language Cardinal Spectrum StoppingRankFiltration

/-- All construction receipts for generic filtration counting and sentence separation. -/
def certificate : FiltrationCertificate Classes knightLang.Sentenceω realizes :=
  ExpansionDomain.filtrationCertificate ConstructedSpectrumEndpoint.countableTerminalFibres
    ExpansionDomain.cofinal_losses

/-- Direct boundedness thinness from uniform finite-cover comparison and countable
terminal fibres. Neither sentence-minimality nor sentence recovery is used. -/
theorem isThinOnNatModels : knightSentence.IsThinOnNatModels :=
  ExpansionDomain.isThinOnNatModels_of_bfBoundedness
    ConstructedSpectrumEndpoint.countableTerminalFibres

/-- Exact spectrum from Scott-separated core counting and local losses. Neither thinness,
Morley counting, nor eventual departure is used in this proof. -/
theorem natModelSpectrum_eq_aleph_one : natModelSpectrum knightSentence = aleph 1 := by
  rw [natModelSpectrum_knightSentence]
  exact certificate.cardinality

end VaughtConjecture.Knight.ExpansionDomainEndpoint
