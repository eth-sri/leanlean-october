/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.ExpansionDomainUniform
import VaughtConjecture.Knight.BFBoundednessThinness
import VaughtConjecture.Knight.ConstructedTerminalCountability
import VaughtConjecture.Knight.ConstructedTerminalLoss
import VaughtConjecture.Knight.ExpansionDomainCertificate
import InfinitaryLogic.Descriptive.PerfectAntichain
import InfinitaryLogic.OrdinalUtil
import Architect
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import InfinitaryLogic.Descriptive.Polish
import InfinitaryLogic.Descriptive.SatisfactionBorelOn
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Scott.BackAndForth
import Mathlib.SetTheory.Cardinal.Aleph
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Lomega1omega.QuantifierRank
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.RefinementCount
import Mathlib.SetTheory.Cardinal.Regular
import InfinitaryLogic.Karp.PotentialIso
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic
import InfinitaryLogic.Descriptive.StructureSpace
import Mathlib.GroupTheory.Perm.Basic
import VaughtConjecture.Spectrum.Sentence

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

