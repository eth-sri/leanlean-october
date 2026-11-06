/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.ChartLanguage
import InfinitaryLogic.Karp.PotentialIso

/-! # The Karp bridge: potential isomorphism of chart structures (#137)

The semantic boundary object between the Knight-specific producer mathematics and standard
model theory is `InfinitaryLogic`'s `PotentialIso` — a family of finite tuple pairs containing
the empty pair, atomically compatible, and closed under one-point forth/back — **of the stage
chart structures** (`stageStructureOf`, `Knight/ChartLanguage.lean`).  This module contains the
consumer direction:

* `nonempty_iso_of_potentialIso` — a `PotentialIso` between `stageStructureOf R` and
  `stageStructureOf R'` yields an actual isomorphism `Realization.Iso R R'` on countable
  carriers.  The standard countable potential-isomorphism theorem
  (`PotentialIso.countable_toEquiv`) constructs the chart-structure isomorphism, and
  `isIsoOfStageStructureEquiv` reflects it back to the `Option`-valued labels;
* `potentialIsoOfCommonCharts` — the producer-facing constructor: a family of tuple pairs each
  witnessed by one common projected chart (`HasCommonChart`), with the empty pair and one-point
  forth/back, *is* a `PotentialIso` of the chart structures, by
  `sameAtomicType_of_commonChart` under exact face consistency on both sides;
* `nonempty_iso_of_commonCharts` — the composite: such a family yields `Realization.Iso R R'`
  on countable carriers.

There is deliberately **no** parallel Knight back-and-forth structure here: producers either
construct `PotentialIso` directly (its compatibility field, `SameAtomicType`, is exactly the
equal-atomic-diagram output of a transfer theorem) or feed common-chart certificates to
`potentialIsoOfCommonCharts`.  All transfinite back-and-forth recursion and formula induction
(`PotentialIso.family_bfEquiv`, `BFEquiv_implies_agreeQR`) live in `InfinitaryLogic` and are
not rebuilt.

**Never identify** (#137): a `PotentialIso` proves the *given* realizations isomorphic — it
does not construct selected descendant contexts, and equality of complete types does not
replace its forth/back fields.  No claim about atomic models or complete types is made. -/

namespace VaughtConjecture.Knight

open FirstOrder Language TypeTower

universe w w'

variable {α : LimitStage}

section

variable {M : Type w} {N : Type w'}
variable {R : KnightRealization α M} {R' : KnightRealization α N}

/-- A family of finite tuple pairs, each witnessed by one common projected Knight chart,
containing the empty pair and closed under one-point forth/back, is a standard potential
isomorphism of the stage chart structures: exact face consistency turns the common-chart
certificates into atomic compatibility.  This is the producer-facing constructor — the
Knight-specific side supplies exactly these four pieces of data, and every later
back-and-forth consequence is delegated to `InfinitaryLogic`. -/
noncomputable def potentialIsoOfCommonCharts
    (hR : R.IsExactParentConsistent) (hR' : R'.IsExactParentConsistent)
    (family : Set (Σ n : ℕ, (Fin n → M) × (Fin n → N)))
    (empty_mem : (⟨0, Fin.elim0, Fin.elim0⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family)
    (commonChart : ∀ x ∈ family, HasCommonChart R R' x.2.1 x.2.2)
    (forth : ∀ x ∈ family, ∀ m ,
      ∃ n' , (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family)
    (back : ∀ x ∈ family, ∀ n' ,
      ∃ m , (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family) := by
  letI instM : (stageLang α).Structure M := stageStructureOf R
  letI instN : (stageLang α).Structure N := stageStructureOf R'
  exact PotentialIso.ofExtensionFamily
    (fun n a b => (⟨n, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ family)
    empty_mem
    (fun h => sameAtomicType_of_commonChart hR hR' (commonChart _ h))
    (fun h => forth _ h)
    (fun h => back _ h)



