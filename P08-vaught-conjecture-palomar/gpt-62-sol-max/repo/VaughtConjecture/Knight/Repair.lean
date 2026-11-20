/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra

/-! # The repair algebra (#42): cutoff-flatten + band-cap on stage types

The kernel of the preferred construction (#42): the **homogeneous repair** of a stage
type at a limit cutoff `α` — cutoff-flatten the high tail, then install one
construction-chosen high value per grade — with every semantic obligation REPROVED, not
assumed:

* a **repair band** (`RepairBand`): the suppressor `g : ℕ → ExtOrd`, antitone,
  self-visible at each grade, high (`≥ α`), stage-bounded;
* the repair of one label (`repairLabel`): `p̂ d = min (truncExt α (p d)) (g (grade d))`
  — ordinary (below-cutoff) labels are untouched (`repairLabel_of_lt`), every high label
  receives exactly the band value of its grade (`repairLabel_of_ge`);
* the repaired stage type (`repairType`): a genuine `S β N` — orderliness, locality and
  availability are reproved by construction.  Locality composes the ambient row
  transform with the compiled strict-truncation closure (`TransformsTo.truncExt_target`)
  and absorbs the band caps into the suppressor (`min`-shuffling; the cap's
  self-visibility survives at every threshold because the band is antitone);
* **restriction commutes with the repair** (`typeMap_repairType`; the coface instance
  `isCoface_repairType` lives in `Knight/RepairConsumers.lean`): restriction preserves grades, so repairing then restricting is
  restricting then repairing — on the nose;
* **reduction is invariant under the repair** (`reduceType_repairType`): the repair
  happens strictly above the cutoff, so the source reduction of the repaired block IS
  that of the unrepaired one;
* **the repair is confined to the source-`⊤` cells** (`repairType_confined`, with its
  projection lemmas): at every cell where the source reduction shows a proper label the
  repaired and unrepaired blocks agree exactly; at the source-`⊤` cells both are high.
  The general two-block form (`residue_confined_to_source_top`: any two blocks
  cutoff-pinned to the same source witness agree at every source-proper cell) lives in
  `Knight/RepairConsumers.lean` — cell transport (`SemScheme.castCell`) enters the
  library at the model layer, while here the two blocks share their scheme
  definitionally.

## Provenance

Extracted from the #42 experiment stack (PRs #154/#157/#158; experimental stack
modules `SpliceFalsify.lean`, `BandSelection.lean`, `RepairedExtension.lean`):
the self-visibility helpers (`SelfVis`, `selfVis_min`, `selfVis_mono`) from #154, the
cutoff arithmetic from #157 (its general residue-confinement theorem sits in
`Knight/RepairConsumers.lean`), the repair algebra itself from #158.  The universal splice (`SelectedBlockSplice`) was REFUTED in #154
(`selectedBlockSplice_false`) and is NOT landed; likewise the falsification
configurations and the dropped `BandCoherent` machinery stay on the experimental
branches.

## Boundary (what this module does NOT claim)

This is the homogeneous repair algebra only — and provably nothing more: the fixed-band
no-go is COMPILED (#160, `no_fixed_band` / `banded_master_impossible`): no `IsModel` at
`α + ω` is globally banded by ONE fixed `RepairBand`, so a fair recursion carrying a
single total band across all steps cannot exist.  **`RepairBand` is LOCAL repair
algebra — per-step, per-block — never fair-recursion state.**  The paired-shadow state
(`PairedShadow`) and the iterable successor step (`exists_repairedAmbientExtension`),
which fix one total band across steps, accordingly remain on the experimental branch
`e5/repaired-extension` and are ruled out as stated; no iterable construction step and
no global recursion invariant are claimed here. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

variable {α β : Ordinal.{0}}

/-! ### Cutoff arithmetic (from #157) -/

/-! ### The repair band -/

/-- A **repair band** from the cutoff `α` into stage `β`: the construction-chosen
suppressor prescribing ONE repaired high value per grade.  Antitone and self-visible are
the suppressor clauses of `TransformsTo`; `high` confines the repair to the high tail
(low labels are never touched, and repaired cells stay high); `bound` keeps the repaired
labels strictly bounded at stage `β`. -/
structure RepairBand (α β : Ordinal.{0}) where
  /-- The repaired high value at each grade. -/
  g : ℕ → ExtOrd
  /-- The band is antitone in the grade (suppressor clause 1, in `≤` form). -/
  antitone : ∀ {k m : ℕ}, k ≤ m → g m ≤ g k
  /-- Each band value is self-visible at its grade (suppressor clause 2). -/
  selfvis : ∀ k, extVisibilityReplace (g k) k k = g k
  /-- Band values are high: the repair never reaches below the cutoff. -/
  high : ∀ k, ofOrd α ≤ g k
  /-- Band values are strictly bounded at stage `β`. -/
  bound : ∀ k, g k < ofOrd β ∨ g k = ⊤

/-! ### The repair on one label -/

/-- **The concrete repair of one label**: cutoff-flatten, then band-cap — `min (truncExt α
x) (b.g k)`.  Fixes every label `< α` and sends every label `≥ α` to `b.g k`. -/
noncomputable def repairLabel (b : RepairBand α β) (k : ℕ) (x : ExtOrd) : ExtOrd :=
  min (truncExt α x) (b.g k)

/-- The repaired label is strictly bounded at stage `β`. -/
theorem repairLabel_bound (b : RepairBand α β) (hαβ : α ≤ β) (k : ℕ) (x : ExtOrd) :
    repairLabel b k x < ofOrd β ∨ repairLabel b k x = ⊤ := by
  rcases le_total (truncExt α x) (b.g k) with hmin | hmin
  · rw [repairLabel, min_eq_left hmin]
    rcases truncExt_bound α x with hlt | htop
    · exact Or.inl (hlt.trans_le (ofOrd_le_ofOrd.mpr hαβ))
    · exact Or.inr htop
  · rw [repairLabel, min_eq_right hmin]; exact b.bound k

/-- The repair preserves self-visibility at the grade (orderliness transports). -/
theorem repairLabel_selfvis (b : RepairBand α β) {k : ℕ} {x : ExtOrd}
    (hx : extVisibilityReplace x k k = x) :
    extVisibilityReplace (repairLabel b k x) k k = repairLabel b k x := by
  rcases le_total (truncExt α x) (b.g k) with hmin | hmin
  · rw [repairLabel, min_eq_left hmin]
    exact truncExt_preserves_selfVis α x k hx
  · rw [repairLabel, min_eq_right hmin]; exact b.selfvis k

/-- The repair is monotone in the label (availability transports). -/
theorem repairLabel_mono (b : RepairBand α β) (k : ℕ) {x y : ExtOrd} (hxy : x ≤ y) :
    repairLabel b k x ≤ repairLabel b k y :=
  min_le_min (truncExt_mono α hxy) le_rfl

/-! ### The repaired stage type

The repair of a whole block, with `RespectsSemantics` REPROVED — the sufficiency
obligation discharged by construction: locality composes the ambient row transform with
the compiled strict-truncation closure (`TransformsTo.truncExt_target`) and absorbs the
band caps into the suppressor. -/

variable {N : ℕ}

/-- **The repaired block**: same domain with its associated semantics (the repair retunes
labels only), every label repaired at its own grade.  A genuine stage type: orderliness,
locality and availability are reproved, not assumed. -/
noncomputable def repairType (hα : Order.IsSuccLimit α) (hαβ : α ≤ β) (b : RepairBand α β)
    (Q : S β N) : S β N where
  scheme := Q.scheme
  label d := repairLabel b (Q.scheme.scheme.grade d) (Q.label d)
  label_bound d := repairLabel_bound b hαβ _ _
  respects :=
    { orderly := fun d => (repairLabel_selfvis b (Q.respects.orderly d).symm).symm
      locality := fun Sig => by
        obtain ⟨g₁, σ₁, hdec, hvis, hbot, hmono, hcl5, heq⟩ :=
          (Q.respects.locality Sig).truncExt_target hα
        -- suppressor clause 2: self-visibility of the capped suppressor at EVERY
        -- threshold (above the grade of `Sig` the antitone band collapses the cap)
        have hG2 : ∀ k : ℕ,
            min (g₁ k) (min (b.g k) (b.g (Q.scheme.scheme.grade Sig))) =
              extVisibilityReplace
                (min (g₁ k) (min (b.g k) (b.g (Q.scheme.scheme.grade Sig)))) k k := by
          intro k
          rcases le_total k (Q.scheme.scheme.grade Sig) with hk | hk
          · exact (selfVis_min ((hvis k).symm)
              (selfVis_min (b.selfvis k)
                (selfVis_mono (b.selfvis _) hk))).symm
          · rw [min_eq_left (b.antitone hk)]
            exact (selfVis_min ((hvis k).symm) (b.selfvis k)).symm
        refine ⟨fun k => min (g₁ k) (min (b.g k) (b.g (Q.scheme.scheme.grade Sig))), σ₁,
          fun n m hnm => min_le_min (hdec n m hnm) (min_le_min (b.antitone hnm.le) le_rfl),
          hG2, hbot, hmono,
          fun x k hle i hik => hcl5 x k (hle.trans (min_le_left _ _)) i hik, ?_⟩
        -- the transformation equation: pure `min`-shuffling around the compiled
        -- truncated equation
        intro d
        have h1 : truncExt α (min (Q.label d.1) (Q.label Sig)) =
            min (σ₁ (Q.scheme.rows.E Sig d)) (g₁ (Q.scheme.scheme.grade d.1)) := heq d
        change min (min (truncExt α (Q.label d.1)) (b.g (Q.scheme.scheme.grade d.1)))
              (min (truncExt α (Q.label Sig)) (b.g (Q.scheme.scheme.grade Sig))) =
            min (σ₁ (Q.scheme.rows.E Sig d))
              (min (g₁ (Q.scheme.scheme.grade d.1))
                (min (b.g (Q.scheme.scheme.grade d.1)) (b.g (Q.scheme.scheme.grade Sig))))
        rw [min_min_min_comm, ← truncExt_min, h1, min_assoc]
      availability := fun Sig Xi₀ hsub hgr => by
        obtain ⟨Xi, hcell, hle⟩ := Q.respects.availability Sig Xi₀ hsub hgr
        refine ⟨Xi, hcell, ?_⟩
        have hgr' : Q.scheme.scheme.grade Sig = Q.scheme.scheme.grade Xi :=
          hgr.trans (congrArg Prod.snd hcell).symm
        change repairLabel b (Q.scheme.scheme.grade Sig) (Q.label Sig) ≤
          repairLabel b (Q.scheme.scheme.grade Xi) (Q.label Xi)
        rw [← hgr']
        exact repairLabel_mono b _ hle }

@[simp] theorem repairType_scheme (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    (b : RepairBand α β) (Q : S β N) : (repairType hα hαβ b Q).scheme = Q.scheme := rfl

@[simp] theorem repairType_label (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    (b : RepairBand α β) (Q : S β N) (d : Cell Q.scheme.scheme) :
    (repairType hα hαβ b Q).label d =
      repairLabel b (Q.scheme.scheme.grade d) (Q.label d) := rfl

/-! ### The repair commutes with restriction and is invisible to reduction -/

/-! ### The confinement of the repair -/

end VaughtConjecture.Knight
