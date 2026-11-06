
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.FiniteFloorCompletion
import VaughtConjecture.Knight.WitnessAlgebra
import VaughtConjecture.Knight.CountedRecoding

/-! # The coded ambient locality of a controller-capped row: the chain

    actual ambient locality  →  controller-capped witness  →  finite floor-completed certificate
      →  keyed encoded certificate  →  the owned coded lower row respects the ambient semantics

**The actual obligation.**  In the assembled scheme, consistency (Def. 2.5.12) demands, for an
owned coded witness row `enc ∘ p` and every proper cell `d` below it, the locality
`E ⇒ enc ∘ p ∧ enc (p c)` from the core's locality `E ⇒ p ∧ p c` toward the **controller** `c` of
maximal grade, which attains the common cap `p c` (`RespectsSemantics.locality`).

* `exists_cappedWitness` — the shifter capped at `p c` is a faithful witness, equal to the displayed
  target at every source, commuting with every replacement at thresholds `≤ grade c`
  unconditionally, and propagating `⊥` (the sibling's controller-capped shifter, in V-C's calculus;
  the key step `cap_le_of_evr` applies the ambient clause 5 at the replaced point).
* `coded_locality_of_capped_S` — the chain for a **fixed key set** `S` in which the capped targets
  are keyed: the floor completion of the capped witness on the bounded replacement closure of the
  sources (`inventory`) is a keyed certificate, which the counted encoding transports.
* `coded_locality_S` (with the bottom cap), `coded_locality` (`S` the primitive range of the row),
  and `coded_locality_valuesAt` — the instantiation on the owned witness's own value set
  `valuesAt gradeP F l` (`Knight/RecodingTriangle.lean`), keyedness derived from the construction,
  with the required target `min (enc_S (p d)) (enc_S (p c))` obtained from preservation of minima.
* Regression instances: a nonconstant mixed-grade locality (`transformsTo_M`, `coded_M`,
  `encT_controller_M`), and the same locality coded with a global key set containing a key absent
  from the controller's local target (`coded_M_global`, `encT_controller_global`): the block numbers
  differ, which is why one shared key set is required for assembly.

**Not here**: full-scope bountifulness, truncations, and the three-level scheme assembly.
Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Part 3 — the chain on an actual ambient locality

`coded_locality_of_capped` / `coded_locality`: an actual ambient locality `E ⇒ p ∧ p(c)` toward a
maximal-grade controller `c`, with `p` orderly on the lower set, gives the **coded** locality
`E ⇒ enc ∘ (p ∧ p(c))` at any coding grade `l ≥ grade c`, with the counted encoding over the
primitive range of the capped target row.  No normalization, keyed-table, orbit, or bridge
hypothesis remains: keyedness is derived from the primitive range and the bounded replacement
closure of the sources, the certificate is the floor completion of the capped witness, and the
cashout is the kernel's.  The bottom-cap case is handled separately (every target is `⊥`). -/

section

variable {D : Type*} [Fintype D]

/-- The primitive range of a row: its ordinal values. -/
noncomputable def primRange (target : D → ExtOrd) :=
  Finset.univ.biUnion fun d =>
    match target d with
    | some (some v) => {v}
    | _ => ∅

theorem mem_primRange_of_eq {target : D → ExtOrd} {d : D} {v : Ordinal₀}
    (h : target d = ofOrd v) : v ∈ primRange target := by
  
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_univ d, ?_⟩
  rw [h]
  exact Finset.mem_singleton_self v

/-- The bounded replacement closure of the sources at the controller grade. -/
noncomputable def inventory (K : ℕ) (E : D → ExtOrd) :=
  Finset.univ.image E ∪
    (Finset.univ.image E).biUnion fun x =>
      (Finset.range (K + 1)).image fun i => extVisibilityReplace x K i

theorem source_mem_inventory (K : ℕ) (E : D → ExtOrd) (d : D) : E d ∈ inventory K E :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem E (Finset.mem_univ d))

theorem evr_source_mem_inventory (K : ℕ) (E : D → ExtOrd) (d : D) {i : ℕ} (hi : i ≤ K) :
    extVisibilityReplace (E d) K i ∈ inventory K E := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨E d, Finset.mem_image_of_mem E (Finset.mem_univ d),
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩⟩

theorem mem_inventory_iff {K : ℕ} {E : D → ExtOrd} {y : ExtOrd} :
    y ∈ inventory K E ↔ (∃ d, y = E d) ∨ ∃ d, ∃ i ≤ K, y = extVisibilityReplace (E d) K i := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · aesop
    · aesop
  · aesop (add safe apply [source_mem_inventory, evr_source_mem_inventory])

/-- A replacement of a source at a threshold `≤ K` is a replacement at `K`, or the source. -/
theorem evr_eq_evr_K {x} {K k i} (hk : k ≤ K) (_hi : i ≤ k) :
    extVisibilityReplace x k i = extVisibilityReplace x K i ∨ extVisibilityReplace x k i = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · right; rfl
  · right; rfl
  · by_cases hfp : finitePart a < k
    · left
      rw [extVisibilityReplace_of_finitePart_lt hfp,
        extVisibilityReplace_of_finitePart_lt (by omega)]
    · grind [extVisibilityReplace_of_le_finitePart]

/-- **The inventory is closed under every replacement at thresholds `≤ K`.** -/
theorem inventory_closed (K : ℕ) (E : D → ExtOrd) :
    ∀ x ∈ inventory K E, ∀ k i , k ≤ K → i ≤ k → extVisibilityReplace x k i ∈ inventory K E := by
  intro x hx k i hk hi
  rcases mem_inventory_iff.mp hx with ⟨d, rfl⟩ | ⟨d, j, hj, rfl⟩
  · rcases evr_eq_evr_K hk hi with h | h
    · rw [h]; exact evr_source_mem_inventory K E d (hi.trans hk)
    · simp_all
  · rcases ExtOrd.cases (E d) with h0 | h0 | ⟨b, hb⟩
    · simp_all
    · simp_all
    · rw [hb]
      by_cases hfb : finitePart b < K
      · rw [extVisibilityReplace_of_finitePart_lt hfb]
        by_cases hjk : j < k
        · rw [extVisibilityReplace_of_finitePart_lt
              (by simp_all [VaughtConjecture.Knight.Value.finitePart, VaughtConjecture.Knight.Value.limitPart]),
            limitPart_limitPart_add_nat, ← extVisibilityReplace_of_finitePart_lt  hfb, ← hb]
          exact evr_source_mem_inventory K E d (hi.trans hk)
        · rw [extVisibilityReplace_of_le_finitePart (by grind [finitePart_limitPart_add_nat]),
            ← extVisibilityReplace_of_finitePart_lt  hfb, ← hb]
          exact evr_source_mem_inventory K E d hj
      · grind [extVisibilityReplace_of_le_finitePart]

variable (grade : D → ℕ) (E p : D → ExtOrd) (c : D)

/-- **The coded locality from an actual controller-capped ambient locality**, for a fixed key set
`S` in which the capped targets are keyed (nonbottom cap). -/
theorem coded_locality_of_capped_S (hmax : BoundedBy grade (grade c))
    (hordp : ∀ d, SelfVis (grade d) (p d)) (hne : p c ≠ ⊥)
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l} (hl : grade c ≤ l)
    S (hS : ∀ d, Keyed l S (min (p d) (p c))) :
    TransformsTo grade E fun d => encT l S (min (p d) (p c)) := by
  
  obtain ⟨g', τ, -, -, hbot, hmono, -, -, hcap, hsrc, hcomm, hbotprop⟩ :=
    exists_cappedWitness grade E p c hmax (hordp c) hne hloc
  set target : D → ExtOrd := fun d => min (p d) (p c) with htarget
  set K := grade c with hK
  have hTail : ∀ k, K < k → finiteTargetSuppressor grade target k = ⊥ := fun k hk =>
    finiteTargetSuppressor_eq_bot_of_lt grade target hmax hk
  obtain ⟨hB, hM, hO, hBr⟩ :=
    floorCompletion K (inventory K E) τ (finiteTargetSuppressor grade target)
    (inventory_closed K E) hbot hmono hbotprop
    (fun x k i hk hi => hcomm x k i hk hi) hTail
  -- the uncoded certificate
  let C : FiniteBlockBridgeCertificate grade E target :=
    { tableDomain := stripDomain K (inventory K E)
      table := fun x => τ (roundUp (inventory K E) x)
      bottom := hB
      monotone := hM
      orbit := hO
      bridge := hBr
      source_mem := fun d => subset_stripDomain K _ (source_mem_inventory K E d)
      realizes := fun d => by
        show target d = min (τ (roundUp (inventory K E) (E d))) _
        rw [roundUp_of_mem (source_mem_inventory K E d), hsrc d,
          min_eq_left (target_le_finiteTargetSuppressor grade target d)] }
  -- keyedness of the table on its domain
  have hkeyed : ∀ y ∈ C.tableDomain, Keyed l S (C.table y) := by
    intro y hy
    show Keyed l S (τ (roundUp (inventory K E) y))
    have hmem := roundUp_mem K (inventory K E) (inventory_closed K E) hy
    rcases mem_inventory_iff.mp hmem with ⟨d, hd⟩ | ⟨d, i, hi, hd⟩
    · rw [hd, hsrc d]; exact hS d
    · rw [hd, hcomm _ K i le_rfl hi, hsrc d]
      exact keyed_evr l S hl (hS d) hi
  have hord : IsOrderly grade target := fun d =>
    (selfVis_min (hordp d) (selfVis_mono (hordp c) (hmax d))).symm
  exact transformsTo_encode C (fun d => (hmax d).trans hl) hS hkeyed
    (isOrderly_encode (fun d => (hmax d).trans hl) hord)

/-- **The coded locality for a fixed key set, including the bottom cap.** -/
theorem coded_locality_S (hmax : BoundedBy grade (grade c))
    (hordp : ∀ d, SelfVis (grade d) (p d))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l} (hl : grade c ≤ l)
    S (hS : ∀ d, Keyed l S (min (p d) (p c))) :
    TransformsTo grade E fun d => encT l S (min (p d) (p c)) := by
  by_cases hne : p c = ⊥
  · aesop
  · exact?

end

/-! ## Part 4 — a nonconstant mixed-grade instance

Two cells: `a` of grade 1 with source `ω·2 + 1` and value `ω + 1`; the controller `c` of grade 2
with source `ω·3 + 2` and value `ω·5 + 2`.  The ambient shifter is `⊥` below the source block of
`a`, `ω + min(fp, 2)` on that block, `ω·5 + min(fp, 2)` on the controller's block, and the constant
`ω·5 + 2` above; the suppressor is the cap through grade 2.  The locality is verified
(`transformsTo_M`), so `coded_locality` applies at coding grade 2 (`coded_M`).  There the
primitive range `{ω + 1, ω·5 + 2}` has keys `{ω, ω·5}`, and the encoding is **not** the identity:
the controller's value `ω·5 + 2` is coded `ω·2 + 2` (`encT_controller_M`). -/

section

theorem omul_le_omul {t t' : ℕ} (h : t ≤ t') :
    Ordinal.omega0 * (t : Ordinal) ≤ Ordinal.omega0 * (t' : Ordinal) := by
  gcongr


