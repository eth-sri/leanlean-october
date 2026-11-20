/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteFloorCompletion
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.CountedRecoding

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Chain

variable {D : Type*} [Fintype D]

/-- The primitive range of a row: its ordinal values. -/
noncomputable def primRange (target : D → ExtOrd) : Finset Ordinal.{0} :=
  Finset.univ.biUnion fun d =>
    match target d with
    | some (some v) => {v}
    | _ => ∅

theorem mem_primRange_of_eq {target : D → ExtOrd} {d : D} {v : Ordinal.{0}}
    (h : target d = ofOrd v) : v ∈ primRange target := by
  unfold primRange
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_univ d, ?_⟩
  rw [h]
  exact Finset.mem_singleton_self v

/-- The bounded replacement closure of the sources at the controller grade. -/
noncomputable def inventory (K : ℕ) (E : D → ExtOrd) : Finset ExtOrd :=
  Finset.univ.image E ∪
    (Finset.univ.image E).biUnion fun x =>
      (Finset.range (K + 1)).image fun i => extVisibilityReplace x K i

theorem source_mem_inventory (K : ℕ) (E : D → ExtOrd) (d : D) : E d ∈ inventory K E :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem E (Finset.mem_univ d))

theorem evr_source_mem_inventory (K : ℕ) (E : D → ExtOrd) (d : D) {i : ℕ} (hi : i ≤ K) :
    extVisibilityReplace (E d) K i ∈ inventory K E := by
  apply Finset.mem_union_right
  grind

theorem mem_inventory_iff {K : ℕ} {E : D → ExtOrd} {y : ExtOrd} :
    y ∈ inventory K E ↔ (∃ d, y = E d) ∨ ∃ d, ∃ i ≤ K, y = extVisibilityReplace (E d) K i := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    all_goals grind
  · rintro (⟨d, rfl⟩ | ⟨d, i, hi, rfl⟩)
    · exact source_mem_inventory K E d
    · exact evr_source_mem_inventory K E d hi

/-- A replacement of a source at a threshold `≤ K` is a replacement at `K`, or the source. -/
theorem evr_eq_evr_K {x : ExtOrd} {K k i : ℕ} (hk : k ≤ K) (_hi : i ≤ k) :
    extVisibilityReplace x k i = extVisibilityReplace x K i ∨ extVisibilityReplace x k i = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · right; rfl
  · right; rfl
  · by_cases hfp : finitePart a < k
    · left
      rw [extVisibilityReplace_of_finitePart_lt hfp,
        extVisibilityReplace_of_finitePart_lt (by omega)]
    · right
      exact extVisibilityReplace_of_le_finitePart (not_lt.mp hfp) i

/-- **The inventory is closed under every replacement at thresholds `≤ K`.** -/
theorem inventory_closed (K : ℕ) (E : D → ExtOrd) :
    ∀ x ∈ inventory K E, ∀ k i : ℕ, k ≤ K → i ≤ k → extVisibilityReplace x k i ∈ inventory K E := by
  intro x hx k i hk hi
  rcases mem_inventory_iff.mp hx with ⟨d, rfl⟩ | ⟨d, j, hj, rfl⟩
  · rcases evr_eq_evr_K hk hi with h | h
    · rw [h]; exact evr_source_mem_inventory K E d (hi.trans hk)
    simp_all
  · rcases ExtOrd.cases (E d) with h0 | h0 | ⟨b, hb⟩
    · simp_all
    · simp_all
    · rw [hb]
      by_cases hfb : finitePart b < K
      · rw [extVisibilityReplace_of_finitePart_lt hfb]
        by_cases hjk : j < k
        · rw [extVisibilityReplace_of_finitePart_lt
              (by rw [finitePart_limitPart_add_nat]; exact hjk),
            limitPart_limitPart_add_nat, ← extVisibilityReplace_of_finitePart_lt (k := K) hfb, ← hb]
          exact evr_source_mem_inventory K E d (hi.trans hk)
        · rw [extVisibilityReplace_of_le_finitePart (by rw [finitePart_limitPart_add_nat]; omega),
            ← extVisibilityReplace_of_finitePart_lt (k := K) hfb, ← hb]
          exact evr_source_mem_inventory K E d hj
      · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfb),
          extVisibilityReplace_of_le_finitePart (by omega), ← hb]
        exact source_mem_inventory K E d

variable (grade : D → ℕ) (E p : D → ExtOrd) (c : D)

/-- **The coded locality from an actual controller-capped ambient locality**, for a fixed key set
`S` in which the capped targets are keyed. -/
theorem coded_locality_S (hmax : ∀ d, grade d ≤ grade c)
    (hordp : ∀ d, SelfVis (grade d) (p d))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l : ℕ} (hl : grade c ≤ l)
    (S : Finset Ordinal.{0}) (hS : ∀ d, Keyed l S (min (p d) (p c))) :
    TransformsTo grade E fun d => encT l S (min (p d) (p c)) := by
  classical
  obtain ⟨τ, hτ, -, hsrc⟩ :=
    exists_bounded_exact_capped_witness hmax (hordp c) hloc
  set target : D → ExtOrd := fun d => min (p d) (p c) with htarget
  set K := grade c with hK
  have hTail : ∀ k, K < k → finiteTargetSuppressor grade target k = ⊥ := fun k hk =>
    finiteTargetSuppressor_eq_bot_of_lt grade target hmax hk
  obtain ⟨hB, hM, hO, hBr⟩ :=
    floorCompletion K (inventory K E) τ (finiteTargetSuppressor grade target)
    (inventory_closed K E) hτ.bot hτ.mono (fun x hz k i hi => hτ.zero_repl x hz k hi)
    (fun x k i hk hi => hτ.comm x hk hi) hTail
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
    · rw [hd, hτ.comm _ le_rfl hi, hsrc d]
      exact keyed_evr l S hl (hS d) hi
  have hord : IsOrderly grade target := fun d =>
    (selfVis_min (hordp d) (selfVis_mono (hordp c) (hmax d))).symm
  exact transformsTo_encode C (fun d => (hmax d).trans hl) hS hkeyed
    (isOrderly_encode (fun d => (hmax d).trans hl) hord)


end Chain

section Instance

theorem omul_le_omul {t t' : ℕ} (h : t ≤ t') :
    Ordinal.omega0 * (t : Ordinal) ≤ Ordinal.omega0 * (t' : Ordinal) := by
  gcongr

end Instance

end VaughtConjecture.Knight
