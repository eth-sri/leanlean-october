/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Countable locally dense compactly supported test families on an open chart. -/

public section

open Set TopologicalSpace
open scoped Topology CompactlySupported

namespace DOZZ.Proofs

/-- Every open planar chart admits a countable family of compactly supported continuous tests
which is uniformly dense on each member of a compact exhaustion of the chart. -/
theorem exists_countable_dense_admissible_tests
    (U : Set ℂ) (hU : IsOpen U) :
    ∃ K : ℕ → Set ℂ,
      (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ U) ∧
      (∀ n, K n ⊆ K (n + 1)) ∧
      (⋃ n, K n) = U ∧
      (∀ L, IsCompact L → L ⊆ U → ∃ n, L ⊆ K n) ∧
      ∃ f : ℕ × ℕ → BoundedContinuousFunction ℂ ℝ,
        (∀ n m, HasCompactSupport (f (n, m) : ℂ → ℝ) ∧
          tsupport (f (n, m) : ℂ → ℝ) ⊆ K n ∧
          tsupport (f (n, m) : ℂ → ℝ) ⊆ U) ∧
        (∀ n (g : C(ℂ, ℝ)), HasCompactSupport g → tsupport g ⊆ K n →
          ∀ δ : ℝ, 0 < δ → ∃ m, ∀ x, ‖f (n, m) x - g x‖ < δ) := by
  classical
  let  := hU.locallyCompactSpace
  let : SigmaCompactSpace (↥U) := inferInstance
  let E : CompactExhaustion (↥U) := CompactExhaustion.choice (↥U)
  let K : ℕ → Set ℂ := fun n => Subtype.val '' E n
  have hKcompact (n : ℕ) : IsCompact (K n) := (E.isCompact n).image continuous_subtype_val
  have hKU (n : ℕ) : K n ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hKmono (n : ℕ) : K n ⊆ K (n + 1) := Set.image_mono (E.subset_succ n)
  have hKcover : (⋃ n, K n) = U := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨n, hx⟩
      grind
    · intro hx
      obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
      apply mem_iUnion.mpr
      grind
  have hKcofinal (L : Set ℂ) (hL : IsCompact L) (hLU : L ⊆ U) :
      ∃ n, L ⊆ K n := by
    let j : L → ↥U := fun x => ⟨x.1, hLU x.2⟩
    have hj : Continuous j := by fun_prop
    let S : Set (↥U) := {y | (y : ℂ) ∈ L}
    have hS : Set.range j = S := by
      continuity
    have hSc : IsCompact S := by
      rw [← hS]
      let  := isCompact_iff_compactSpace.mp hL
      exact isCompact_range hj
    obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hSc
    refine ⟨n, ?_⟩
    intro x hx
    refine ⟨⟨x, hLU hx⟩, hn (show (⟨x, hLU hx⟩ : ↥U) ∈ S from hx), rfl⟩
  let S : ℕ → Set C(ℂ, ℝ) := fun n =>
    {g | HasCompactSupport g ∧ tsupport g ⊆ K n}
  let R : (n : ℕ) → Set C(↑(K n), ℝ) := fun n =>
    Set.range fun g : ↥(S n) => g.1.restrict (K n)
  have hRsep (n : ℕ) : SeparableSpace (↥(R n)) := by
    have  := isCompact_iff_compactSpace.mp (hKcompact n)
    have : SecondCountableTopology (↑(K n)) := inferInstance

    have : SecondCountableTopology C(↑(K n), ℝ) := inferInstance
    have : SecondCountableTopology (↥(R n)) := inferInstance
    infer_instance
  have hRnonempty (n : ℕ) : Nonempty (↥(R n)) := by
    refine ⟨⟨0, ?_⟩⟩
    refine ⟨⟨0, ?_⟩, ?_⟩
    · change HasCompactSupport (0 : C(ℂ, ℝ)) ∧ tsupport (0 : C(ℂ, ℝ)) ⊆ K n
      simp [HasCompactSupport]
    · rfl
  let seq : (n : ℕ) → ℕ → ↥(R n) := fun n => by
    letI  := hRsep n
    letI  := hRnonempty n
    exact TopologicalSpace.denseSeq (↥(R n))
  have hseq (n : ℕ) : DenseRange (seq n) := TopologicalSpace.denseRange_denseSeq (↥(R n))
  let source : (n m : ℕ) → ↥(S n) :=
    fun n m => Classical.choose (Set.mem_range.mp (seq n m).property)
  have hsource (n m : ℕ) :
      source n m |>.1.restrict (K n) = (seq n m).1 := by
    grind
  let test : ℕ × ℕ → BoundedContinuousFunction ℂ ℝ := fun nm =>
    ((⟨(source nm.1 nm.2).1, (source nm.1 nm.2).property.1⟩ :
      C_c(ℂ, ℝ)).toBoundedContinuousFunction)
  have htestSupport (n m : ℕ) :
      HasCompactSupport (test (n, m) : ℂ → ℝ) ∧
        tsupport (test (n, m) : ℂ → ℝ) ⊆ K n ∧
        tsupport (test (n, m) : ℂ → ℝ) ⊆ U := by
    refine ⟨(source n m).property.1, ?_, ?_⟩
    · exact (source n m).property.2
    · exact (source n m).property.2.trans (hKU n)
  have hdense (n : ℕ) (g : C(ℂ, ℝ))
      (hg : HasCompactSupport g) (hgs : tsupport g ⊆ K n)
      (δ : ℝ) (hδ : 0 < δ) :
      ∃ m, ∀ x, ‖test (n, m) x - g x‖ < δ := by
    let  := isCompact_iff_compactSpace.mp (hKcompact n)
    let : SecondCountableTopology (↑(K n)) := inferInstance
    let : PseudoMetricSpace C(↑(K n), ℝ) := inferInstance
    let : SecondCountableTopology C(↑(K n), ℝ) := inferInstance

    let : PseudoMetricSpace (↥(R n)) := inferInstance
    let gS : ↥(S n) := ⟨g, ⟨hg, hgs⟩⟩
    let target : C(↑(K n), ℝ) := g.restrict (K n)
    have htarget : target ∈ R n := ⟨gS, rfl⟩
    let targetR : ↥(R n) := ⟨target, htarget⟩
    have hclosure  := hseq n targetR
    obtain ⟨q, hq, hdist⟩ := (Metric.mem_closure_iff.mp hclosure) δ hδ
    obtain ⟨m, rfl⟩ := hq
    refine ⟨m, ?_⟩
    intro x
    by_cases hx : x ∈ K n
    · have hpoint := ContinuousMap.dist_apply_le_dist
        (f := target) (g := (seq n m).1) ⟨x, hx⟩
      have hdistAmbient : dist target (seq n m).1 < δ := by
        omega
      have hdistx  :=
        lt_of_le_of_lt hpoint hdistAmbient
      have hsourceeq  := hsource n m
      let xK : ↑(K n) := ⟨x, hx⟩
      have hsourceval  :=
        congrArg (fun F : C(↑(K n), ℝ) => F xK) hsourceeq
      have htesteq : test (n, m) x = (seq n m).1 ⟨x, hx⟩ := by
        assumption_mod_cast
      rw [htesteq]
      calc
        ‖(seq n m).1 ⟨x, hx⟩ - g x‖ =
            dist ((seq n m).1 ⟨x, hx⟩) (g x) := (dist_eq_norm _ _).symm
        _ = dist (g x) ((seq n m).1 ⟨x, hx⟩) := dist_comm _ _
        _ < δ := hdistx
    · have hgzero  := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (hgs hx'))
      have hsourcezero : (test (n, m) : ℂ → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hx' => hx ((source n m).property.2 hx'))
      simpa [hgzero, hsourcezero] using hδ
  refine ⟨K, hKcompact, hKU, hKmono, hKcover, hKcofinal, test, ?_, ?_⟩
  all_goals assumption_mod_cast

end DOZZ.Proofs
