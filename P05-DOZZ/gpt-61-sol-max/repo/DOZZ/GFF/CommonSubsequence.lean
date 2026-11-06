/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-!
# DOZZ.GFF.CommonSubsequence

Diagonal extraction for countably many scalar limits in measure. This is the probabilistic
bookkeeping needed to put all local Fourier-mode limits on one full-measure event.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ

private structure GFFSubsequenceStage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → ℕ → Ω → ℝ) (g : ℕ → Ω → ℝ) (m : ℕ) where
  seq : ℕ → ℕ
  strict : StrictMono seq
  converges : ∀ i, i < m → ∀ᵐ ω ∂μ,
    Tendsto (fun n => F (seq n) i ω) atTop (𝓝 (g i ω))
  next : ℕ → ℕ
  next_strict : StrictMono next
  next_converges : ∀ᵐ ω ∂μ,
    Tendsto (fun n => F (seq (next n)) m ω) atTop (𝓝 (g m ω))

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (μ : Measure Ω) (F : ℕ → ℕ → Ω → ℝ) (g : ℕ → Ω → ℝ) (hF : ∀ i, TendstoInMeasure μ (fun n ω => F n i ω) atTop (g i))

include Ω _inst1 μ F g hF in
private noncomputable def gffSubsequenceStageZero  :
      GFFSubsequenceStage μ F g 0 := by
  classical
  let hseq := (hF 0).exists_seq_tendsto_ae
  let ψ : ℕ → ℕ := Classical.choose hseq
  have hψ  := (Classical.choose_spec hseq).1
  have hψae := (Classical.choose_spec hseq).2
  exact ⟨id, strictMono_id, fun i hi => by omega, ψ, hψ, hψae⟩

include Ω _inst1 μ F g hF in
private noncomputable def gffSubsequenceStageSucc 
    (m : ℕ) (d : GFFSubsequenceStage μ F g m) :
      GFFSubsequenceStage μ F g (m + 1) := by
  classical
  let φ : ℕ → ℕ := d.seq ∘ d.next
  have hφ  := d.strict.comp d.next_strict
  let hnew := (hF (m + 1)).comp hφ.tendsto_atTop
  let hseq := hnew.exists_seq_tendsto_ae
  let ψ : ℕ → ℕ := Classical.choose hseq
  have hψ  := (Classical.choose_spec hseq).1
  have hψae := (Classical.choose_spec hseq).2
  refine ⟨φ, hφ, ?_, ψ, hψ, hψae⟩
  intro i hi
  by_cases him : i = m
  · subst i
    exact d.next_converges
  · have him : i < m := by omega
    filter_upwards [d.converges i him] with ω hω
    exact hω.comp d.next_strict.tendsto_atTop

include Ω _inst1 μ F g hF in
private noncomputable def gffSubsequenceStages  :
      ∀ m, GFFSubsequenceStage μ F g m := by
  classical
  refine Nat.rec ?_ ?_
  · exact gffSubsequenceStageZero μ F g hF
  · intro m d
    exact gffSubsequenceStageSucc μ F g hF m d



include Ω _inst1 μ F g hF in
private theorem gffSubsequenceStages_range_mono  (m : ℕ) :
      Set.range (gffSubsequenceStages μ F g hF (m + 1)).seq ⊆
        Set.range (gffSubsequenceStages μ F g hF m).seq := by
  intro x hx
  continuity

include Ω _inst1 μ F g hF in
private theorem gffSubsequenceStages_range_le  :
    ∀ i m, i ≤ m →
      Set.range (gffSubsequenceStages μ F g hF m).seq ⊆
        Set.range (gffSubsequenceStages μ F g hF i).seq := by
  intro i m him
  induction m with
  | zero =>
      continuity
  | succ m ih =>
      by_cases h : i ≤ m
      · exact (gffSubsequenceStages_range_mono μ F g hF m).trans (ih h)
      grind

private theorem strictMono_nat_le_self {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (n : ℕ) :
    n ≤ ψ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hs : ψ n < ψ (n + 1) := hψ (by omega)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hs)

include Ω _inst1 μ F g hF in
/-- From countably many scalar convergences in measure, extract one increasing subsequence along
which every coordinate converges almost everywhere. The diagonal sequence uses nested subsequences,
so the limit event is a countable intersection rather than a family of unrelated testwise events. -/
theorem exists_common_subseq_tendsto_ae  :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ, ∀ i,
      Tendsto (fun n => F (ns n) i ω) atTop (𝓝 (g i ω)) := by
  classical
  let stages := gffSubsequenceStages μ F g hF
  let diag : ℕ → ℕ := fun n => (stages n).seq n
  have hdiag : StrictMono diag := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hidx : n < (stages n).next (n + 1) := by
      have := strictMono_nat_le_self (stages n).next_strict (n + 1)
      omega
    exact (stages n).strict hidx
  have hconv (i : ℕ) : ∀ᵐ ω ∂μ,
      Tendsto (fun n => F (diag n) i ω) atTop (𝓝 (g i ω)) := by
    let φ := (stages (i + 1)).seq
    have hφ : StrictMono φ := (stages (i + 1)).strict
    have hφconv  :=
      (stages (i + 1)).converges i (by omega)
    have hmem (n : ℕ) (hn : i < n) : diag n ∈ Set.range φ := by
      have hsubset := gffSubsequenceStages_range_le μ F g hF (i + 1) n (by omega)
      exact hsubset ⟨n, rfl⟩
    let idx : ℕ → ℕ := fun n =>
      if hn : i < n then Classical.choose (hmem n hn) else 0
    have hidx_eq : ∀ᶠ n in atTop, φ (idx n) = diag n := by
      filter_upwards [Filter.eventually_gt_atTop i] with n hn
      simp [idx, hn, Classical.choose_spec (hmem n hn)]
    have hidx_tendsto : Tendsto idx atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have hlarge  :=
        hdiag.tendsto_atTop.eventually_ge_atTop (φ b)
      filter_upwards [hlarge, hidx_eq] with n hlarge heq
      by_contra hidx
      have hlt : idx n < b := by omega
      have hphi  := hφ hlt
      omega
    filter_upwards [hφconv] with ω hω
    have hcomp := hω.comp hidx_tendsto
    have hEq : (fun n => F (φ (idx n)) i ω) =ᶠ[atTop]
        (fun n => F (diag n) i ω) := by
      filter_upwards [hidx_eq] with n hn
      rw [hn]
    exact hcomp.congr' hEq
  have hae  := ae_all_iff.mpr hconv
  exact ⟨diag, hdiag, hae⟩

end DOZZ

end
