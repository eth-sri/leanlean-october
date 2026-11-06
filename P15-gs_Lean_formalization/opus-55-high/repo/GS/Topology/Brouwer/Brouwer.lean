module

/-
Copyright (c) 2025 Math_XMUM. All rights reserved.
Released under the MIT license; see THIRD_PARTY_LICENSE.txt.

Ported from math-xmum/Brouwer, commit c938f0f2b355adc9f07666c1c2c4002100406923 (2025-11-23),
Gametheory/Brouwer.lean, to the project's pinned mathlib v4.19.0.
Upstream: https://github.com/math-xmum/Brouwer
Only import/API compatibility and proof elaboration changes are intended.
-/
public import GS.Topology.Brouwer.Scarf
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable (n l : ℕ+) (i : Fin n)

abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}


instance TT.inhabited : Inhabited (TT n l) where
  default := ⟨fun i => if i = 0 then Fin.last l else 0, by simp [apply_ite Fin.val]⟩

instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective := by simp

variable {n l} in
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, fun _ => by positivity, by
  rw [← Finset.sum_div, div_eq_one_iff_eq (by simp)]; exact_mod_cast x.2⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex

lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : ∀ y, ∃ i ∈ C, ∀ x ∈ σ, toLex (y i, y) ≤ toLex (x i, x))
(h2 : σ.Nonempty):
  l < ∑ k ∈ C, (σ.image (fun x => (x k : ℕ))).min' (by simp_all) + C.card := by
  by_contra h_not
  let M' k := if k ∈ C then (σ.image (fun x => (x k : ℕ))).min' (by simp_all) + 1 else 0
  have hS : ∑ k, M' k ≤ l := by
    simp only [M', ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  let M k := M' k + if k = 0 then l - ∑ k, M' k else 0
  have hM : ∑ k, M k = l := by simp [M, Finset.sum_add_distrib]; omega
  obtain ⟨i, hi, h⟩ := h ⟨fun k => ⟨M k, Nat.lt_succ_of_le (hM ▸ Finset.single_le_sum (by simp) (Finset.mem_univ k))⟩, hM⟩
  obtain ⟨x, hx, hxm⟩ := Finset.mem_image.1 (Finset.min'_mem (σ.image (fun x => (x i : ℕ))) (by simp_all))
  refine (h x hx).not_gt (Prod.Lex.toLex_lt_toLex.2 (.inl (show (x i : ℕ) < M i by
    grind)))

theorem size_bound (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : ∀ y, ∃ i ∈ C, ∀ x ∈ σ, toLex (y i, y) ≤ toLex (x i, x))
    (hσ : σ.Nonempty) (i : Fin n) : ∃ m : ℕ, (i ∉ C → m = 0) ∧ ∀ z ∈ σ, m ≤ (z i : ℕ) ∧ (z i : ℕ) < m + n := by
  let m k := (σ.image (fun x => (x k : ℕ))).min' (by simp_all)
  have hm (z) (hz : z ∈ σ) (k) : m k ≤ z k := Finset.min'_le _ _ (by grind)
  have key : l < ∑ k ∈ C, m k + C.card := size_bound_key n l σ C h hσ
  have hC : C.card ≤ n := (Finset.card_le_univ C).trans (by simp)
  refine ⟨if i ∈ C then m i else 0, by simp_all, fun z hz => ?_⟩
  have h1 : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (z k : ℕ) := Finset.sum_le_sum (by grind)
  have h2 : ∑ k ∈ insert i C, (z k : ℕ) ≤ l := (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans_eq z.2
  split_ifs with hi
  · have h3 : ∑ k ∈ C.erase i, m k ≤ ∑ k ∈ C.erase i, (z k : ℕ) := Finset.sum_le_sum (by grind)
    rw [← Finset.add_sum_erase _ _ hi] at key h1
    rw [Finset.insert_eq_of_mem hi, ← Finset.add_sum_erase _ _ hi] at h2
    grind
  grind

section Brouwer

variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} :=
  have ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le (by simp) (x.2.2.trans y.2.2.symm).le
  (by aesop)

noncomputable def stdSimplex.pick (x  y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y

def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)

theorem Brouwer (hf : Continuous f): ∃ x , f x = x := by
  have key (ε : ℝ) (hε : 0 < ε) : ∃ x : stdSimplex ℝ (Fin n), ∀ i, x.1 i ≤ (f x).1 i + ε := by
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous hf) (ε / 2) (by positivity)
    obtain ⟨l, hl⟩ := exists_nat_gt (n / min δ (ε / 2))
    let L : ℕ+ := ⟨l + 1, by omega⟩
    have hL : n / (L : ℝ) < min δ (ε / 2) := by
      field_simp
      rw [div_lt_iff₀ (by positivity)] at hl
      simp [L]
      grind
    obtain ⟨σ, C, hd, hc⟩ := Scarf.scarf (r := fun i (x : TT n L) => toLex (x i, x))
      (fun i x y h => by simp_all) (Fcolor f) 0
    obtain ⟨i, hi, -⟩ := hd default
    obtain ⟨x, hx, -⟩ := hc i hi
    refine ⟨x, fun i => ?_⟩
    by_cases hi : i ∈ C
    · obtain ⟨y, hy, rfl⟩ := hc i hi
      have h1 : (y : stdSimplex ℝ (Fin n)).1 (Fcolor f y) ≤ (f y).1 (Fcolor f y) := (stdSimplex.pick _ _).2
      have h2 : dist (y : stdSimplex ℝ (Fin n)) x < min δ (ε / 2) := by
        rw [Subtype.dist_eq, dist_pi_lt_iff (by positivity)]
        intro j
        refine lt_of_le_of_lt ?_ hL
        simp only [TTtostdSimplex, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < L)]
        field_simp
        obtain ⟨m, -, hm⟩ := size_bound n L σ C hd ⟨x, hx⟩ j
        obtain ⟨a1, a2⟩ := hm x hx
        obtain ⟨b1, b2⟩ := hm y hy
        rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
        constructor <;> norm_cast <;> omega
      have h3 := (dist_le_pi_dist (f y).1 (f x).1 (Fcolor f y)).trans
        (hfδ (by grind)).le
      have h4 := (dist_le_pi_dist (y : stdSimplex ℝ (Fin n)).1 (x : stdSimplex ℝ (Fin n)).1 (Fcolor f y)).trans
        (h2.trans_le (min_le_right _ _)).le
      rw [Real.dist_eq, abs_le] at h3 h4
      grind
    · obtain ⟨m, hm0, hm⟩ := size_bound n L σ C hd ⟨x, hx⟩ i
      have := (hm x hx).2
      have h0 := (f x).2.1 i
      have : (x : stdSimplex ℝ (Fin n)).1 i ≤ n / L := by
        simp only [TTtostdSimplex]
        field_simp
        simp_all
        grind
      grind
  have hc (k : ℕ) : IsClosed {x : stdSimplex ℝ (Fin n) | ∀ i, x.1 i ≤ (f x).1 i + 1 / (k + 1)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le ((continuous_apply i).comp continuous_subtype_val)
      (((continuous_apply i).comp (continuous_subtype_val.comp hf)).add continuous_const)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k : ℕ => {x : stdSimplex ℝ (Fin n) | ∀ i, x.1 i ≤ (f x).1 i + 1 / (k + 1)})
    (fun k x hx i => (hx i).trans (by gcongr; simp))
    (fun k => key _ (by positivity))
    (hc 0).isCompact hc
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hz
  have hle (i) : z.1 i ≤ (f z).1 i :=
    le_of_forall_pos_le_add fun ε hε => by
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      linarith [hz k i]
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  exact ((Finset.sum_eq_sum_iff_of_le (by grind)).1 (by rw [z.2.2, (f z).2.2]) i
    (Finset.mem_univ _)).symm

end Brouwer
