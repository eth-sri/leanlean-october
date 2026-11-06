/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.GramCompletion

@[expose] public section

namespace OAI.EuclideanRamsey
noncomputable section
open scoped BigOperators RealInnerProductSpace

universe uValue

def FiniteEuclidean := ℕ →₀ ℝ

namespace FiniteEuclidean

instance : AddCommGroup FiniteEuclidean := inferInstanceAs (AddCommGroup (ℕ →₀ ℝ))
instance : Module ℝ FiniteEuclidean := inferInstanceAs (Module ℝ (ℕ →₀ ℝ))

def coords (x : FiniteEuclidean) : ℕ →₀ ℝ := x

abbrev product (x y : FiniteEuclidean) : ℝ :=
  (coords x).sum fun n r => r * coords y n

instance core : InnerProductSpace.Core ℝ FiniteEuclidean where
  inner := product
  conj_inner_symm x y := by
    dsimp [product]
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_union_right : (coords y).support ⊆ (coords x).support ∪ (coords y).support) _ (by simp),
      Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (by simp)]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  re_inner_nonneg x := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  add_left x y z := Finsupp.sum_add_index (by simp) fun _ _ _ _ => add_mul _ _ _
  smul_left x y r := by
    change (r • coords x).sum (fun n t => t * coords y n) = r * product x y
    rw [Finsupp.sum_smul_index (by simp)]
    simp only [product, Finsupp.mul_sum, mul_assoc]
  definite x h := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg fun n _ => mul_self_nonneg (coords x n)).mp h
    refine Finsupp.ext fun n => ?_
    by_cases hn : n ∈ (coords x).support
    · exact mul_self_eq_zero.mp (hs n hn)
    · exact Finsupp.notMem_support_iff.mp hn

instance : NormedAddCommGroup FiniteEuclidean := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ FiniteEuclidean := InnerProductSpace.ofCore core.toCore

lemma norm_sq (x : FiniteEuclidean) : ‖x‖ ^ 2 = (coords x).sum fun _ r => r ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change product x x = _
  simp [product, Finsupp.sum, sq]

def block (j : ℕ) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap :=
    { toFun := fun x => (coords x).mapDomain (Nat.pair j)
      map_add' := fun _ _ => Finsupp.mapDomain_add
      map_smul' := fun c x => Finsupp.mapDomain_smul c (coords x) }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, norm_sq]
    exact Finsupp.sum_mapDomain_index_inj fun _ _ h => (Nat.pair_eq_pair.mp h).2

def embed (d : ℕ) : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap :=
    { toFun := fun x => (Finsupp.equivFunOnFinite.symm fun i => x i).mapDomain Fin.val
      map_add' := fun x y => by
        change Finsupp.mapDomain _ _ = _ + _
        rw [← Finsupp.mapDomain_add]; congr 1; ext; simp
      map_smul' := fun r x => by
        change Finsupp.mapDomain _ _ = r • (_ : ℕ →₀ ℝ)
        rw [← Finsupp.mapDomain_smul]; congr 1; ext; simp }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, EuclideanSpace.norm_sq_eq]
    change (Finsupp.mapDomain Fin.val _).sum _ = _
    rw [Finsupp.sum_mapDomain_index_inj Fin.val_injective, Finsupp.sum_fintype _ _ fun _ => by simp]
    simp [Real.norm_eq_abs, sq_abs]

lemma inner_block_ne (i j : ℕ) (hij : i ≠ j) (x y : FiniteEuclidean) :
    ⟪block i x, block j y⟫ = 0 := by
  change ((coords x).mapDomain (Nat.pair i)).sum (fun n r => r * ((coords y).mapDomain (Nat.pair j)) n) = 0
  rw [Finsupp.sum_mapDomain_index_inj fun _ _ h => (Nat.pair_eq_pair.mp h).2]
  refine Finset.sum_eq_zero fun n _ => ?_
  dsimp only
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · rintro ⟨m, hm⟩; exact hij (Nat.pair_eq_pair.mp hm).1.symm

def flatten : List FiniteEuclidean → FiniteEuclidean
  | [] => 0
  | x :: l => block 0 x + block 1 (flatten l)

lemma unit_distance_constant {Y : Type uValue} (r : ℝ) (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y, ‖x - y‖ = r → f x = f y) (x y : FiniteEuclidean) :
    f x = f y := by
  have hsmall (x y : FiniteEuclidean) (h : ‖y - x‖ ≤ 2 * r) : f x = f y := by
    classical
    let v := y - x
    obtain ⟨n, hn⟩ := (coords v).support.exists_notMem
    let e : FiniteEuclidean := Finsupp.single n 1
    have he : ‖e‖ = 1 := by
      apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [norm_sq]; simp [e, coords]
    have hv : ⟪v, e⟫ = 0 := by
      rw [real_inner_comm]
      change product e v = 0
      simpa [product, e, coords] using Finsupp.notMem_support_iff.mp hn
    let t := Real.sqrt (r ^ 2 - ‖v‖ ^ 2 / 4)
    have ht : t ^ 2 = r ^ 2 - ‖v‖ ^ 2 / 4 :=
      Real.sq_sqrt (by change ‖v‖ ≤ 2 * r at h; nlinarith [norm_nonneg v, sq_nonneg (2 * r - ‖v‖)])
    let z := x + (1 / 2 : ℝ) • v + t • e
    have hz1 : ‖z - x‖ = r := by
      apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
      rw [show z - x = (1 / 2 : ℝ) • v + t • e by dsimp [z]; abel, norm_add_sq_real, norm_smul, norm_smul, he,
        real_inner_smul_left, real_inner_smul_right, hv]
      simp only [Real.norm_eq_abs, sq_abs, mul_pow]; nlinarith
    have hz2 : ‖z - y‖ = r := by
      apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
      rw [show z - y = (-(1 / 2) : ℝ) • v + t • e by dsimp [z, v]; module, norm_add_sq_real, norm_smul, norm_smul, he,
        real_inner_smul_left, real_inner_smul_right, hv]
      simp only [Real.norm_eq_abs, sq_abs, mul_pow]; nlinarith
    exact (hf z x hz1).symm.trans (hf z y hz2)
  have hl : IsLocallyConstant f := (IsLocallyConstant.iff_exists_open f).mpr fun x =>
    ⟨Metric.ball x (2 * r), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), fun y hy =>
      (hsmall x y (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le)).symm⟩
  exact hl.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)

end FiniteEuclidean
end
end OAI.EuclideanRamsey

