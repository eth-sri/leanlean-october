/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.GramCompletion

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace OAI.EuclideanRamsey

abbrev FiniteEuclidean := ℕ →₀ ℝ
namespace FiniteEuclidean
instance core : InnerProductSpace.Core ℝ FiniteEuclidean where
  inner x y := (x * y).sum fun _ => id
  conj_inner_symm x y := by simp [mul_comm]
  re_inner_nonneg x := Finset.sum_nonneg fun n _ => mul_self_nonneg (x n)
  add_left x y z := by simp [add_mul, Finsupp.sum_add_index']
  smul_left x y r := by rw [show r • x * y = r • (x * y) by ext; simp [mul_assoc], Finsupp.sum_smul_index'] <;> simp [Finsupp.mul_sum]
  definite x h := by
    ext n
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun n _ => mul_self_nonneg (x n)).1 h n
instance : NormedAddCommGroup FiniteEuclidean := core.toNormedAddCommGroup
instance : InnerProductSpace ℝ FiniteEuclidean := .ofCore core.toCore
lemma inner_eq (x y : FiniteEuclidean) : ⟪x, y⟫ = x.sum fun n r => r * y n :=
  Finsupp.sum_of_support_subset _ Finsupp.support_mul_subset_left _ (by simp)

def reindex (f : ℕ → ℕ) (hf : f.Injective) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean :=
  (Finsupp.lmapDomain ℝ ℝ f).isometryOfInner fun x y => by
    simp [inner_eq, Finsupp.sum_mapDomain_index_inj hf, Finsupp.mapDomain_apply_of_injective hf]

def embed (d : ℕ) : Space d →ₗᵢ[ℝ] FiniteEuclidean :=
  (Finsupp.lmapDomain ℝ ℝ Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite ℝ ℝ _).symm.toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℝ _).toLinearMap).isometryOfInner fun x y => by
    simp [inner_eq, Finsupp.sum_mapDomain_index_inj Fin.val_injective, Finsupp.mapDomain_apply_of_injective Fin.val_injective, Finsupp.sum_fintype, PiLp.inner_apply, mul_comm]

lemma embed_apply d x (i : Fin d) : embed d x i = x i :=
  Finsupp.mapDomain_apply_of_injective Fin.val_injective _ i

lemma embed_outside d x n (hn : d ≤ n) : embed d x n = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ fun ⟨i, h⟩ => by omega

def flatten : List FiniteEuclidean → FiniteEuclidean
  | [] => 0
  | x :: l => reindex (2 * ·) (fun _ _ => by simp) x + reindex (2 * · + 1) (fun _ _ => by simp) (flatten l)

lemma flatten_cons x y (l k) : ‖flatten (x :: l) - flatten (y :: k)‖ ^ 2 = ‖x - y‖ ^ 2 + ‖flatten l - flatten k‖ ^ 2 := by
  rw [flatten, flatten, add_sub_add_comm, ← map_sub, ← map_sub, norm_add_sq_real, LinearIsometry.norm_map, LinearIsometry.norm_map]
  have (w : FiniteEuclidean) a : w.mapDomain (2 * · + 1) (2 * a) = 0 := Finsupp.mapDomain_of_notMem_range _ _ fun ⟨i, h⟩ => by grind
  simp [reindex, inner_eq, Finsupp.sum_mapDomain_index_inj (mul_right_injective₀ two_ne_zero), this]

lemma common_vertex r (hr : 0 < r) x y (hxy : ‖y-x‖≤2*r) :
    ∃ z : FiniteEuclidean,‖z-x‖=r ∧ ‖z-y‖=r := by
  obtain ⟨n, hn⟩ := (y - x).support.exists_notMem
  obtain ⟨e, he, hv⟩ : ∃ e, ‖e‖ = 1 ∧ ⟪y - x, e⟫ = 0 :=
    ⟨.single n 1, by rw [norm_eq_sqrt_real_inner, inner_eq]; simp, by rw [real_inner_comm, inner_eq]; simpa using hn⟩
  obtain ⟨s, ht⟩ : ∃ s, s^2 = r^2-‖y - x‖^2/4 := ⟨_, Real.sq_sqrt (by nlinarith [norm_nonneg (y - x)])⟩
  have key (c : ℝ) (hc : c ^ 2 = 1 / 4) : ‖c • (y - x) + s • e‖ = r :=
    (sq_eq_sq₀ (norm_nonneg _) hr.le).mp (by simp [norm_add_sq_real, norm_smul, he, real_inner_smul_left, real_inner_smul_right, hv, mul_pow, ht, hc]; ring)
  exact ⟨x + (1/2:ℝ) • (y - x) + s • e, by convert key (1/2) (by norm_num); abel, by convert key (-1/2) (by norm_num); module⟩

lemma unit_distance_constant {Y : Type*} r (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y,‖x-y‖=r → f x=f y) x y :
    f x=f y :=
  ((IsLocallyConstant.iff_exists_open f).mpr fun x => ⟨Metric.ball x (2*r), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), fun y hy => by
    obtain ⟨z, hz, hz'⟩ := common_vertex r hr x y (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
    exact (hf z y hz').symm.trans (hf z x hz)⟩).apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
