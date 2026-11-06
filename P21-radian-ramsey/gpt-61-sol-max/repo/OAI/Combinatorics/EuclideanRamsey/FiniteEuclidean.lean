/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.TensorPresentation

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section




abbrev FiniteEuclidean := ℕ →₀ ℝ
namespace FiniteEuclidean

def product (x y : FiniteEuclidean) : ℝ :=
  x.sum (fun n r => r*y n)
instance core : InnerProductSpace.Core ℝ FiniteEuclidean where
  inner := product
  conj_inner_symm x y := by
    induction x using Finsupp.induction_linear with
    | zero => simp [product]
    | single a b =>
      by_cases hy : y a = 0 <;> simp [product,Finsupp.single_apply,Finsupp.sum,
        mul_comm,hy]
    | add x z hx hz =>
      simp_all [product,Finsupp.sum_add_index,mul_add,add_mul]
  re_inner_nonneg x := by
    change 0 ≤ x.sum (fun n r => r*x n)
    exact Finset.sum_nonneg (fun n _ => mul_self_nonneg _)
  add_left x y z := (Finsupp.linearCombination ℝ z).map_add x y
  smul_left x y r := (Finsupp.linearCombination ℝ y).map_smul r x
  definite x h := by
    change x.sum (fun n r => r*x n)=0 at h
    have hs :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => mul_self_nonneg _)).mp h
    apply Finsupp.ext
    aesop
instance : NormedAddCommGroup FiniteEuclidean := InnerProductSpace.Core.toNormedAddCommGroup (𝕜:=ℝ)
instance : InnerProductSpace ℝ FiniteEuclidean := InnerProductSpace.ofCore core.toCore
lemma norm_sq (x : FiniteEuclidean) : ‖x‖^2=x.sum (fun _ r => r^2) := by
  rw [← real_inner_self_eq_norm_sq]
  noncomm_ring [*]

def reindex (f : ℕ → ℕ) (hf : Function.Injective f) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap := Finsupp.lmapDomain ℝ ℝ f
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    exact Finsupp.sum_mapDomain_index_inj hf

def block (j : ℕ) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean :=
  reindex (Nat.pair j) (fun _m _n h => (Nat.pair_eq_pair.mp h).2)
open scoped RealInnerProductSpace
def embed (d : ℕ) : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap := (Finsupp.lmapDomain ℝ ℝ Fin.val).comp
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin d)).symm.toLinearMap.comp
      (EuclideanSpace.equiv (Fin d) ℝ).toLinearMap)
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,EuclideanSpace.norm_sq_eq]
    change (Finsupp.mapDomain Fin.val _).sum _ = _
    rw [Finsupp.sum_mapDomain_index_inj Fin.val_injective]
    rw [Finsupp.sum_fintype]
    · simp [*]
    · intro _; simp

lemma inner_block_ne (i j : ℕ) (hij : i≠j) (x y : FiniteEuclidean) :
    ⟪block i x,block j y⟫=0 := by
  change product (block i x) (block j y)=0
  unfold product
  change (x.mapDomain (Nat.pair i)).sum
    (fun n r => r*(y.mapDomain (Nat.pair j)) n)=0
  rw [Finsupp.sum_mapDomain_index_inj (fun _ _ h => (Nat.pair_eq_pair.mp h).2)]
  apply Finset.sum_eq_zero
  intro n hn
  dsimp only
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · aesop

def flatten (l : List FiniteEuclidean) : FiniteEuclidean :=
  ∑ i : Fin l.length,block i (l.get i)

lemma unit_distance_constant {Y : Type*} (r : ℝ) (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y,‖x-y‖=r → f x=f y) (x y : FiniteEuclidean) :
    f x=f y := by
  classical
  have hsmall x y (h : ‖y-x‖≤2*r) : f x=f y := by
    let v := y-x
    obtain ⟨n,hn⟩ := v.support.exists_notMem
    have hz := Finsupp.notMem_support_iff.mp hn
    let e := Finsupp.single n (1:ℝ)
    have he : ‖e‖ = 1 := by
      apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [norm_sq]
      simp [e]
    have hv : ⟪v,e⟫=0 := by
      rw [real_inner_comm]
      change product e v = 0
      simp [product,e,hz]
    let t := Real.sqrt (r^2-‖v‖^2/4)
    have ht0 : 0≤r^2-‖v‖^2/4 := by
      have hv0 := norm_nonneg v
      change ‖v‖≤2*r at h
      nlinarith [sq_nonneg (2*r-‖v‖)]
    have ht := Real.sq_sqrt ht0
    have hnorm (c : ℝ) (hc : c^2=1/4) : ‖c•v+t•e‖=r := by
      apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
      rw [norm_add_sq_real,norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
      simp [mul_pow]
      nlinarith
    apply (hf (x+(1/2:ℝ)•v+t•e) x ?_).symm.trans (hf _ y ?_)
    · rw [show x+(1/2:ℝ)•v+t•e-x=(1/2:ℝ)•v+t•e by module]
      exact hnorm _ (by norm_num)
    · rw [show x+(1/2:ℝ)•v+t•e-y=(-(1/2):ℝ)•v+t•e by dsimp [v]; module]
      exact hnorm _ (by norm_num)
  have hl : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Metric.ball_mem_nhds x (show 0 < 2*r by positivity)] with y hy
    exact (hsmall x y (by simpa [dist_eq_norm] using (Metric.mem_ball.mp hy).le)).symm
  exact hl.apply_eq_of_preconnectedSpace x y

end FiniteEuclidean
end

end OAI.EuclideanRamsey
