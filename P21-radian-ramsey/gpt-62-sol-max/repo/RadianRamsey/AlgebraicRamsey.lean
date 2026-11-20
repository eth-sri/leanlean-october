module

public import OAI.Combinatorics.EuclideanRamsey.GramCompletion
public import OAI.Combinatorics.EuclideanRamsey.CorrectionPaths
public import OAI.Combinatorics.EuclideanRamsey.ColoringCompactness

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct (tmul_mul_tmul)
open Algebra.FormallyUnramified (elem one_tmul_mul_elem lmul_elem)
open Finset
namespace OAI.EuclideanRamsey

/-- Change a diagonal tensor presentation so that its negative coefficients
have arbitrarily small quadratic cost under a distinguished real functional. -/
private lemma rebalance {W ι : Type} [AddCommGroup W] [Module ℚ W] [Fintype ι]
    (b : ι → W) (c : ι → ℚ) (f : W →ₗ[ℚ] ℝ)
    (hf : ∑ j, (c j : ℝ) * f (b j)^2 = 1) (D : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (B : Option ι → W) (C : Option ι → ℚ),
      (∑ j, C j • (B j ⊗ₜ[ℚ] B j)) = ∑ j, c j • (b j ⊗ₜ[ℚ] b j) ∧
      D * (∑ j, max (-(C j : ℝ)) 0 * f (B j)^2) < η := by
  let t : ι → ℝ := f ∘ b
  let A (x : ι → ℝ) := ∑ j, (c j : ℝ) * x j ^ 2
  let V (x : ι → ℝ) := ∑ j, (c j : ℝ) * x j * t j
  let E (x : ι → ℝ) := D * (max (A x-2) 0 * (V x)^2 +
    ∑ j, max (-(c j : ℝ)) 0 * (t j - x j * V x)^2)
  have hV : V t = 1 := by grind
  have hE : E t = 0 := by aesop
  have he : Continuous E := by unfold E A V; fun_prop
  have hd : DenseRange (fun x : ι → ℚ => fun j => (x j : ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨r,hr⟩ := hd.exists_mem_open (isOpen_lt he continuous_const) ⟨t,by simpa [hE] using hη⟩
  let a := ∑ j, c j * r j^2
  let z := ∑ j, (c j * r j) • b j
  have hzf : f z = V (fun j => (r j : ℝ)) := by simp [z,V,t,Rat.smul_def]
  refine ⟨Option.elim' z (fun j => b j - r j • z), Option.elim' (2-a) c, ?_, ?_⟩
  · simp only [Fintype.sum_option, Option.elim'_none, Option.elim'_some]
    simp only [TensorProduct.sub_tmul,TensorProduct.tmul_sub,TensorProduct.smul_tmul',
      TensorProduct.tmul_smul,smul_sub,smul_smul,Finset.sum_sub_distrib,← pow_two]
    simp_rw [TensorProduct.smul_tmul _ z, ← TensorProduct.tmul_sum,
      ← TensorProduct.sum_tmul, ← Finset.sum_smul]
    simp only [TensorProduct.tmul_smul]; module
  · simpa [E,A,t,a,hzf,Rat.smul_def] using hr

lemma diagonalCertificate_of_algebraic {s d : ℕ} (a : Fin s → Space d)
    (hA : ∀ i j, IsAlgebraic ℚ (a i j)) (hS : ∀ i, ∑ j, (a i j)^2 = 1)
    (η : ℝ) (hη : 0 < η) : DiagonalCertificate a η := by
  classical
  let S := Set.range (fun ij : Fin s × Fin d => a ij.1 ij.2)
  let F := IntermediateField.adjoin ℚ S
  let x (i : Fin s) (j : Fin d) : F :=
    ⟨a i j, IntermediateField.subset_adjoin ℚ S (Set.mem_range_self (i,j))⟩
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin (S:=S)
    (by rintro _ ⟨⟨i,j⟩,rfl⟩; exact (hA i j).isIntegral)
  have := Algebra.FormallyUnramified.of_isSeparable ℚ F
  let t := elem ℚ F
  let σ := Algebra.TensorProduct.comm ℚ F F
  let E := t * σ t
  have hσ : σ E = E := by
    change σ (t * σ t) = _
    rw [map_mul,show σ (σ t) = t from TensorProduct.comm_comm ℚ F F t,mul_comm]
  obtain ⟨n,u,v,h⟩ := TensorProduct.exists_sum_tmul_eq E
  let ι := Fin n × Bool
  let b₀ (p : ι) := if p.2 then u p.1+v p.1 else u p.1-v p.1
  let c₀ (p : ι) : ℚ := if p.2 then 1/4 else -1/4
  have he₀ : ∑ j, c₀ j • (b₀ j ⊗ₜ[ℚ] b₀ j) = E := by
    conv_rhs => rw [show E = (1/2:ℚ) • (E+σ E) by rw [hσ]; module]
    rw [Fintype.sum_prod_type,h,map_sum,← sum_add_distrib,smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [b₀,c₀,σ,TensorProduct.add_tmul,TensorProduct.tmul_add,TensorProduct.sub_tmul,TensorProduct.tmul_sub]
    module
  have ht : Algebra.TensorProduct.lmul' ℚ t = 1 := lmul_elem
  have hc : (Algebra.TensorProduct.lmul' ℚ).comp σ.toAlgHom = Algebra.TensorProduct.lmul' ℚ :=
    Algebra.TensorProduct.ext' (fun x y => mul_comm y x)
  let φ := F.val.comp (Algebra.TensorProduct.lmul' ℚ)
  have hh : Algebra.TensorProduct.lmul' ℚ (σ t) = 1 := (congrArg (fun f => f t) hc).trans ht
  have hval {τ : Type} [Fintype τ] {u : τ → F} {g : τ → ℚ}
      (hu : ∑ j, g j • (u j ⊗ₜ[ℚ] u j) = E) : ∑ j, (g j:ℝ) * F.val (u j)^2 = 1 := by
    simpa [φ,E,ht,hh,Rat.smul_def,pow_two] using congrArg φ hu
  obtain ⟨b,c,hbc,hneg⟩ := rebalance b₀ c₀ F.val.toLinearMap (hval he₀) d hη
  have h' : (∑ j, c j • (b j ⊗ₜ[ℚ] b j)) = E := hbc.trans he₀
  have hb := hval h'
  have hE (x : F) : (x ⊗ₜ[ℚ] x) * E = ((x^2) ⊗ₜ[ℚ] (1:F)) * E := by
    dsimp only [E]
    rw [show x ⊗ₜ[ℚ] x = (x ⊗ₜ[ℚ] (1:F)) * ((1:F) ⊗ₜ[ℚ] x) by simp [tmul_mul_tmul],
      mul_assoc _ _ (t*σ t),← mul_assoc _ t,one_tmul_mul_elem]
    simp [t,tmul_mul_tmul,← mul_assoc,pow_two]
  refine ⟨_,inferInstance,F.val ∘ b,c,fun i => ?_,hb,hneg⟩
  · let f := Algebra.TensorProduct.map F.val F.val
    have hl (j : Fin d) : (∑ l, c l • ((a i j * F.val (b l)) ⊗ₜ[ℚ] (a i j * F.val (b l)))) =
        f (((x i j ^ 2) ⊗ₜ[ℚ] (1:F))*E) := by
      rw [← hE, ← h', mul_sum, map_sum]
      simp [x,f,map_smul,mul_smul_comm,tmul_mul_tmul]
    have h : (∑ j, (x i j)^2) = 1 := F.val.injective (by simpa [x] using hS i)
    simp only [Function.comp_apply,hl]
    rw [← map_sum,← sum_mul,← TensorProduct.sum_tmul,h,← Algebra.TensorProduct.one_def,one_mul,← h',map_sum]
    simp [f,map_smul]

theorem ramsey_of_algebraic {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s)
    (ha : Function.Injective a) (hA : ∀ i j, IsAlgebraic ℚ (a i j))
    (hS : ∀ i, ∑ j, (a i j)^2 = 1) : Ramsey a := by
  apply paths_ramsey a
  dsimp only
  intro ε hε
  have hs' : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
  let η := ε/3
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨τ,hτ,M,hM,f,g,hf,hg,hperm⟩ := diagonal_two_scale a (by omega) η (diagonalCertificate_of_algebraic a hA hS η hη)
  let := hτ
  let δ := M*η/s
  obtain ⟨w,lmb,μ,hp,hm,hlmb,hr⟩ := permutation_equal_endpoints a ha f g
    (M*(1+η)) (M*η) δ (by positivity) (by positivity) (by dsimp [δ]; positivity) hf hg hperm
  refine ⟨w,lmb,μ,hp,hm,hlmb,hr.trans_lt ?_⟩
  dsimp [δ,η]
  field_simp
  nlinarith [sq_nonneg ε]

end OAI.EuclideanRamsey
