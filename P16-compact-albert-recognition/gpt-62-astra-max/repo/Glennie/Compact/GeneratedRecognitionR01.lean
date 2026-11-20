module
public import Glennie.Compact.NativeWordTableCoordinatesR01
@[expose] public section
namespace Glennie.SubmissionR03
noncomputable section
open Compact.NativeWordTableR01 Module

private def B : Basis (Fin 27) ℝ Albert := basisOfLinearIndependentOfCardEqFinrank'
  nativeWordValues nativeWords_independent (by simp [albert_finrank])
private theorem bw (i : Fin 27) : B i = nativeWordValues i := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' ..) i
private theorem ext₂ {X : Type*} [AddCommMonoid X] [Module ℝ X] (f g : Albert →ₗ[ℝ] Albert →ₗ[ℝ] X)
    (h : ∀ i k, f (B i) (B k) = g (B i) (B k)) : f = g := B.ext fun i => B.ext (h i)

private theorem word_mem {E : Type*} (e : E) (a : Fin 3 → E) (j : E → E → E) (K : Set E)
    (he : e ∈ K) (ha : ∀ i, a i ∈ K) (hp : ∀ x ∈ K, ∀ y ∈ K, j x y ∈ K) (i) : wordValues e a j i ∈ K := by
  let f (u v : K) : K := ⟨_,hp _ u.2 _ v.2⟩
  let w := wordValues (⟨e,he⟩ : K) (fun i => ⟨a i,ha i⟩) f i
  have eq : (w : E) = _ := word_map Subtype.val f j (fun _ _ => rfl) _ _ i
  exact eq ▸ w.2
theorem finite_word_marked_recognition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (h : Match27 e a j) :
    ∃! L : Albert →ₗ[ℝ] E,
      L 1 = e ∧
      (∀ i : Fin 3, L (nativeMarks i) = a i) ∧
      (∀ x y : Albert, L (jordan x y) = j (L x) (L y)) ∧
      (∀ x y : Albert, Inner.inner ℝ (L x) (L y) = inner x y) ∧
      Function.Injective L ∧ LinearMap.range L = generated e a j := by
  let v := candidateWordValues e a j
  let L := B.constr ℝ v
  have lw (i) : L (B i) = v i := B.constr_basis ℝ v i
  have iso (x y : Albert) : Inner.inner ℝ (L x) (L y) = inner x y := by
    have he := ext₂ ((innerₗ E).compl₁₂ L L) (innerₗ Albert) (fun i k => by
      change Inner.inner ℝ (L (B i)) (L (B k)) = inner (B i) (B k)
      rw [lw,lw,bw,bw]; exact h.gram i k)
    exact DFunLike.congr_fun (DFunLike.congr_fun he x) y
  have prod (x y : Albert) : L (jordan x y) = j (L x) (L y) := by
    suffices he : jordanLinear.compr₂ L = j.compl₁₂ L L from DFunLike.congr_fun (DFunLike.congr_fun he x) y
    apply ext₂; intro i k
    let u := jordan (B i) (B k); let p := j (v i) (v k)
    have mix : (innerₗ E p).comp L = innerₗ Albert u := by
      apply B.ext; intro l; change Inner.inner ℝ p (L (B l)) = inner u (B l)
      rw [lw]; simpa only [u,bw] using h.mixed i k l
    have sq : Inner.inner ℝ p p = inner u u := by simpa only [u,bw] using h.product_sq i k
    have m : Inner.inner ℝ p (L u) = inner u u := DFunLike.congr_fun mix u
    change L u = j (L (B i)) (L (B k)); rw [lw,lw]
    change L u = p
    apply sub_eq_zero.mp; apply (_root_.inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [_root_.inner_sub_left,_root_.inner_sub_right,_root_.inner_sub_right,real_inner_comm p (L u),m,sq,iso]; ring
  have eval (i) : L (nativeWordValues i) = v i := bw i ▸ lw i
  have unit : L 1 = e := eval 0
  have marks (i : Fin 3) : L (nativeMarks i) = a i := by
    fin_cases i <;> first | exact eval 1 | exact eval 2 | exact eval 3
  have inj : Function.Injective L := (show Albert →ₗᵢ[ℝ] E from
    ⟨L, fun x => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [← real_inner_self_eq_norm_sq,iso,native_norm_sq])⟩).injective
  refine ⟨L,⟨unit,marks,prod,iso,inj,le_antisymm ?_ ?_⟩,?_⟩
  · rintro _ ⟨x,rfl⟩; apply Submodule.mem_sInf.mpr; intro K hK
    rw [← B.sum_repr x,map_sum]; apply K.sum_mem; intro i _
    rw [map_smul,lw]; apply K.smul_mem
    exact word_mem e a (fun x y => j x y) K hK.1 hK.2.1 hK.2.2 _
  · exact sInf_le ⟨⟨1,unit⟩,fun i => ⟨_,marks i⟩,by rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩; exact ⟨_,prod x y⟩⟩
  · rintro M ⟨mu,ma,mj,_⟩; apply B.ext; intro i; rw [lw,bw]
    have mm : M ∘ nativeMarks = a := funext ma
    exact (word_map M jordan (fun x y => j x y) mj 1 nativeMarks i).trans (by rw [mu,mm]; rfl)
end
end Glennie.SubmissionR03
