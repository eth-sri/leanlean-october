module
public import OAI.Combinatorics.EuclideanRamsey.SignedRows
@[expose] public noncomputable section
open Polynomial Matrix Algebra.TensorProduct
open scoped TensorProduct
namespace OAI.EuclideanRamsey.Radian

private abbrev labels := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)
private def outer {R : Type} [Mul R] (x y : Fin 3 → R) (j : Fin 9) :=
  x (labels.symm j).2 * y (labels.symm j).1
private def nodes {R : Type} [CommRing R] (s t : R) := outer (s^·.val) (t^·.val)
def form (z : ℂ) (x : Fin 3 → ℂ) (k : Fin 9) := ∑ j, (z^k.val)^j.val * x j
def Projects (z : ℂ) := ∀ w : Fin 3 → ℂ, ∃ f : Fin 9 → ℂ → ℝ, ∀ x, ∑ i, f i (form z x i) = ((∑ j, x j*w j)^2).re

/-- Flat base change preserves regularity of the Vandermonde determinant. -/
private lemma base_change {J B : Type} [CommRing J] [CommRing B] [IsDomain B] [Algebra J B] [Algebra J ℂ]
    [Module.Flat J ℂ] (C : ℂ →+* B) (e : B →ₐ[J] ℂ) (he : ∀ x, e (C x) = x) (u : J)
    (z : ℂ) (ht : algebraMap J ℂ u = z) (hd : Function.Injective (nodes (C z) (algebraMap J B u))) : Projects z := by
  let A := B ⊗[J] ℂ
  let L := algebraMap B A
  let r : ℂ →+* A := includeRight.toRingHom
  let l := L.comp C
  let μ := (productMap e (AlgHom.id J ℂ)).toRingHom
  have hl x : μ (l x) = x := (productMap_left_apply e _ _).trans (he x)
  have hr x : μ (r x) = x := productMap_right_apply e _ x
  let M := (vandermonde (nodes (l z) (r z))).transpose
  have hinj : Function.Injective M.mulVec := by
    apply mulVec_injective_of_det_mem_nonZeroDivisors
    have h : L (algebraMap J B u) = r z := ht ▸ DFunLike.congr_fun (includeLeftRingHom_comp_algebraMap ..) u
    let V := vandermonde (nodes (C z) (algebraMap J B u))
    have hV : L.mapMatrix V = vandermonde (nodes ((L.comp C) z) (r z)) := by ext; simp [V,nodes,outer,← h]
    rw [det_transpose,← hV,← RingHom.map_det]
    apply IsRegular.mem_nonZeroDivisors ∘ isLeftRegular_iff_isRegular.mp
    exact IsSMulRegular.of_flat (S:=A) (IsRegular.of_ne_zero (det_vandermonde_ne_zero_iff.mpr hd)).left
  intro w
  let p := outer (l ∘ w) (r ∘ w)
  let E := (Complex.reAddGroupHom.comp μ.toAddMonoidHom).comp (Fintype.linearCombination A p).toAddMonoidHom
  let T := M.mulVecLin.toAddMonoidHom
  obtain ⟨F,hF⟩ := coordinate_potentials T E (by rw [T.ker_eq_bot hinj]; simp)
  refine ⟨fun i b => F i (l b * r b),fun x => ?_⟩
  let v := outer (l ∘ x) (r ∘ x)
  have val (i) : M.mulVec v i = l (form z x i)*r (form z x i) := by
    rw [mulVec,dotProduct,← labels.sum_comp]
    simp [M,nodes,outer,v,form,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,mul_pow,mul_mul_mul_comm,pow_right_comm _ i.val]
  have h := hF v
  change ∑ i, F i (M.mulVec v i) = (μ (∑ j, v j*p j)).re at h
  simp only [val] at h
  rw [h,← labels.sum_comp]; simp [v,p,outer,hl,hr,Fintype.sum_prod_type,sq,Finset.sum_mul,Finset.mul_sum,mul_mul_mul_comm]

lemma pow_inj {z : ℂ} (ht : Transcendental ℚ z) : Function.Injective (fun n : ℕ => z^n) := by
  intro m n h
  have eq : (X : ℚ[X])^m = X^n := transcendental_iff_injective.mp ht (by aesop)
  simpa using congrArg natDegree eq

theorem projection {z : ℂ} (ht : Transcendental ℚ z) : Projects z := by
  let := (aeval (R:=ℚ) z).toRingHom.toAlgebra
  have : Module.IsTorsionFree ℚ[X] ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp ht)
  let := Polynomial.algebra ℚ ℂ
  let e : ℂ[X] →ₐ[ℚ[X]] ℂ := ⟨evalRingHom z, fun p => eval_map ..⟩
  apply base_change C e (fun _ => eval_C) X z (aeval_X z)
  intro i j eq
  have eq := congrArg (eval (z^3)) eq
  simp [nodes,outer,← pow_mul,← pow_add] at eq
  exact Fin.ext (by simpa [labels,finProdFinEquiv,Nat.mod_add_div] using pow_inj ht eq)
end OAI.EuclideanRamsey.Radian
