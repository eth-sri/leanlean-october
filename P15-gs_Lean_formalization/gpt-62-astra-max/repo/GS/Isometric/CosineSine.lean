module

public import GS.Isometric.Products
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

/-! Complete cosine-sine reduction, uniformly for real and complex matrices.
On the first block column use a common spectral basis, then complete the
orthogonal columns separately. The second block column is determined up to
one unitary change of basis. Zero columns require no limiting argument. -/
noncomputable section
open Matrix InnerProductSpace
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

def realDiag (𝕜 : Type*) [RCLike 𝕜] (c : Fin n → ℝ) : Square 𝕜 n := diagonal fun i => (c i : 𝕜)
@[simp] lemma realDiag_star (c : Fin n → ℝ) : (realDiag 𝕜 c)ᴴ = realDiag 𝕜 c := by
  rw [realDiag,diagonal_conjTranspose]; congr 1; ext; simp [RCLike.star_def]

private lemma diagonalize {A : Square 𝕜 n} (h : ∀ i j, i ≠ j → (Aᴴ*A) i j = 0) :
    ∃ U c, IsU U ∧ A = U * realDiag 𝕜 c := by
  let f (j : Fin n) := WithLp.toLp 2 (A.col j)
  have pair : Pairwise fun i j => inner 𝕜 (f i) (f j) = 0 := by
    intro i j hne
    simpa only [PiLp.inner_apply, RCLike.inner_apply', mul_apply, conjTranspose_apply,
      RCLike.star_def] using! h i j hne
  have dim : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis dim f
  have col (j) : f j = (‖f j‖ : 𝕜) • e j := by
    by_cases hz : f j = 0
    · simp [hz]
    · simp [e,gramSchmidtOrthonormalBasis_apply_of_orthogonal dim pair hz,smul_smul,hz]
  let b := EuclideanSpace.basisFun (Fin n) 𝕜
  refine ⟨b.toBasis.toMatrix e, fun j => ‖f j‖, b.toMatrix_orthonormalBasis_mem_unitary e, ?_⟩
  ext i j
  simpa only [realDiag, mul_diagonal, smul_eq_mul, mul_comm] using!
    congrArg (fun v : EuclideanSpace 𝕜 (Fin n) => v i) (col j)

lemma thin (A B : Square 𝕜 n) (h : Aᴴ*A + Bᴴ*B = 1) :
    ∃ U W V c s, IsU U ∧ IsU W ∧ IsU V ∧ A*V = U*realDiag 𝕜 c ∧ B*V = W*realDiag 𝕜 s := by
  let H := isHermitian_conjTranspose_mul_self A
  let V : Square 𝕜 n := H.eigenvectorUnitary
  have v : IsU V := H.eigenvectorUnitary.property
  have d : (A*V)ᴴ*(A*V) = diagonal (RCLike.ofReal ∘ H.eigenvalues) := by
    simpa only [V,Unitary.conjStarAlgAut_star_apply,star_eq_conjTranspose,conjTranspose_mul,Matrix.mul_assoc]
      using H.conjStarAlgAut_star_eigenvectorUnitary
  have e : (A*V)ᴴ*(A*V) + (B*V)ᴴ*(B*V) = 1 := calc
    _ = Vᴴ*(Aᴴ*A + Bᴴ*B)*V := by simp [Matrix.mul_assoc,Matrix.mul_add,Matrix.add_mul]
    _ = _ := by simp [h,v.1]
  obtain ⟨U,c,u,hu⟩ := diagonalize (A := A*V) fun i j hij => by rw [d]; simp [diagonal_apply,hij]
  rw [d] at e
  obtain ⟨W,s,w,hw⟩ := diagonalize (A := B*V) fun i j hij => by
    simpa [*] using congrFun (congrFun e i) j
  exact ⟨U,W,V,c,s,u,w,v,hu,hw⟩

end GS.Isometric
