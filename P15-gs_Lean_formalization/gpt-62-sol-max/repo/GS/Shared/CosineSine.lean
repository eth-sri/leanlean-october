module

public import GS.Shared.BlockCoordinates

public import GS.OriginalLocalModel

public import Mathlib.Analysis.Matrix.Spectrum

public import Mathlib.Analysis.SpecialFunctions.Sqrt

public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Mathlib.Tactic.LinearCombination

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators ComplexConjugate ComplexOrder

namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜]
/-- A square matrix with real diagonal Gram matrix has a unitary
left factor, including at zero diagonal entries. -/
theorem exists_unitary_mul_sqrt_diagonal {n : ℕ} (A : M 𝕜 n) (v : Fin n → ℝ)
    (hA : Aᴴ * A = diagonal (fun i => (v i : 𝕜))) :
    ∃ U : M 𝕜 n, Unitary U ∧ A = U * diagonal (fun i => (Real.sqrt (v i) : 𝕜)) ∧
      ∀ i, Real.sqrt (v i) ^ 2 = v i := by
  classical
  let d i := Real.sqrt (v i)
  have hd (i : Fin n) : d i ^ 2 = v i := Real.sq_sqrt <| RCLike.ofReal_nonneg.mp
    ((Matrix.posSemidef_diagonal_iff.mp (hA ▸ Matrix.posSemidef_conjTranspose_mul_self A)) i)
  let e₀ := EuclideanSpace.basisFun (Fin n) 𝕜
  let f : Fin n → EuclideanSpace 𝕜 (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  have hgram (i j : Fin n) : ⟪f i, f j⟫_𝕜 = if i = j then (d i : 𝕜) ^ 2 else 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change (Aᴴ * A) i j = _
    simp [hA, diagonal_apply, ← RCLike.ofReal_pow, hd]
  let u : Fin n → EuclideanSpace 𝕜 (Fin n) := fun j => ((d j : 𝕜))⁻¹ • f j
  let s : Set (Fin n) := {i | d i ≠ 0}
  have hv : Orthonormal 𝕜 (s.domRestrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪((d i : 𝕜))⁻¹ • f i, ((d j : 𝕜))⁻¹ • f j⟫_𝕜 = _
    rw [inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · subst j
      have hd : d i ≠ 0 := i.property
      simp [hd, pow_two]
    · simp [hij, show (i : Fin n) ≠ (j : Fin n) from fun h => hij (Subtype.ext h)]
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n))
  refine ⟨e₀.toBasis.toMatrix e, Unitary.of_conjTranspose_mul
    (Matrix.mem_unitaryGroup_iff'.mp (e₀.toMatrix_orthonormalBasis_mem_unitary e)), ?_, hd⟩
  have hcol (j : Fin n) : (d j : 𝕜) • e j = f j := by
    by_cases h : d j = 0
    · have hf := inner_self_eq_zero.mp ((hgram j j).trans (by simp [h]))
      simp [h,hf]
    · rw [he j h]
      simp [u, smul_smul, h]
  ext i j
  rw [Matrix.mul_diagonal, mul_comm]
  change A i j = (d j : 𝕜) * e₀.repr (e j) i
  simpa [f,e₀,RCLike.real_smul_eq_coe_mul] using congrArg (fun w : EuclideanSpace 𝕜 (Fin n) => w i) (hcol j).symm

/-- Simultaneous unitary reduction of two square blocks with orthonormal
stacked columns, including repeated eigenvalues and zero columns. -/
theorem exists_thin_cs {n : ℕ} (A B : M 𝕜 n)
    (h : Aᴴ * A + Bᴴ * B = 1) :
    ∃ (U₁ U₂ V : M 𝕜 n) (c s : Fin n → ℝ),
      Unitary U₁ ∧ Unitary U₂ ∧ Unitary V ∧
      (∀ i, c i ^ 2 + s i ^ 2 = 1) ∧
      A * V = U₁ * diagonal (fun i => (c i : 𝕜)) ∧
      B * V = U₂ * diagonal (fun i => (s i : 𝕜)) := by
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let V : M 𝕜 n := hH.eigenvectorUnitary
  let d : Fin n → ℝ := hH.eigenvalues
  have hV : Unitary V := hH.eigenvectorUnitary.property
  let e := _root_.Unitary.conjStarAlgAut 𝕜 _ (star hH.eigenvectorUnitary)
  have hmul (X : M 𝕜 n) : (X * V)ᴴ * (X * V) = e (Xᴴ * X) := by
    simp [e, V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hdiag : e (Aᴴ * A) = diagonal (fun i => (d i : 𝕜)) :=
    hH.conjStarAlgAut_star_eigenvectorUnitary
  have hAV := (hmul A).trans hdiag
  have hBV : (B * V)ᴴ * (B * V) = diagonal (fun i => ((1 - d i : ℝ) : 𝕜)) := by
    rw [hmul, eq_sub_of_add_eq' h, map_sub, map_one, hdiag]
    simpa only [RCLike.ofReal_sub, RCLike.ofReal_one, diagonal_one] using
      (diagonal_sub (fun _ : Fin n => (1 : 𝕜)) (fun i => (d i : 𝕜)))
  obtain ⟨U₁, hU₁, he₁, hc⟩ := exists_unitary_mul_sqrt_diagonal _ _ hAV
  obtain ⟨U₂, hU₂, he₂, hs⟩ := exists_unitary_mul_sqrt_diagonal _ _ hBV
  refine ⟨U₁, U₂, V, _, _, hU₁, hU₂, hV, ?_, he₁, he₂⟩
  intro i
  rw [hc, hs]
  ring

variable {k b p : ℕ}

abbrev shuffleIndex (k b : ℕ) : Fin b × Fin k ≃ Fin (k*b) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (GS.scalarShuffle k b))

theorem shuffleIndex_label (x : Fin b × Fin k) : (shuffleIndex k b x).val / k = x.1.val := by
  have val_cast {a b : ℕ} (h : a = b) (i : Fin a) :
      (cast (congrArg Fin h) i).val = i.val := by cases h; rfl
  simp only [shuffleIndex, GS.scalarShuffle, Equiv.trans_apply, Equiv.prodComm_apply,
    Equiv.symm_apply_apply, Prod.swap_swap, Equiv.cast_apply]
  exact (congrArg (· / k) (val_cast (Nat.mul_comm b k) (finProdFinEquiv x))).trans (standard_block_label x)

theorem blockView_shuffle (D : Fin b → M 𝕜 k) (i j : Fin k) :
    let P := permMatrix (𝕜 := 𝕜) (GS.scalarShuffle k b)
    blockView finProdFinEquiv (Pᴴ * packBlocks (shuffleIndex k b) D * P) i j =
      diagonal (fun a => D a i j) := by
  ext a c
  simp only [blockView_apply, perm_conjTranspose, mul_perm_apply, perm_mul_apply, Equiv.symm_symm]
  change packBlocks (shuffleIndex k b) D (shuffleIndex k b (a,i)) (shuffleIndex k b (c,j)) = _
  by_cases h : a = c <;> simp [h]

private def rotation (c s : ℝ) : M 𝕜 2 := !![(c : 𝕜),-(s : 𝕜); (s : 𝕜), (c : 𝕜)]

private theorem rotation_unitary {c s : ℝ} (h : c^2+s^2=1) : Unitary (rotation (𝕜 := 𝕜) c s) := by
  apply Unitary.of_conjTranspose_mul
  have hh := congrArg (fun t : ℝ => (t : 𝕜)) h
  simp only [RCLike.ofReal_add, RCLike.ofReal_pow, RCLike.ofReal_one] at hh
  ext i j
  fin_cases i, j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, ← pow_two, hh, add_comm (↑s ^ 2 : 𝕜) (↑c ^ 2), mul_comm]

/-- Match the first block column, then use triangular unitarity to fix the other column. -/
theorem cs_exhaustion {A : M 𝕜 (2*p)} :
    InA3Unitary p 2 p (permMatrix (𝕜 := 𝕜) (GS.scalarShuffle 2 p))
      (permMatrix (𝕜 := 𝕜) (GS.scalarShuffle 2 p))ᴴ A ↔ Unitary A := by
  let P := permMatrix (𝕜 := 𝕜) (GS.scalarShuffle 2 p)
  have hP : Unitary P := perm_unitary _
  refine ⟨fun h => (inA3Unitary_implies_inA3_and_unitary hP hP.conjTranspose h).2, ?_⟩
  intro hA
  let e : Fin 2 × Fin p ≃ Fin (2*p) := finProdFinEquiv
  let v := blockView (𝕜 := 𝕜) e
  have hgram := congrArg (fun X : M 𝕜 (2*p) => v X 0 0) hA.1
  simp only [v, map_mul, map_one, blockView_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hgram
  obtain ⟨U,V,W,c,s,hU,hV,hW,hcs,hu,hv⟩ := exists_thin_cs (v A 0 0) (v A 1 0) hgram
  let C := packBlocks (shuffleIndex 2 p) (fun i => rotation (𝕜 := 𝕜) (c i) (s i))
  let K := Pᴴ * C * P
  let B := packBlocks e ![U,V]
  let T := packBlocks e ![W,(1 : M 𝕜 p)]
  let L := B * K
  let R := Lᴴ * (A*T)
  have hC : Unitary C := (packBlocks_unitary_iff ..).mpr (fun i => rotation_unitary (hcs i))
  have hB : Unitary B := (packBlocks_unitary_iff ..).mpr (by intro i; fin_cases i <;> assumption)
  have hT : Unitary T := (packBlocks_unitary_iff ..).mpr (by intro i; fin_cases i; exact hW; exact Unitary.one)
  have hL : Unitary L := hB.mul ((hP.conjTranspose.mul hC).mul hP)
  have hR : Unitary R := hL.conjTranspose.mul (hA.mul hT)
  have hK (i : Fin 2) : v K i 0 = diagonal (fun j => rotation (𝕜 := 𝕜) (c j) (s j) i 0) :=
    blockView_shuffle _ _ _
  have hcol (i : Fin 2) : v (A*T) i 0 = v L i 0 := by
    change v (A * packBlocks e _) i 0 = v (packBlocks e _ * K) i 0
    have hd (D : Fin 2 → M 𝕜 p) : v (packBlocks e D) = diagonal D := blockView_pack ..
    simp only [map_mul, hd, Matrix.mul_diagonal, Matrix.diagonal_mul, hK]
    fin_cases i
    · simpa [rotation] using hu
    · simpa [rotation] using hv
  have hfix (i : Fin 2) : v R i 0 = (1 : Matrix (Fin 2) (Fin 2) (M 𝕜 p)) i 0 := by
    have hh : v R i 0 = v (Lᴴ * L) i 0 := by
      simp only [R, map_mul v Lᴴ (A*T), map_mul v Lᴴ L, Matrix.mul_apply, hcol]
    rw [hh, hL.1, map_one]
  have hsR : BlockDiagonal p R := unitary_blockTriangular_supported hR <| by
    intro i j h
    obtain ⟨⟨i,a⟩,rfl⟩ := e.surjective i
    obtain ⟨⟨j,b⟩,rfl⟩ := e.surjective j
    change (e (j,b)).val / p < (e (i,a)).val / p at h
    rw [show e = finProdFinEquiv from rfl, standard_block_label, standard_block_label] at h
    change v R i j a b = 0
    fin_cases i, j <;> simp_all
  refine ⟨R*Tᴴ,C,B,CSupported.mul hsR (packBlocks_supported e standard_block_label _).conjTranspose,
    packBlocks_supported _ shuffleIndex_label _, packBlocks_supported e standard_block_label _,
    hR.mul hT.conjTranspose,hC,hB,?_⟩
  have h : A = L * R * Tᴴ := by
    simp only [R, ← Matrix.mul_assoc, hL.2, Matrix.one_mul, Matrix.mul_assoc A T Tᴴ, hT.2, Matrix.mul_one]
  simpa only [L,K,P,product3,Matrix.mul_assoc] using h

end GS.Shared
