import Mathlib.Tactic.Module

import GS.NonmanifoldCompletion.FactorSpace
import GS.NonmanifoldCompletion.OriginalCoordinates
import GS.Continuation.CompactCoverageTools
open GS.MatrixBase



/-!
# Coverage of an actual GS neighbourhood by the original compact parametrization

The proof normalizes EACH representative of the full compact fibre, using fixed
local diagonal gauges, local rotation angles, and genuine small logarithms.
It then applies compactness. No normalization or full-fibre coverage assumption
is exposed in the final theorem. The original scalarShuffle, localFamily,
originalF, and originalK definitions are retained.

This theorem supplies `OriginalLocalCoverageGoal` to the final nonmanifold
proof. 
-/
open Matrix GS.Extensions
namespace GS.NonmanifoldCompletion

/-- Every full-fibre representative has a parameter neighbourhood whose image
is contained in originalF(K_eta). Gauges are chosen locally, not globally. -/
theorem factor_neighbourhood_in_original_image {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0)
    (η : ℝ) (hη : 0<η) (p : SmallBlockParameters q) (hp : p∈smallFactorSet q)
    (he : smallFactorMap p=basePoint Q₀) :
    ∃ N : Set (SmallBlockParameters q), IsOpen N ∧ p∈N ∧
      ∀ p'∈N, p'∈smallFactorSet q → smallFactorMap p' ∈ originalF Q₀ '' originalK q η := by
  rcases p with ⟨U,A,B,V⟩
  rcases hp with ⟨hU,hA,hB,hV⟩
  have hbase (i j : Fin q) : U i * diagTwo (A i j) (B i j) * V j = Q₀ i j • (1 : Mat 2) := by
    ext a b
    have hh := congrFun (congrFun he (finProdFinEquiv (i,a))) (finProdFinEquiv (j,b))
    rw [smallFactorMap,flattenBlocks_apply,small_block_sandwich] at hh
    dsimp only [basePoint] at hh
    rw [Equiv.symm_apply_apply finProdFinEquiv (i,a),
      Equiv.symm_apply_apply finProdFinEquiv (j,b)] at hh
    exact hh
  let i₀ : Fin q := ⟨0,hq⟩
  let S := V i₀
  let D : Fin q → Mat 2 := fun i => S*U i
  let E : Fin q → Mat 2 := fun j => V j*Sᵀ
  have hS : Orthogonal S := hV i₀
  have hdiag (i j : Fin q) : DiagonalTwo (V j*U i) := by
    have hh := congrArg (fun Z : Mat 2 => (U i)ᵀ * Z * (V j)ᵀ) (hbase i j)
    simp only [← Matrix.mul_assoc, (hU i).1, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hh
    simp only [Matrix.mul_assoc, (hV j).2, Matrix.mul_one] at hh
    have hd : DiagonalTwo (Q₀ i j • ((U i)ᵀ*(V j)ᵀ)) := by
      rw [← hh]
      simp [DiagonalTwo,diagTwo]
    simp [DiagonalTwo, Matrix.smul_apply, smul_eq_mul, hentries i j] at hd
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      diagonalTwo_transpose hd
  have hD (i : Fin q) : DiagonalTwo (D i) ∧ Orthogonal (D i) := ⟨hdiag i i₀,hS.mul (hU i)⟩
  have hE (j : Fin q) : DiagonalTwo (E j) ∧ Orthogonal (E j) := by
    refine ⟨?_,(hV j).mul hS.transpose⟩
    have he : E j = (V j*U i₀)*(S*U i₀)ᵀ := by
      simp only [E, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U i₀), (hU i₀).2, Matrix.one_mul]
    rw [he]
    exact diagonalTwo_mul (hdiag i₀ j) (diagonalTwo_transpose (hdiag i₀ i₀))
  have hleft (i : Fin q) : U i*D i*S=1 := by
    rw [← diagonalTwo_symmetric (D i) (hD i).1]
    dsimp [D]
    simp only [Matrix.transpose_mul, ← Matrix.mul_assoc, (hU i).2, Matrix.one_mul, hS.1]
  have hright (j : Fin q) : Sᵀ*E j*V j=1 := by
    rw [← diagonalTwo_symmetric (E j) (hE j).1]
    dsimp [E]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      hS.1, Matrix.one_mul, (hV j).1]
  have hmiddle (i j : Fin q) :
      diagTwo (gaugeMiddle D E 0 A i j) (gaugeMiddle D E 1 B i j) =
        Q₀ i j • (1 : Mat 2) := by
    rw [gaugeMiddle_apply,gaugeMiddle_apply,← diagonal_gauge_middle (D i) (E j) (hD i).1 (hE j).1]
    change (S*U i)*diagTwo (A i j) (B i j)*(V j*Sᵀ) = _
    calc
      _ = S*(U i*diagTwo (A i j) (B i j)*V j)*Sᵀ := by grind
      _ = S*(Q₀ i j • (1 : Mat 2))*Sᵀ := by grind
      _ = _ := by simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hS.2]
  have hAg : gaugeMiddle D E 0 A = Q₀ := by
    ext i j
    simpa [diagTwo] using congrFun (congrFun (hmiddle i j) 0) 0
  have hBg : gaugeMiddle D E 1 B = Q₀ := by
    ext i j
    simpa [diagTwo] using congrFun (congrFun (hmiddle i j) 1) 1
  obtain ⟨L,hL,hQL,hlog⟩ := exists_open_small_skew_log Q₀ hQ₀
    {H : Mat q | cFrobSq H < η^2} (isOpen_lt continuous_frobSq continuous_const)
    (by simp_all [cFrobInner,cFrobSq])
  let N : Set (SmallBlockParameters q) := {p' |
    (∀ i, p'.1 i*D i*S ∈ rotationChartDomain (η/4)) ∧
    (∀ j, Sᵀ*E j*p'.2.2.2 j ∈ rotationChartDomain (η/4)) ∧
    gaugeMiddle D E 0 p'.2.1 ∈ L ∧ gaugeMiddle D E 1 p'.2.2.1 ∈ L}
  have hN : IsOpen N := by
    simp only [N, Set.ofPred_and, Set.ofPred_forall]
    repeat' apply IsOpen.inter
    all_goals first
      | apply isOpen_iInter_of_finite
        intro i
        exact (isOpen_rotationChartDomain _).preimage (by fun_prop)
      | exact hL.preimage (by unfold gaugeMiddle; fun_prop)
  have hI : (1 : Mat 2) ∈ rotationChartDomain (η/4) := one_mem_rotationChartDomain (by positivity)
  have hpN : (U,A,B,V)∈N := by grind
  refine ⟨N,hN,hpN,?_⟩
  rintro ⟨U',A',B',V'⟩ ⟨hUl,hVr,hAL,hBL⟩ ⟨hU',hA',hB',hV'⟩
  let α : Fin q → ℝ := fun i => localRotationAngle (U' i*D i*S)
  let β : Fin q → ℝ := fun j => localRotationAngle (Sᵀ*E j*V' j)
  have hα (i : Fin q) :=
    rotation_localRotationAngle _ (((hU' i).mul (hD i).2).mul hS) (hUl i).1 (hUl i).2.1
  have hβ (j : Fin q) :=
    rotation_localRotationAngle _ ((hS.transpose.mul (hE j).2).mul (hV' j)) (hVr j).1 (hVr j).2.1
  obtain ⟨H,hHn,hH,hHA⟩ := hlog _ hAL (gaugeMiddle_orthogonal D E hD hE 0 A' hA')
  obtain ⟨K,hKn,hK,hKB⟩ := hlog _ hBL (gaugeMiddle_orthogonal D E hD hE 1 B' hB')
  let c := (1/2 : ℝ) • (H+K)
  let z := (1/2 : ℝ) • (H-K)
  change Hᵀ = -H at hH
  change Kᵀ = -K at hK
  have hk : IsSkew c ∧ IsSkew z := by
    constructor <;> simp [c,z,IsSkew,hH,hK,smul_sub] <;> abel
  have hsum : cFrobSq c+cFrobSq z = (cFrobSq H+cFrobSq K)/2 := by
    
    grind [cFrobInner_real_smul_left,cFrobInner_add_right,cFrobInner_sub_left,cFrobInner_comm]
  simp only [Set.mem_setOf_eq] at hHn hKn
  have hplus : c+z=H := by module
  have hminus : c-z=K := by module
  obtain ⟨u,hu,hconj⟩ := conjugate_reflection_coordinates (S*rotation (β i₀))
    (hS.mul (rotation_orthogonal (β i₀)))
  let ell : Fin q → ℝ := fun i => α i+β i₀
  let r : Fin q → ℝ := fun j => β j-β i₀
  have hell (i : Fin q) : |ell i| ≤ η := by
    
    linarith [(hUl i).2.2,(hVr i₀).2.2,abs_add_le (α i) (β i₀)]
  have hr (j : Fin q) : |r j| ≤ η := by
    
    linarith [(hVr j).2.2,(hVr i₀).2.2,abs_sub (β j) (β i₀)]
  refine ⟨(ell,r,c,z,u),⟨hell,hr,
    (by grind),hk.1,hk.2,
    (by linarith [cFrobSq_nonneg z]),(by linarith [cFrobSq_nonneg c]),hu⟩,?_⟩
  ext i j
  let x := finProdFinEquiv.symm i
  let y := finProdFinEquiv.symm j
  change (rotation (ell x.1)*middleBlock
    (originalPsi Q₀ (c+z) x.1 y.1) (originalPsi Q₀ (c-z) x.1 y.1) u*
    rotation (r y.1)) x.2 y.2 =
    (blockMatrix U'*centralPair A' B'*blockMatrix V') x y
  rw [small_block_sandwich,hplus,hminus,hHA,hKB]
  have htail : rotation (β i₀)*rotation (β y.1-β i₀)=rotation (β y.1) := by
    rw [← rotation_add]
    congr 1
    ring
  change _ = (U' x.1*diagTwo (A' x.1 y.1) (B' x.1 y.1)*V' y.1) x.2 y.2
  simp only [ell,r]
  rw [hconj,rotation_add,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc,
    ← Matrix.mul_assoc (rotation (β i₀)) (rotation (β i₀))ᵀ,
    (rotation_orthogonal (β i₀)).2, Matrix.one_mul, htail]
  rw [hα,hβ,gaugeMiddle_apply,gaugeMiddle_apply]
  have hDsq := diagonalTwo_involution (hD x.1).1 (hD x.1).2
  have hEsq := diagonalTwo_involution (hE y.1).1 (hE y.1).2
  rw [← diagonal_gauge_middle _ _ (hD x.1).1 (hE y.1).1]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S Sᵀ, hS.2, Matrix.one_mul,
    ← Matrix.mul_assoc (D x.1) (D x.1), hDsq]
  simp only [← Matrix.mul_assoc,hEsq,Matrix.mul_one]


end GS.NonmanifoldCompletion
