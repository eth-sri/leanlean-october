/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.CubeSlicing
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

public section

open Finset MeasureTheory Module Submodule Matrix
open scoped ENNReal Pointwise

/-- Cauchy–Binet identity: the determinant of `A * B` is the sum of products of maximal minors. -/
theorem Matrix.det_mul_eq_sum_det_submatrix {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
    (A * B).det = ∑ s : Fin m ↪o ι, (A.submatrix id s).det * (B.submatrix s id).det := by
  let b := Pi.basisFun R ι
  let x := exteriorPower.ιMulti R m A.row
  let y := exteriorPower.ιMulti R m Bᵀ.row
  have hpair : exteriorPower.pairingDual R (ι → R) m (exteriorPower.map m b.toDual x) y =
      ∑ s : Set.powersetCard ι m,
        (b.exteriorPower m).repr x s * (b.exteriorPower m).repr y s := by
    conv_lhs => rw [← (b.exteriorPower m).sum_repr x]
    rw [map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
      show b.toDual ∘ b = b.coord from funext b.coe_toDual_self, exteriorPower.basis_repr_apply]
    rfl
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti] at hpair
  have hlhs : (Matrix.of fun i j => (b.toDual ∘ A.row) j (Bᵀ.row i)).det = (A * B).det := by
    have hdot (u v : ι → R) : b.toDual u v = u ⬝ᵥ v := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      simp only [map_smul, b, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp only [Function.comp_apply, hdot]
    rw [← Matrix.det_transpose (Matrix.of fun i j => A.row j ⬝ᵥ Bᵀ.row i)]; rfl
  rw [← hlhs, hpair, ← Equiv.sum_comp Set.powersetCard.ofFinEmbEquiv]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [x, y, b, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply, Basis.coord_apply, Pi.basisFun_repr]
  congr 1
  rw [← Matrix.det_transpose (B.submatrix s id), Matrix.transpose_submatrix]; rfl

namespace Int.Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- Greatest common divisor of the `m × m` minors of an `m × ι` integer matrix. -/
@[expose] noncomputable def minorGcd (A : _root_.Matrix (Fin m) ι ℤ) : ℤ :=
  (Finset.univ : Finset (Fin m ↪o ι)).gcd fun s => (A.submatrix id s).det

private theorem det_gram_eq (A : _root_.Matrix (Fin m) ι ℤ) :
    (A * Aᵀ).det = ∑ s : Fin m ↪o ι, (A.submatrix id s).det ^ 2 := by
  rw [_root_.Matrix.det_mul_eq_sum_det_submatrix]
  exact Finset.sum_congr rfl fun s _ => by rw [sq, ← _root_.Matrix.det_transpose (Aᵀ.submatrix s id)]; rfl

private theorem det_pos {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 0 < (A * Aᵀ).det := by
  refine lt_of_le_of_ne (det_gram_eq A ▸ Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h0 => ?_
  set Aq := A.map ((↑) : ℤ → ℚ)
  have hdet0 : (Aq * Aqᵀ).det = 0 := by
    rw [show Aq * Aqᵀ = (Int.castRingHom ℚ).mapMatrix (A * Aᵀ) by ext; simp [Aq, _root_.Matrix.mul_apply],
      ← RingHom.map_det, ← h0, map_zero]
  obtain ⟨c, hc0, hc⟩ := _root_.Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  set w := Aqᵀ *ᵥ c
  have hw2 : w ⬝ᵥ w = 0 := by
    have h2 : c ⬝ᵥ (Aq *ᵥ w) = 0 := by rw [_root_.Matrix.mulVec_mulVec, hc, dotProduct_zero]
    rwa [_root_.Matrix.dotProduct_mulVec, show c ᵥ* Aq = w from funext fun _ => dotProduct_comm _ _] at h2
  have hw0 (j : ι) : w j = 0 := sq_eq_zero_iff.mp <|
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp (by simpa [dotProduct, sq] using hw2) j (mem_univ j)
  refine hc0 (funext fun i => Fintype.linearIndependent_iff.mp hA c ?_ i)
  ext j; simpa [w, _root_.Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using hw0 j

theorem one_le_minorGcd {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 1 ≤ minorGcd A := by
  have hpos := det_gram_eq A ▸ det_pos hA
  have hne : minorGcd A ≠ 0 := fun h => by
    simp [fun s => Finset.gcd_eq_zero_iff.mp h s (mem_univ s)] at hpos
  have hnn : 0 ≤ minorGcd A := by
    rw [minorGcd, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]; exact abs_nonneg _
  omega

/-- Bombieri–Vaaler's Theorem 1: for an `m × ι` integer matrix with linearly independent rows
and `m < Fintype.card ι`, there is a nonzero integral solution `A *ᵥ x = 0` with sup norm at most
`(√det(A Aᵀ) / minorGcd A) ^ (1 / (card ι - m))`. -/
theorem exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hmn : m < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ((⨆ i, |x i| : ℤ) : ℝ) ≤
        (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ)) ^
          (((Fintype.card ι : ℝ) - m)⁻¹) := by
  classical
  set K := LinearMap.ker A.mulVecLin
  obtain ⟨r, snf⟩ := K.smithNormalForm (Pi.basisFun ℤ ι)
  have hbK (l : Fin r) : A *ᵥ snf.bM (snf.f l) = 0 := by
    have ha : snf.a l ≠ 0 := fun h => Subtype.coe_injective.ne (snf.bN.ne_zero l) (by simp [snf.snf, h])
    have hmul : A.mulVecLin (snf.a l • snf.bM (snf.f l)) = 0 :=
      snf.snf l ▸ LinearMap.mem_ker.mp (snf.bN l).2
    exact smul_eq_zero.mp (map_smul A.mulVecLin _ _ ▸ hmul) |>.resolve_left ha
  let U : _root_.Matrix ι ι ℤ := _root_.Matrix.of snf.bM
  let Uinv : _root_.Matrix ι ι ℤ := fun j k => snf.bM.repr (Pi.single j 1) k
  have hUinvU : Uinv * U = 1 := by
    ext j l; rw [_root_.Matrix.mul_apply]
    simpa [U, Uinv, Finset.sum_apply, smul_eq_mul, _root_.Matrix.one_apply,
      Pi.single_apply, eq_comm] using congrFun (snf.bM.sum_repr (Pi.single j 1)) l
  have hUUinv : U * Uinv = 1 := by
    ext u v; rw [_root_.Matrix.mul_apply]
    have hlin : ∑ j, U u j * Uinv j v = snf.bM.repr (∑ j, U u j • Pi.single j (1 : ℤ)) v := by
      rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun _ _ => by
        rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hlin, show (∑ j, U u j • Pi.single j (1 : ℤ)) = snf.bM u by
      ext j; simp [U, Finset.sum_apply, Pi.single_apply], snf.bM.repr_self]
    by_cases h : u = v <;> simp [h, _root_.Matrix.one_apply]
  have hU_li (R : Type) [Field R] : LinearIndependent R (fun j : ι => ((↑) : ℤ → R) ∘ snf.bM j) := by
    rw [Fintype.linearIndependent_iff]; intro c hc j
    have hvec : c ᵥ* U.map ((↑) : ℤ → R) = 0 := by
      ext k; simpa [U, _root_.Matrix.vecMul, dotProduct, Finset.sum_apply] using congrFun hc k
    have h1 : U.map ((↑) : ℤ → R) * Uinv.map ((↑) : ℤ → R) = 1 := by
      change (Int.castRingHom R).mapMatrix U * (Int.castRingHom R).mapMatrix Uinv = 1
      rw [← map_mul, hUUinv, map_one]
    have hmul := congrFun (congrArg (· ᵥ* Uinv.map ((↑) : ℤ → R)) hvec) j
    simpa [_root_.Matrix.vecMul_vecMul, h1] using hmul
  set Aq := A.map ((↑) : ℤ → ℚ)
  have hker_eq : LinearMap.ker Aq.mulVecLin =
      Submodule.span ℚ (Set.range fun l : Fin r => ((↑) : ℤ → ℚ) ∘ snf.bM (snf.f l)) := by
    refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
    · let d : ℤ := ∏ i : ι, ((v i).den : ℤ)
      have hd0 : (d : ℚ) ≠ 0 := by
        dsimp only [d]
        exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ =>
          Int.natCast_ne_zero.mpr (v i).pos.ne' : (∏ i : ι, ((v i).den : ℤ)) ≠ 0)
      let z : ι → ℤ := fun i => (v i).num * ∏ k ∈ univ.erase i, ((v k).den : ℤ)
      have hz (i : ι) : (d : ℚ) * v i = z i := by
        dsimp only [d, z]; push_cast
        rw [← Finset.mul_prod_erase univ (fun k => ((v k).den : ℚ)) (mem_univ i),
          mul_right_comm, mul_comm (((v i).den : ℚ)) (v i), Rat.mul_den_eq_num]
      have hzK : z ∈ K := by
        rw [LinearMap.mem_ker]; ext i
        have hcast : ((A *ᵥ z) i : ℚ) = (Aq *ᵥ (((↑) : ℤ → ℚ) ∘ z)) i := by
          simp [Aq, _root_.Matrix.mulVec, dotProduct]
        have heq : (((↑) : ℤ → ℚ) ∘ z) = (d : ℚ) • v := funext fun j => (hz j).symm
        have hi : (Aq *ᵥ (((↑) : ℤ → ℚ) ∘ z)) i = 0 := by
          rw [heq, ← Aq.mulVecLin_apply, map_smul, LinearMap.mem_ker.mp hv, smul_zero, Pi.zero_apply]
        exact_mod_cast hcast.trans hi
      have hz_sum : z = ∑ l : Fin r, snf.bM.repr z (snf.f l) • snf.bM (snf.f l) := by
        conv_lhs => rw [← snf.bM.sum_repr z]
        rw [← Finset.sum_filter_of_ne (p := fun j => j ∈ Set.range snf.f) fun j _ hj => by
          by_contra hnr
          exact hj (snf.repr_eq_zero_of_notMem_range ⟨z, hzK⟩ hnr ▸ zero_smul ℤ _)]
        rw [show (univ.filter fun j => j ∈ Set.range snf.f) = univ.image snf.f by ext; simp,
          Finset.sum_image fun _ _ _ _ h => snf.f.injective h]
      rw [show v = ∑ l : Fin r, ((d : ℚ)⁻¹ * (snf.bM.repr z (snf.f l) : ℚ)) •
          (((↑) : ℤ → ℚ) ∘ snf.bM (snf.f l)) by
        ext j
        have hzj := congrArg ((↑) : ℤ → ℚ) (congrFun hz_sum j)
        simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
          Int.cast_sum, Int.cast_mul, mul_assoc] at hzj ⊢
        rw [← Finset.mul_sum, ← hzj, ← hz j, inv_mul_cancel_left₀ hd0]]
      exact sum_mem fun l _ => smul_mem _ _ (subset_span ⟨l, rfl⟩)
    · rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply]
      ext i
      simpa [Aq, _root_.Matrix.mulVec, dotProduct] using congrArg ((↑) : ℤ → ℚ) (congrFun (hbK l) i)
  have hmr : m + r = Fintype.card ι := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Aq.mulVecLin
    have h2 : finrank ℚ (LinearMap.range Aq.mulVecLin) = m := by
      change Aq.rank = m; simpa using hA.rank_matrix
    have h3 : finrank ℚ (LinearMap.ker Aq.mulVecLin) = r := by
      rw [hker_eq]
      change finrank ℚ (span ℚ (Set.range ((fun j => ((↑) : ℤ → ℚ) ∘ snf.bM j) ∘ snf.f))) = r
      rw [finrank_span_eq_card ((hU_li ℚ).comp snf.f snf.f.injective), Fintype.card_fin]
    simpa [h2, h3] using h1
  have hrpos : 0 < r := by omega
  set Sc : Finset ι := (univ.map snf.f)ᶜ
  have hScard : Fintype.card Sc = m := by
    rw [Fintype.card_coe, Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin]; omega
  let g : Fin m ↪ ι := (Fintype.equivFinOfCardEq hScard).symm.toEmbedding.trans (.subtype _)
  have hdisj (i : Fin m) (l : Fin r) : g i ≠ snf.f l := fun h => by
    have hmem : g i ∈ Sc := ((Fintype.equivFinOfCardEq hScard).symm i).2
    exact (Finset.mem_compl.mp hmem) (h ▸ Finset.mem_map_of_mem snf.f (mem_univ l))
  let e : Fin m ⊕ Fin r ≃ ι := Equiv.ofBijective (Sum.elim g snf.f)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      rintro (i₁ | l₁) (i₂ | l₂) h
      · exact congrArg Sum.inl (g.injective h)
      · exact (hdisj i₁ l₂ h).elim
      · exact (hdisj i₂ l₁ h.symm).elim
      · exact congrArg Sum.inr (snf.f.injective h), by simp [hmr]⟩)
  let C : _root_.Matrix (Fin m) ι ℤ := U.submatrix g id
  let B : _root_.Matrix (Fin r) ι ℤ := U.submatrix snf.f id
  let M : _root_.Matrix (Fin m ⊕ Fin r) ι ℤ := U.submatrix e id
  let P : _root_.Matrix ι (Fin m ⊕ Fin r) ℤ := Uinv.submatrix id e
  have hPM : P * M = 1 := by
    ext j l
    simp only [P, M, _root_.Matrix.mul_apply, _root_.Matrix.submatrix_apply, id_eq]
    rw [Equiv.sum_comp e fun w => Uinv j w * U w l]
    exact congrArg (fun X => X j l) hUinvU
  have hABt : A * Bᵀ = 0 := funext fun i => funext fun l => congrFun (hbK l) i
  have hA_fac : A = (A * Cᵀ) * Pᵀ.submatrix Sum.inl id := by
    calc A = (A * Mᵀ) * Pᵀ := by
          rw [_root_.Matrix.mul_assoc, ← _root_.Matrix.transpose_mul, hPM,
            _root_.Matrix.transpose_one, _root_.Matrix.mul_one]
      _ = (A * Cᵀ) * Pᵀ.submatrix Sum.inl id := by
          ext i j
          rw [_root_.Matrix.mul_apply, Fintype.sum_sum_type, _root_.Matrix.mul_apply]
          have hz : ∑ l : Fin r, (A * Mᵀ) i (Sum.inr l) * Pᵀ (Sum.inr l) j = 0 :=
            Finset.sum_eq_zero fun l _ => by
              have : (A * Mᵀ) i (Sum.inr l) = (A * Bᵀ) i l := rfl
              rw [this, hABt, _root_.Matrix.zero_apply, zero_mul]
          rw [hz, add_zero]; rfl
  have hgcd_sq : minorGcd A ^ 2 = (A * Cᵀ).det ^ 2 := by
    have hd1 : minorGcd A ∣ (A * Cᵀ).det := by
      rw [_root_.Matrix.det_mul_eq_sum_det_submatrix]
      exact Finset.dvd_sum fun s _ => dvd_mul_of_dvd_left (Finset.gcd_dvd (mem_univ s))
    have hd2 : (A * Cᵀ).det ∣ minorGcd A := Finset.dvd_gcd fun s _ => by
      have hs : A.submatrix id s = (A * Cᵀ) * Pᵀ.submatrix Sum.inl s := by
        conv_lhs => rw [hA_fac]
        rfl
      rw [hs, _root_.Matrix.det_mul]; exact dvd_mul_right _ _
    obtain ⟨u, hu⟩ := associated_of_dvd_dvd hd1 hd2
    rcases Int.isUnit_iff.mp u.isUnit with h | h <;> simp [← hu, h]
  let W : _root_.Matrix (Fin m ⊕ Fin r) ι ℤ := _root_.Matrix.of (Sum.elim A.row B.row)
  let M₀ := M.submatrix id e
  let P₀ := P.submatrix e id
  let W₀ := W.submatrix id e
  have hM₀_sq : M₀.det ^ 2 = 1 := by
    have h1 : P₀.det * M₀.det = 1 := by
      rw [← _root_.Matrix.det_mul, show P₀ * M₀ = 1 by
        ext u v; refine (congrArg (fun X => X (e u) (e v)) hPM).trans ?_
        by_cases huv : u = v <;> simp [huv, _root_.Matrix.one_apply, e.injective.eq_iff],
        _root_.Matrix.det_one]
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨P₀.det, h1.symm.trans (mul_comm _ _)⟩) with h | h <;>
      simp [h]
  have hWWt : (W₀ * W₀ᵀ).det = (A * Aᵀ).det * (B * Bᵀ).det := by
    have h1 : W₀ * W₀ᵀ = W * Wᵀ := by ext u v; exact Equiv.sum_comp e fun j => W u j * W v j
    have h2 : W * Wᵀ = _root_.Matrix.fromBlocks (A * Aᵀ) (A * Bᵀ) (B * Aᵀ) (B * Bᵀ) := by
      ext (_ | _) (_ | _) <;> rfl
    have hBAt : B * Aᵀ = 0 := by
      rw [← _root_.Matrix.transpose_transpose B, ← _root_.Matrix.transpose_mul, hABt,
        _root_.Matrix.transpose_zero]
    rw [h1, h2, hABt, hBAt, _root_.Matrix.det_fromBlocks_zero₁₂]
  have hWMt : (W₀ * M₀ᵀ).det = (A * Cᵀ).det * (B * Bᵀ).det := by
    have h1 : W₀ * M₀ᵀ = W * Mᵀ := by ext u v; exact Equiv.sum_comp e fun j => W u j * M v j
    have h2 : W * Mᵀ = _root_.Matrix.fromBlocks (A * Cᵀ) (A * Bᵀ) (B * Cᵀ) (B * Bᵀ) := by
      ext (_ | _) (_ | _) <;> rfl
    rw [h1, h2, hABt, _root_.Matrix.det_fromBlocks_zero₁₂]
  have hBBpos : 0 < (B * Bᵀ).det := det_pos ((hU_li ℚ).comp snf.f snf.f.injective)
  have hdet_id : (A * Aᵀ).det = minorGcd A ^ 2 * (B * Bᵀ).det := by
    refine mul_right_cancel₀ hBBpos.ne' ?_
    rw [← hWWt, _root_.Matrix.det_mul, _root_.Matrix.det_transpose, ← sq,
      show W₀.det ^ 2 = (W₀ * M₀ᵀ).det ^ 2 by
        rw [_root_.Matrix.det_mul, _root_.Matrix.det_transpose, mul_pow, hM₀_sq, mul_one],
      hWMt, hgcd_sq, mul_pow, sq ((B * Bᵀ).det), mul_assoc]
  let b : Fin r → EuclideanSpace ℝ ι := fun l => WithLp.toLp 2 (((↑) : ℤ → ℝ) ∘ B l)
  have hb_li : LinearIndependent ℝ b :=
    ((hU_li ℝ).comp snf.f snf.f.injective).map'
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
  set V : Submodule ℝ (EuclideanSpace ℝ ι) := Submodule.span ℝ (Set.range b)
  let β : Basis (Fin r) ℝ V := Basis.span hb_li
  have hdim : finrank ℝ V = r := by rw [finrank_eq_card_basis β, Fintype.card_fin]
  let o : OrthonormalBasis (Fin r) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq (by simp [hdim]))
  have hgram : (o.toBasis.toMatrix β)ᵀ * o.toBasis.toMatrix β = (B * Bᵀ).map ((↑) : ℤ → ℝ) := by
    ext l₁ l₂
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.transpose_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, _root_.Matrix.map_apply]
    have hin : ∑ k : Fin r, inner ℝ (o k) (β l₁) * inner ℝ (o k) (β l₂) =
        inner ℝ (β l₁ : EuclideanSpace ℝ ι) (β l₂ : EuclideanSpace ℝ ι) :=
      (Finset.sum_congr rfl fun k _ => by rw [real_inner_comm (o k) (β l₁)]).trans
        (o.sum_inner_mul_inner (β l₁) (β l₂))
    rw [hin, Basis.span_apply, Basis.span_apply, PiLp.inner_apply]
    push_cast; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  set Cval : ℝ := Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ)
  have hCpos : 0 < Cval := div_pos (Real.sqrt_pos.mpr (mod_cast det_pos hA))
    (mod_cast one_le_minorGcd hA)
  have hfund : volume (ZSpan.fundamentalDomain β) = ENNReal.ofReal Cval := by
    have ho1 : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
      simp [o.volume_parallelepiped]
    rw [ZSpan.measure_fundamentalDomain β volume o.toBasis, ho1, mul_one, Basis.det_apply]
    congr 1
    refine (sq_eq_sq₀ (abs_nonneg _) hCpos.le).mp ?_
    have hsq : |(o.toBasis.toMatrix β).det| ^ 2 = (((B * Bᵀ).det : ℤ) : ℝ) := by
      rw [sq_abs, sq]
      conv_lhs => arg 1; rw [← _root_.Matrix.det_transpose]
      rw [← _root_.Matrix.det_mul, hgram]
      change _ = (Int.castRingHom ℝ) (B * Bᵀ).det
      rw [RingHom.map_det]; rfl
    have hD1 : (1 : ℝ) ≤ ((minorGcd A : ℤ) : ℝ) := mod_cast one_le_minorGcd hA
    rw [hsq, div_pow, Real.sq_sqrt (mod_cast (det_pos hA).le), hdet_id]; push_cast; field_simp
  set X : ℝ := Cval ^ ((r : ℝ)⁻¹)
  have hXpos : 0 < X := Real.rpow_pos_of_pos hCpos _
  set t : ℝ := (X + ((⌊X⌋ : ℝ) + 1)) / 2
  have hXt : X < t := by dsimp only [t]; linarith [Int.lt_floor_add_one X]
  have htfl : t < (⌊X⌋ : ℝ) + 1 := by dsimp only [t]; linarith [Int.lt_floor_add_one X]
  have htpos : 0 < t := hXpos.trans hXt
  set Kset : Set V := {y : V | ∀ j, |(y : EuclideanSpace ℝ ι) j| ≤ 1}
  have hKconv : Convex ℝ Kset := fun x hx y hy a₁ a₂ ha₁ ha₂ ha j => by
    have h : ((a₁ • x + a₂ • y : V) : EuclideanSpace ℝ ι) j =
        a₁ * (x : EuclideanSpace ℝ ι) j + a₂ * (y : EuclideanSpace ℝ ι) j := by simp
    rw [h]
    exact (abs_add_le _ _).trans <| by
      rw [abs_mul, abs_mul, abs_of_nonneg ha₁, abs_of_nonneg ha₂]
      exact (add_le_add (mul_le_mul_of_nonneg_left (hx j) ha₁)
        (mul_le_mul_of_nonneg_left (hy j) ha₂)).trans_eq (by linarith)
  have hKsymm : ∀ y ∈ t • Kset, -y ∈ t • Kset := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨-y, fun j => ?_, smul_neg t y⟩
    have h : ((-y : V) : EuclideanSpace ℝ ι) j = -((y : V) : EuclideanSpace ℝ ι) j := by simp
    rw [h, abs_neg]; exact hy j
  have hvol_lt : volume (ZSpan.fundamentalDomain β) * 2 ^ finrank ℝ V < volume (t • Kset) := by
    have hpow : Cval < t ^ r :=
      Real.rpow_inv_natCast_pow hCpos.le hrpos.ne' ▸ pow_lt_pow_left₀ hXt hXpos.le hrpos.ne'
    have hcube := hdim ▸ two_pow_finrank_le_volume_inter_cube V
    rw [Measure.addHaar_smul, hdim, abs_of_pos (pow_pos htpos r), hfund]
    calc ENNReal.ofReal Cval * 2 ^ r < ENNReal.ofReal (t ^ r) * 2 ^ r := by
          rw [mul_comm, mul_comm _ (2 ^ r)]
          exact ENNReal.mul_lt_mul_right (pow_ne_zero r two_ne_zero) (by finiteness)
            ((ENNReal.ofReal_lt_ofReal_iff (pow_pos htpos r)).mpr hpow)
      _ ≤ ENNReal.ofReal (t ^ r) * volume Kset := by gcongr
  have : Countable (span ℤ (Set.range ⇑β)).toAddSubgroup :=
    Function.Surjective.countable (f := fun c : Fin r → ℤ =>
      (⟨∑ l, c l • β l, sum_mem fun l _ => zsmul_mem (subset_span (Set.mem_range_self l)) _⟩ :
        (span ℤ (Set.range ⇑β)).toAddSubgroup)) fun ⟨y, hy⟩ => by
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
      exact ⟨c, Subtype.ext (by simpa [Finsupp.sum_fintype] using hc)⟩
  obtain ⟨y, hy0, y', hy'K, hy'eq⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' β volume) hKsymm (hKconv.smul t) hvol_lt
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp y.2
  set x : ι → ℤ := fun j => ∑ l : Fin r, c l * B l j
  have hy_coord (j : ι) : ((y : V) : EuclideanSpace ℝ ι) j = (x j : ℝ) := by
    rw [show (y : V) = ∑ l : Fin r, c l • β l by simpa [Finsupp.sum_fintype] using hc.symm]
    have hcoe : ((∑ l : Fin r, c l • β l : V) : EuclideanSpace ℝ ι) j =
        ∑ l : Fin r, (c l : ℝ) * (b l) j := by
      push_cast; simp only [WithLp.ofLp_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [congrArg Subtype.val (Basis.span_apply hb_li l)]; simp
    rw [hcoe]; simp [x, b]
  refine ⟨x, fun hx0 => hy0 <| by
    ext1; ext j; rw [hy_coord j, hx0, Pi.zero_apply, Int.cast_zero]; simp, ?_, ?_⟩
  · ext i
    simp only [_root_.Matrix.mulVec, dotProduct, x, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    simp_rw [← mul_assoc, mul_comm (A i _) (c l), mul_assoc, ← Finset.mul_sum]
    exact mul_eq_zero_of_right _
      (by simpa [_root_.Matrix.mulVec, dotProduct, B, U] using congrFun (hbK l) i)
  · have hxle (j : ι) : |x j| ≤ ⌊X⌋ := by
      have hj : |((y : V) : EuclideanSpace ℝ ι) j| ≤ t := by
        rw [← hy'eq, show ((t • y' : V) : EuclideanSpace ℝ ι) j = t * (y' : EuclideanSpace ℝ ι) j by simp,
          abs_mul, abs_of_pos htpos]
        exact (mul_le_mul_of_nonneg_left (hy'K j) htpos.le).trans_eq (mul_one t)
      have hjR : ((|x j| : ℤ) : ℝ) < (⌊X⌋ : ℝ) + 1 := by
        rw [Int.cast_abs, ← hy_coord j]; exact hj.trans_lt htfl
      have hjZ : |x j| < ⌊X⌋ + 1 := mod_cast hjR
      omega
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := fun j => |x j|)
    rw [← Nat.cast_sub hmn.le, show Fintype.card ι - m = r by omega, ← hj₀]
    exact (Int.cast_le.mpr (hxle j₀)).trans (Int.floor_le X)

end Int.Matrix

end
