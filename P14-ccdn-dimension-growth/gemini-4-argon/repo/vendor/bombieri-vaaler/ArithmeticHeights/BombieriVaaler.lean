/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.Localization.Integer

public section

open Finset Module Submodule Matrix

namespace exteriorPower

private lemma ofFinEmbEquiv_symm_fin {k : ℕ} (s : Set.powersetCard (Fin k) k) :
    ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) := by
  have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm

section Plucker

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The **Plücker coordinates** of a family `v : Fin k → (ι → R)`. -/
@[expose] noncomputable def plucker (k : ℕ) (v : Fin k → (ι → R)) : Set.powersetCard ι k → R :=
  ((Pi.basisFun R ι).exteriorPower k).equivFun (ιMulti R k v)

theorem plucker_apply (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) :
    plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
  rw [plucker, Basis.equivFun_apply, basis_repr_apply, ιMultiDual_apply_ιMulti]
  simp

theorem plucker_fin_eq_det {n : ℕ} (v : Fin n → (Fin n → R)) (s : Set.powersetCard (Fin n) n) :
    plucker n v s = (Matrix.of v).det := by
  rw [plucker_apply, ofFinEmbEquiv_symm_fin]
  rfl

theorem plucker_eq_zero_iff {K : Type*} [Field K] (k : ℕ) (v : Fin k → (ι → K)) :
    plucker k v = 0 ↔ ¬ LinearIndependent K v := by
  rw [plucker, map_eq_zero_iff _ (LinearEquiv.injective _)]
  refine ⟨fun h hv ↦ ?_, AlternatingMap.map_linearDependent _ v⟩
  have h0 := (ιMulti_family_linearIndependent_field k hv).ne_zero
    (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
  rw [ιMulti_family, ofFinEmbEquiv_symm_fin, Function.comp_id] at h0
  exact h0 h

/-- **The Cauchy–Binet identity.** -/
theorem sum_plucker_mul_plucker (k : ℕ) (v w : Fin k → (ι → R)) :
    ∑ s : Set.powersetCard ι k, plucker k v s * plucker k w s
      = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det := by
  have hdual (x y : ι → R) : (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y := by
    conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
    rw [map_sum]
    simp only [map_smul, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hpair (x y : ⋀[R]^k (ι → R)) :
      pairingDual R (ι → R) k (map k (Pi.basisFun R ι).toDual x) y
        = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
            ((Pi.basisFun R ι).exteriorPower k).repr y s := by
    conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
    rw [map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [basis_apply, map_apply_ιMulti_family, show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) =
      (Pi.basisFun R ι).coord from funext fun i ↦ Basis.coe_toDual_self _ i, basis_repr_apply]
    rfl
  have h := hpair (ιMulti R k v) (ιMulti R k w)
  rw [map_apply_ιMulti, pairingDual_ιMulti_ιMulti] at h
  simp only [plucker, Basis.equivFun_apply, ← h, Function.comp_apply, hdual,
    ← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
  rfl

theorem plucker_map {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
    (s : Set.powersetCard ι k) : plucker k (fun i ↦ f ∘ v i) s = f (plucker k v s) := by
  rw [plucker_apply, plucker_apply, RingHom.map_det]
  rfl

end Plucker

end exteriorPower

open exteriorPower

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m k l : ℕ}

theorem plucker_row_eq_det_submatrix (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) :
    plucker m A.row s =
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [plucker_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

theorem det_mul_eq_sum_det_submatrix (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
    (A * B).det = ∑ s : Set.powersetCard ι m,
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det *
        (B.submatrix ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s)) id).det := by
  change (Matrix.of fun i j ↦ A.row i ⬝ᵥ Bᵀ.row j).det = _
  rw [← sum_plucker_mul_plucker m A.row Bᵀ.row]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [plucker_row_eq_det_submatrix, plucker_row_eq_det_submatrix,
    ← Matrix.det_transpose (B.submatrix _ id), Matrix.transpose_submatrix]

theorem det_mul_transpose_self_eq_sum_sq (A : Matrix (Fin m) ι R) :
    (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s ^ 2 := by
  change (Matrix.of fun i j ↦ A.row i ⬝ᵥ A.row j).det = _
  rw [← sum_plucker_mul_plucker m A.row A.row]
  exact Finset.sum_congr rfl fun s _ ↦ (sq _).symm

end Matrix

/-- Coordinatewise `ℤ → ℚ` on tuples, as a `ℤ`-linear map. -/
@[expose] def Rat.piIntCast (ι : Type*) : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun z i := (z i : ℚ)
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp

@[simp] theorem Rat.piIntCast_apply {ι : Type*} (z : ι → ℤ) (i : ι) :
    Rat.piIntCast ι z i = (z i : ℚ) := rfl

section IntPoints

variable {ι : Type*}

/-- The **integral points** `V ∩ ℤ^ι` of a rational subspace, as a `ℤ`-submodule of `ι → ℤ`. -/
@[expose] def Submodule.intPoints (V : Submodule ℚ (ι → ℚ)) : Submodule ℤ (ι → ℤ) :=
  Submodule.comap (Rat.piIntCast ι) (V.restrictScalars ℤ)

@[simp] theorem Submodule.mem_intPoints {V : Submodule ℚ (ι → ℚ)} {z : ι → ℤ} :
    z ∈ V.intPoints ↔ Rat.piIntCast ι z ∈ V := Iff.rfl

variable [Finite ι]

private theorem exists_intCast_smul (v : ι → ℚ) :
    ∃ (N : ℤ) (z : ι → ℤ), N ≠ 0 ∧ (N : ℚ) • v = Rat.piIntCast ι z := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
    (Finset.univ : Finset ι) v
  choose z hz using fun i ↦ hb i (Finset.mem_univ i)
  refine ⟨(b : ℤ), z, nonZeroDivisors.coe_ne_zero b, funext fun i ↦ ?_⟩
  simpa [Algebra.smul_def] using (hz i).symm

theorem Submodule.span_rat_of_span_intPoints (V : Submodule ℚ (ι → ℚ)) {κ : Type*}
    {y : κ → (ι → ℤ)} (hsat : Submodule.span ℤ (Set.range y) = V.intPoints) :
    Submodule.span ℚ (Set.range fun i ↦ Rat.piIntCast ι (y i)) = V := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact (hsat ▸ Submodule.subset_span ⟨i, rfl⟩ : y i ∈ V.intPoints)
  · obtain ⟨N, z, hN, hz⟩ := exists_intCast_smul v
    have hzΛ : z ∈ Submodule.span ℤ (Set.range y) := by
      rw [hsat, Submodule.mem_intPoints, ← hz]
      exact V.smul_mem _ hv
    have h2 := Submodule.mem_map_of_mem (f := Rat.piIntCast ι) hzΛ
    rw [Submodule.map_span, ← Set.range_comp] at h2
    have hNQ : (N : ℚ) ≠ 0 := Int.cast_ne_zero.2 hN
    rw [show v = (N : ℚ)⁻¹ • Rat.piIntCast ι z by
      rw [← hz, smul_smul, inv_mul_cancel₀ hNQ, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars ℤ ℚ _ h2)

end IntPoints

section Primitive

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (V : Submodule ℚ (ι → ℚ))

theorem Submodule.gcd_plucker_eq_one {k : ℕ} {y : Fin k → (ι → ℤ)}
    (hy : LinearIndependent ℚ (fun i ↦ Rat.piIntCast ι (y i)))
    (hsat : Submodule.span ℤ (Set.range y) = V.intPoints) :
    (Finset.univ : Finset (Set.powersetCard ι k)).gcd (plucker k y) = 1 := by
  classical
  have hyZ : LinearIndependent ℤ y :=
    LinearIndependent.of_comp (Rat.piIntCast ι)
      (hy.restrict_scalars (by simpa using Int.cast_injective (α := ℚ)))
  rw [← Finset.normalize_gcd]
  refine normalize_eq_one.2 (Int.isUnit_iff_natAbs_eq.2 ?_)
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Int.exists_prime_and_dvd hne
  have hdvd : ∀ s, q ∣ plucker k y s := fun s ↦ hqd.trans (Finset.gcd_dvd (Finset.mem_univ s))
  set P := q.natAbs
  have hPp : P.Prime := Int.prime_iff_natAbs_prime.1 hq
  have : Fact P.Prime := ⟨hPp⟩
  have hzero : plucker k (fun i ↦ (Int.castRingHom (ZMod P)) ∘ y i) = 0 := by
    funext s; rw [plucker_map]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).2
      ((Int.natAbs_dvd.2 dvd_rfl).trans (hdvd s))
  obtain ⟨c, hcsum, i₀, hi₀⟩ :=
    Fintype.not_linearIndependent_iff.1 ((plucker_eq_zero_iff (K := ZMod P) k _).1 hzero)
  choose c' hc' using fun i ↦ ZMod.intCast_surjective (n := P) (c i)
  let w : ι → ℤ := ∑ i, c' i • y i
  have hwdvd (l : ι) : (P : ℤ) ∣ w l := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hl := congrFun hcsum l
    simp only [w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Function.comp_apply, eq_intCast, Int.cast_sum, Int.cast_mul, hc'] at hl ⊢
    exact hl
  choose z hz using hwdvd
  have hwz : w = (P : ℤ) • z := funext fun l ↦ by simp [hz l]
  have hwV : Rat.piIntCast ι w ∈ V :=
    Submodule.mem_intPoints.1 (hsat ▸ Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ (c' i) (Submodule.subset_span ⟨i, rfl⟩))
  have hPQ : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hPp.ne_zero
  have hzV : z ∈ Submodule.span ℤ (Set.range y) := by
    rw [hsat, Submodule.mem_intPoints]
    have h1 : Rat.piIntCast ι w = (P : ℚ) • Rat.piIntCast ι z := by
      rw [hwz, map_zsmul]; funext l; simp
    have h2 := V.smul_mem (P : ℚ)⁻¹ hwV
    rwa [h1, smul_smul, inv_mul_cancel₀ hPQ, one_smul] at h2
  obtain ⟨d, hd⟩ := (mem_span_range_iff_exists_fun ℤ).1 hzV
  have hcoef : ∀ i, c' i - (P : ℤ) * d i = 0 := by
    refine Fintype.linearIndependent_iff.1 hyZ _ ?_
    have h2 : ∑ i, ((P : ℤ) * d i) • y i = w := by
      rw [hwz, ← hd]; funext l; simp [Finset.mul_sum, Finset.sum_apply, mul_assoc]
    simp only [sub_smul, Finset.sum_sub_distrib, h2, w, sub_self]
  exact hi₀ (by rw [← hc' i₀, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨d i₀, by linarith [hcoef i₀]⟩)

end Primitive

namespace Int.Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

noncomputable def minorGcd (A : _root_.Matrix (Fin m) ι ℤ) : ℤ :=
  (univ : Finset (Set.powersetCard ι m)).gcd (plucker m A.row)

private theorem plucker_row_ne_zero {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : plucker m A.row ≠ 0 := by
  intro h
  refine (plucker_eq_zero_iff m (A.map ((↑) : ℤ → ℚ)).row).1 ?_ hA
  funext s
  rw [show (A.map ((↑) : ℤ → ℚ)).row = fun i ↦ (Int.castRingHom ℚ) ∘ A.row i from rfl,
    plucker_map, h, Pi.zero_apply, map_zero]
  rfl

theorem one_le_minorGcd {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 1 ≤ minorGcd A := by
  have hD0 : minorGcd A ≠ 0 := fun h ↦ plucker_row_ne_zero hA
    (funext fun s ↦ Finset.gcd_eq_zero_iff.1 h s (mem_univ s))
  have hDnn : 0 ≤ minorGcd A := by
    rw [minorGcd, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]
    exact abs_nonneg _
  omega

theorem minorGcd_sq_mul_plucker_sq_le {k l N : ℕ} (hkl : k + l = N)
    (A : _root_.Matrix (Fin k) (Fin N) ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row)
    (y : Fin l → (Fin N → ℤ))
    (hAY : A * (_root_.Matrix.of y)ᵀ = 0)
    (hgcd : (univ : Finset (Set.powersetCard (Fin N) l)).gcd (plucker l y) = 1)
    (S : Set.powersetCard (Fin N) l) :
    (minorGcd A) ^ 2 * (plucker l y S) ^ 2 ≤ (A * Aᵀ).det := by
  classical
  have hA_pos : 0 < (A * Aᵀ).det := by
    rw [_root_.Matrix.det_mul_transpose_self_eq_sum_sq]
    obtain ⟨s, hs⟩ := Function.ne_iff.1 (plucker_row_ne_zero hA)
    exact Finset.sum_pos' (fun t _ ↦ sq_nonneg _) ⟨s, mem_univ s, sq_pos_of_ne_zero hs⟩
  let Y := _root_.Matrix.of y
  let D := minorGcd A
  let C : _root_.Matrix (Fin k ⊕ Fin l) (Fin N) ℤ :=
    _root_.Matrix.of fun r i ↦ Sum.elim (A · i) (Y · i) r
  have horth (a : Fin k) (b : Fin l) : ∑ i, A a i * Y b i = 0 := by
    simpa [Y, _root_.Matrix.mul_apply] using congrFun (congrFun hAY a) b
  let e₀ : Fin k ⊕ Fin l ≃ Fin N := finSumFinEquiv.trans (finCongr hkl)
  let d₀ := (C.submatrix id e₀).det
  have hdvd_all (T : Set.powersetCard (Fin N) l) :
      D * (Y * Yᵀ).det ∣ d₀ * plucker l y T := by
    let s : Finset (Fin N) := (T : Finset (Fin N))ᶜ
    have hT : (T : Finset (Fin N)).card = l := Set.powersetCard.card_eq T
    have hs : s.card = k := by
      rw [Finset.card_compl, Fintype.card_fin, hT]; omega
    have hsc : sᶜ.card = l := by simp [s, hT]
    let enum : Fin k ⊕ Fin l ≃ Fin N :=
      (Equiv.sumCongr (s.orderIsoOfFin hs).toEquiv
        ((sᶜ.orderIsoOfFin hsc).toEquiv.trans
          (Equiv.subtypeEquivRight fun _ ↦ Finset.mem_compl))).trans (Equiv.sumCompl (· ∈ s))
    have he_inl (a : Fin k) : enum (Sum.inl a) = s.orderEmbOfFin hs a :=
      Finset.coe_orderIsoOfFin_apply s hs a
    have he_inr (b : Fin l) : enum (Sum.inr b) = sᶜ.orderEmbOfFin hsc b :=
      Finset.coe_orderIsoOfFin_apply sᶜ hsc b
    have hminor : (C.submatrix id enum).det * (Y.submatrix id (sᶜ.orderEmbOfFin hsc)).det =
        (A.submatrix id (s.orderEmbOfFin hs)).det * (Y * Yᵀ).det := by
      set E : _root_.Matrix (Fin N) (Fin k ⊕ Fin l) ℤ :=
        _root_.Matrix.of fun i r ↦ Sum.elim (fun a ↦ if i = s.orderEmbOfFin hs a then 1 else 0)
          (fun b ↦ Y b i) r with hE
      have hCE : C * E = _root_.Matrix.fromBlocks
          (A.submatrix id (s.orderEmbOfFin hs)) 0
          (Y.submatrix id (s.orderEmbOfFin hs)) (Y * Yᵀ) := by
        ext r c
        rcases c with a | b
        · rcases r with a' | b' <;>
            simp [C, _root_.Matrix.mul_apply, hE, mul_ite, Finset.sum_ite_eq' Finset.univ]
        · rcases r with a' | b'
          · simp [C, _root_.Matrix.mul_apply, hE, horth a' b]
          · simp [C, _root_.Matrix.mul_apply, hE]
      have hEσ : E.submatrix enum id = _root_.Matrix.fromBlocks 1
          (_root_.Matrix.of fun a' b ↦ Y b (s.orderEmbOfFin hs a')) 0
          (Y.submatrix id (sᶜ.orderEmbOfFin hsc))ᵀ := by
        ext r c
        rcases r with a' | b' <;> rcases c with a | b
        · simp only [_root_.Matrix.submatrix_apply, id_eq, he_inl, hE, _root_.Matrix.of_apply,
            Sum.elim_inl, _root_.Matrix.fromBlocks_apply₁₁, _root_.Matrix.one_apply]
          exact if_congr ⟨fun h ↦ (s.orderEmbOfFin hs).injective h, fun h ↦ by rw [h]⟩ rfl rfl
        · simp [hE, he_inl]
        · have hne : sᶜ.orderEmbOfFin hsc b' ≠ s.orderEmbOfFin hs a := fun hcon ↦ by
            have h1 := sᶜ.orderEmbOfFin_mem hsc b'
            rw [hcon, Finset.mem_compl] at h1
            exact h1 (s.orderEmbOfFin_mem hs a)
          simp [hE, he_inr, hne]
        · simp [hE, he_inr, _root_.Matrix.transpose_apply]
      rw [← _root_.Matrix.det_fromBlocks_zero₁₂ (A.submatrix id (s.orderEmbOfFin hs))
        (Y.submatrix id (s.orderEmbOfFin hs)) (Y * Yᵀ), ← hCE,
        ← _root_.Matrix.submatrix_id_id (C * E),
        ← _root_.Matrix.submatrix_mul_equiv C E id enum id,
        _root_.Matrix.det_mul, hEσ, _root_.Matrix.det_fromBlocks_zero₂₁, _root_.Matrix.det_one,
        one_mul, _root_.Matrix.det_transpose]
    have hplY : (Y.submatrix id (sᶜ.orderEmbOfFin hsc)).det = plucker l y T := by
      change _ = plucker l Y.row T
      rw [plucker_row_eq_det_submatrix Y T]
      congr 1; ext i j
      exact congrArg (Y i) (congrFun (Finset.orderEmbOfFin_unique hsc
        (fun x ↦ by simp [s]) ((T : Finset (Fin N)).orderEmbOfFin hT).strictMono).symm j)
    let s_card : Set.powersetCard (Fin N) k := ⟨s, hs⟩
    rw [hplY, ← plucker_row_eq_det_submatrix A s_card] at hminor
    have hD_dvd : D * (Y * Yᵀ).det ∣ (C.submatrix id enum).det * plucker l y T := by
      rw [hminor]
      exact mul_dvd_mul_right (Finset.gcd_dvd (mem_univ s_card)) _
    have hperm : C.submatrix id e₀ =
        (C.submatrix id enum).submatrix id (e₀.trans enum.symm) := by ext i j; simp
    have hd_dvd : (C.submatrix id enum).det ∣ d₀ := by
      dsimp [d₀]; rw [hperm, _root_.Matrix.det_permute']; exact dvd_mul_left _ _
    exact hD_dvd.trans (mul_dvd_mul_right hd_dvd _)
  have hdvd_gcd : D * (Y * Yᵀ).det ∣ d₀ := by
    have h1 : D * (Y * Yᵀ).det ∣ univ.gcd (fun T ↦ d₀ * plucker l y T) :=
      Finset.dvd_gcd fun T _ ↦ hdvd_all T
    rw [Finset.gcd_mul_left, hgcd, mul_one] at h1
    exact h1.trans (normalize_dvd_iff.mpr dvd_rfl)
  have hS_le : (plucker l y S) ^ 2 ≤ (Y * Yᵀ).det := by
    rw [_root_.Matrix.det_mul_transpose_self_eq_sum_sq Y]
    exact single_le_sum (fun T _ ↦ sq_nonneg _) (mem_univ S)
  rcases eq_or_ne (plucker l y S) 0 with hS0 | hS0
  · rw [hS0]; simpa using hA_pos.le
  have hY_pos : 0 < (Y * Yᵀ).det := lt_of_lt_of_le (sq_pos_of_ne_zero hS0) hS_le
  obtain ⟨q, hq⟩ := hdvd_gcd
  have hsq : d₀ ^ 2 = (A * Aᵀ).det * (Y * Yᵀ).det := by
    have hCC : C * Cᵀ = _root_.Matrix.fromBlocks (A * Aᵀ) 0 0 (Y * Yᵀ) := by
      ext r c
      rcases r with a | b <;> rcases c with a' | b'
      · simp [C, _root_.Matrix.mul_apply]
      · simp [C, _root_.Matrix.mul_apply, horth a b']
      · simpa [C, _root_.Matrix.mul_apply, mul_comm] using horth a' b
      · simp [C, _root_.Matrix.mul_apply]
    rw [← _root_.Matrix.det_fromBlocks_zero₁₂ (A * Aᵀ) 0 (Y * Yᵀ), ← hCC,
      ← _root_.Matrix.submatrix_id_id (C * Cᵀ),
      ← _root_.Matrix.submatrix_mul_equiv C Cᵀ id e₀ id,
      _root_.Matrix.det_mul, ← _root_.Matrix.transpose_submatrix, _root_.Matrix.det_transpose, sq]
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hq, mul_zero, sq, mul_zero] at hsq
    exact (mul_pos hA_pos hY_pos).ne hsq
  have hq2 : 1 ≤ q ^ 2 := sq_pos_of_ne_zero hq0
  refine (mul_le_mul_of_nonneg_left hS_le (sq_nonneg D)).trans (le_of_mul_le_mul_right ?_ hY_pos)
  calc D ^ 2 * (Y * Yᵀ).det * (Y * Yᵀ).det
      = D ^ 2 * (Y * Yᵀ).det ^ 2 * 1 := by ring
    _ ≤ D ^ 2 * (Y * Yᵀ).det ^ 2 * q ^ 2 :=
        mul_le_mul_of_nonneg_left hq2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = d₀ ^ 2 := by rw [hq]; ring
    _ = (A * Aᵀ).det * (Y * Yᵀ).det := hsq

omit [LinearOrder ι] in
theorem finrank_ker (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    finrank ℚ ↥(LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin) = Fintype.card ι - m := by
  have h := LinearMap.finrank_range_add_finrank_ker (A.map ((↑) : ℤ → ℚ)).mulVecLin
  rw [show finrank ℚ ↥(LinearMap.range (A.map ((↑) : ℤ → ℚ)).mulVecLin)
      = (A.map ((↑) : ℤ → ℚ)).rank from rfl, show (A.map ((↑) : ℤ → ℚ)).rank = m by
        simpa using hA.rank_matrix, Module.finrank_pi] at h
  omega

omit [LinearOrder ι] in
theorem exists_ne_zero_mulVec_eq_zero (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hmn : m < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have hpos : 0 < finrank ℚ ↥(LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin) := by
    rw [finrank_ker A hA]; omega
  obtain ⟨⟨v, hv⟩, hv0⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  obtain ⟨N, z, hN, hz⟩ := exists_intCast_smul v
  have hz_ker : Rat.piIntCast ι z ∈ LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin := by
    rw [← hz]; exact Submodule.smul_mem _ _ hv
  rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply] at hz_ker
  refine ⟨z, fun h ↦ hv0 (Subtype.ext ?_), funext fun i ↦ ?_⟩
  · exact (smul_eq_zero.1 (by rw [hz, h, map_zero])).resolve_left (Int.cast_ne_zero.2 hN)
  · have hi := congrFun hz_ker i
    simp only [_root_.Matrix.mulVec, dotProduct, _root_.Matrix.map_apply, Rat.piIntCast_apply,
      Pi.zero_apply] at hi ⊢
    exact_mod_cast hi

end Int.Matrix

end
