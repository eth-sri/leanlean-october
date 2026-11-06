module

public import Mathlib
public import OAI.Combinatorics.EuclideanRamsey.Main

@[expose] public section

/-! Theorem D: the radian 9-gon is Ramsey iff `tan (θ/2)` is algebraic. -/

set_option autoImplicit true
namespace OAI
set_option hygiene false
local notation "𝔟" => (e i)
local notation "𝔞" => (n * θ)
notation "𝔬" => Option (Fin 2)
noncomputable section
open scoped TensorProduct
open MvPolynomial
namespace EuclideanRamsey
namespace Radian

notation:max "τ" θ:max => Real.tan (θ / 2)

def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

notation:max "ρ" θ:max => radianConfig θ

variable {R S : Type*} [CommRing R] [CommRing S]

def rot (z : R) : ℕ → Fin 2 → R
  | 0 => ![1, 0]
  | n + 1 => ![(1 - z ^ 2) * rot z n 0 - 2 * z * rot z n 1, 2 * z * rot z n 0 + (1 - z ^ 2) * rot z n 1]

def qv (z : R) (n : ℕ) (α : 𝔬) : R := α.elim ((1 + z ^ 2) ^ n) (rot z n)

def e : 𝔬 × 𝔬 ≃ Fin 9 :=
  ((finSuccEquiv 2).symm.prodCongr (finSuccEquiv 2).symm).trans finProdFinEquiv

abbrev C := 𝔬 × 𝔬

def Ecl (z w : R) : Matrix C C R := fun i q => qv z 𝔟 q.1 * qv w 𝔟 q.2

lemma map_rot [FunLike F R S] [RingHomClass F R S] (f : F) z (n j) : f (rot z n j) = rot (f z) n j := by
  induction n generalizing j <;> fin_cases j <;> simp [rot, map_ofNat, *]

lemma map_qv [FunLike F R S] [RingHomClass F R S] (f : F) z (n α) : f (qv z n α) = qv (f z) n α := by
  cases α <;> simp [qv, map_rot]

lemma map_Ecl (f : R →+* S) z w : f.mapMatrix (Ecl z w) = Ecl (f z) (f w) := by
  ext
  simp [Ecl, map_qv]

lemma det_Ecl : (Ecl (X (Sum.inl ()) : MvPolynomial (Unit ⊕ Unit) ℚ) (X (Sum.inr ()))).det ≠ 0 := fun h => by
  have := congrArg (eval (Sum.elim 2 3)) h
  rw [RingHom.map_det, map_Ecl, ← Matrix.det_reindex_self e, ← Matrix.etaExpand_eq (Matrix.reindex _ _ _)] at this
  have h9 : (Matrix.etaExpand (Matrix.reindex e e (Ecl (2 : ℚ) 3))).rank = 9 := by
    norm_num [Matrix.etaExpand, FinVec.etaExpand, FinVec.map, FinVec.seq, Matrix.vecTail, Ecl, qv, rot, e, finProdFinEquiv, Fin.divNat, Fin.modNat, show finSuccEquiv 2 1 = some 0 from rfl, show finSuccEquiv 2 2 = some 1 from rfl]
    eval_rank
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 (LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq (h9.trans (Module.finrank_fin_fun ℚ).symm))))).ne_zero (by simp_all)

abbrev P1 := MvPolynomial Unit ℚ
abbrev R1 := FractionRing P1
abbrev P2 := MvPolynomial (Unit ⊕ Unit) ℚ
abbrev R2 := FractionRing P2
local instance : Algebra ℚ R1 := OreLocalization.instAlgebra
abbrev Y : R1 := algebraMap P1 R1 (X ())
abbrev Z (i : Unit ⊕ Unit) : R2 := algebraMap P2 R2 (X i)

lemma side_inj (i : Unit → Unit ⊕ Unit) (hi : i.Injective) :
    Function.Injective ((IsScalarTower.toAlgHom ℚ P2 R2).comp (rename i)).toRingHom :=
  (IsFractionRing.injective P2 R2).comp (rename_injective i hi)

def sideMap (i : Unit → Unit ⊕ Unit) (hi : i.Injective) : R1 →ₐ[ℚ] R2 :=
  IsFractionRing.liftAlgHom (side_inj i hi)

@[simp] lemma sideMap_alg i hi p :
    sideMap i hi (algebraMap P1 R1 p) = algebraMap P2 R2 (rename i p) :=
  IsFractionRing.lift_algebraMap (side_inj i hi) p

def emb : R1 ⊗[ℚ] R1 →ₐ[ℚ] R2 :=
  Algebra.TensorProduct.lift (sideMap _ Sum.inl_injective) (sideMap _ Sum.inr_injective) fun _ _ => .all _ _

theorem emb_injective : Function.Injective emb := by
  let ι := IsScalarTower.toAlgHom ℚ P1 R1
  have key x : ∃ p q, ∃ y, ι p ≠ 0 ∧ ι q ≠ 0 ∧ (ι p ⊗ₜ ι q) * x = Algebra.TensorProduct.map ι ι y := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, 1, 0, by simp⟩
    | tmul a b =>
      obtain ⟨a, p, hp, rfl⟩ := IsFractionRing.div_surjective (A := P1) a
      obtain ⟨b, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := P1) b
      have hp := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := R1) hp
      have hq := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := R1) hq
      exact ⟨p, q, a ⊗ₜ b, hp, hq, by simp [ι, mul_div_cancel₀ _ hp, mul_div_cancel₀ _ hq]⟩
    | add x y hx hy =>
      obtain ⟨p, q, u, hp, hq, hu⟩ := hx
      obtain ⟨p', q', v, hp', hq', hv⟩ := hy
      exact ⟨p * p', q * q', (p' ⊗ₜ q') * u + (p ⊗ₜ q) * v, by grind, by grind, by
        simp [ ← hu, ← hv, ← Algebra.TensorProduct.tmul_mul_tmul]
        ring⟩
  have hc : emb.comp (Algebra.TensorProduct.map ι ι) = (IsScalarTower.toAlgHom ℚ P2 R2).comp (tensorEquivSum ℚ Unit Unit ℚ).toAlgHom := by
    ext <;> simp [emb, ι]
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨p, q, y, hp, hq, h⟩ := key x
  have : y = 0 := by simpa [← h, hx] using (AlgHom.congr_fun hc y).symm
  simpa [this, ← mul_assoc, hp, hq, ← Algebra.TensorProduct.one_def] using congrArg ((ι p)⁻¹ ⊗ₜ[ℚ] (ι q)⁻¹ * ·) h

lemma trig (hc : Real.cos θ ≠ -1) (n : ℕ) j :
    (1 + τ θ ^ 2) ^ n * ![Real.cos 𝔞, Real.sin 𝔞] j = rot τ θ n j := by
  induction n generalizing j with
  | zero => fin_cases j <;> simp [rot]
  | succ n ih =>
    fin_cases j <;> simp [rot, ← ih, add_mul, Real.cos_add, Real.sin_add,
      Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq θ hc, Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq θ] <;>
      field_simp <;> ring

lemma circle θ k : dist (radianConfig θ k) 0 = 1 := by
  simp [radianConfig, EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma span (hinj : Function.Injective ρ θ) : affineSpan ℝ (Set.range ρ θ) = ⊤ :=
  top_unique <| ((EuclideanGeometry.Cospherical.affineIndependent ⟨0, 1, Set.forall_mem_range.2 (circle θ)⟩
    (Set.range_comp_subset_range (Fin.castLE (by grind)) _) (hinj.comp (Fin.castLE_injective _))).affineSpan_eq_top_iff_card_eq_finrank_add_one.2
    (by simp)).ge.trans (affineSpan_mono _ (Set.range_comp_subset_range _ _))

theorem algebraic_of_tan (h : IsAlgebraic ℚ τ θ) :
    IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  have hd := (isAlgebraic_one.add (h.pow 2)).inv
  refine ⟨?_, by rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq, div_eq_mul_inv, two_mul]; exact (h.add h).mul hd⟩
  by_cases hc : Real.cos θ = -1
  · rw [hc]
    exact isAlgebraic_one.neg
  · rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq _ hc, div_eq_mul_inv]
    exact (isAlgebraic_one.sub (h.pow 2)).mul hd

theorem cos_ne (ht : Transcendental ℚ τ θ) : Real.cos θ ≠ -1 := fun h => ht <| by
  have := Real.cos_sq (θ / 2)
  rw [mul_div_cancel₀ θ two_ne_zero, h] at this
  norm_num at this
  simp [Real.tan_eq_sin_div_cos, this, isAlgebraic_zero]

abbrev K (θ : ℝ) := IntermediateField.adjoin ℚ (Set.range fun _ : Unit => τ θ)

def w (k : ℕ) (α : 𝔬) : R1 := qv Y k α / (1 + Y ^ 2) ^ k

section
variable (ht : Transcendental ℚ τ θ)
include ht

abbrev φ : R1 ≃ₐ[ℚ] K θ :=
  (algebraicIndependent_unique_type_iff.mpr ht).aevalEquivField

lemma real_w (k : Fin 9) (α) : (φ ht (w k α) : ℝ) = realAugmented ρ θ k α := by
  have : (1 + τ θ ^ 2) ^ (k : ℕ) ≠ 0 := by positivity
  have h := map_qv ((IntermediateField.val _).comp (φ ht).toAlgHom) Y k α
  cases α <;> simp_all [w, qv, ← trig (cos_ne ht), realAugmented, radianConfig]
end

theorem radian_configuration (θ : ℝ) (ht : Transcendental ℚ τ θ) :
    Function.Injective ρ θ ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey ρ θ := by
  let M : Matrix C C R2 := fun i q => emb (w 𝔟 q.1 ⊗ₜ w 𝔟 q.2)
  have hM : M.det ≠ 0 := by
    have hZ (i) : (1 + Z i ^ 2 : R2) ≠ 0 := fun h => by
      simpa using congrArg (eval 0) (IsFractionRing.injective P2 R2 (by simpa using h : algebraMap P2 R2 (1 + X i ^ 2) = algebraMap _ _ 0))
    have hE : Ecl (Z (.inl ())) (Z (.inr ())) = Matrix.diagonal (fun i => (1 + Z (.inl ()) ^ 2) ^ (e i : ℕ) * (1 + Z (.inr ()) ^ 2) ^ (e i : ℕ)) * M := by
      ext i q
      rw [Matrix.diagonal_mul]
      simp [Ecl, M, emb, w, map_qv]; field_simp [hZ]
    have := det_Ecl
    rw [← (IsFractionRing.injective P2 R2).ne_iff, map_zero, RingHom.map_det, map_Ecl, hE, Matrix.det_mul] at this
    exact right_ne_zero_of_mul this
  have hinj : Function.Injective ρ θ := fun i j h => by_contra fun hne => hM <| Matrix.det_zero_of_row_eq (e.symm.injective.ne hne) <| by
    have (α : 𝔬) : w i α = w j α := (φ ht).injective (Subtype.val_injective (by rw [real_w, real_w]; simp [realAugmented, h]))
    ext q
    simp [M, this]
  refine ⟨hinj, circle θ, fun hR => ?_⟩
  obtain ⟨P, hP, hm⟩ := ramsey_realCriterion _ (by decide) (span hinj) hR
  let F := emb.comp (Algebra.TensorProduct.congr (φ ht).symm (φ ht).symm).toAlgHom
  let b := Module.Basis.ofVectorSpace (K θ) ℝ
  let C := (TensorProduct.congr (b.repr.restrictScalars ℚ) (b.repr.restrictScalars ℚ)).trans (finsuppTensorFinsupp ℚ ℚ _ _ _ _)
  have hC (x y : K θ) T : C (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T * ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) = (x ⊗ₜ[ℚ] y) • C T := by
    ext ⟨l, m⟩
    induction T using TensorProduct.inductionOn with
    | tmul u v =>
      have (x : K θ) u : b.repr (x * u) = x • b.repr u := by simpa [Algebra.smul_def] using b.repr.map_smul x u
      simp [C, mul_comm v, this]
    | add U V hU hV => simp_all [mul_add, add_mul]
  have : C (P (some 0) (some 0)) = 0 := Finsupp.ext fun kl => (emb_injective.comp (AlgEquiv.injective _) :  Function.Injective F) <| by
    have := Matrix.eq_zero_of_mulVec_eq_zero hM (v := fun q => F (C (P q.1 q.2) kl)) (funext fun i => by
      have h := congrArg (fun T => F (C T kl)) (hP 𝔟)
      simp only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, ← real_w ht, hC, map_zero] at h
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, F] using h)
    exact congrFun this (some 0, some 0)
  have h0 : Algebra.TensorProduct.lmul' ℚ (P (some 0) (some 0)) = 1 := congrFun₂ hm 0 0
  simp [C.map_eq_zero_iff.1 this] at h0

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ τ θ) :
    ¬ Ramsey ρ θ :=
  (radian_configuration θ ht).2.2

theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective ρ θ) :
    Ramsey ρ θ ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  refine ⟨fun hR => by_contra fun h => radian_not_ramsey θ (fun ht => h (algebraic_of_tan ht)) hR, fun ⟨hc, hs⟩ =>
    fieldCriterion_ramsey _ (by norm_num) (by norm_num) hinj ?_⟩
  have (n : ℕ) : IsAlgebraic ℚ (Real.cos 𝔞) ∧ IsAlgebraic ℚ (Real.sin 𝔞) := by
    induction n with
    | zero => simp [isAlgebraic_one, isAlgebraic_zero]
    | succ n ih =>
      simp only [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
      exact ⟨(ih.1.mul hc).sub (ih.2.mul hs), (ih.2.mul hc).add (ih.1.mul hs)⟩
  let F := IntermediateField.adjoin ℚ (Set.range fun ij : Fin 9 × Fin 2 => ρ θ ij.1 ij.2)
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin
    fun _ ⟨⟨k, j⟩, h⟩ => h ▸ (by fin_cases j <;> simp [radianConfig, this] : IsAlgebraic ℚ _).isIntegral
  obtain ⟨t, ht, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1 (.of_isSeparable ℚ F)
  let φ := Algebra.TensorProduct.map F.val F.val
  have h x (hx : x ∈ F) T : x ⊗ₜ 1 * (φ t * T) * (1 ⊗ₜ x) = φ t * (x ⊗ₜ 1 * T * (x ⊗ₜ 1)) := by
    linear_combination x ⊗ₜ 1 * T * (by simpa [φ] using congrArg φ (ht ⟨x, hx⟩) : _ = (0 : ℝ ⊗[ℚ] ℝ))
  refine ⟨fun α β => if α = β then φ t * (α.elim (-1) 1 ⊗ₜ 1) else 0, fun i => ?_, ?_⟩
  · have (α : 𝔬) : realAugmented ρ θ i α ∈ F := by
      cases α
      exacts [one_mem _, IntermediateField.subset_adjoin _ _ ⟨(i, _), rfl⟩]
    have : ∑ α, realAugmented ρ θ i α * α.elim (-1) 1 * realAugmented ρ θ i α = 0 := by
      simp [ realAugmented, radianConfig, ← sq]
    simp_all [arrayEvaluation, ← mul_add, ← TensorProduct.add_tmul]
  · have : (Algebra.TensorProduct.lmul' ℚ).comp φ = F.val.comp (Algebra.TensorProduct.lmul' ℚ) := by
      ext <;> simp [φ]
    ext α β
    show Algebra.TensorProduct.lmul' ℚ (ite _ _ _) = _
    simp [Matrix.one_apply, apply_ite, ← AlgHom.comp_apply, this, ht1]

theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective ρ θ) :
    Ramsey ρ θ ↔ IsAlgebraic ℚ τ θ :=
  ⟨fun hR => by_contra fun h => radian_not_ramsey θ h hR, fun h => (radian_ramsey_iff θ hinj).2 (algebraic_of_tan h)⟩
