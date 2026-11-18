module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ProjectiveIntegerHeight
import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.ShearNormalization
import CCDN.Plane.GridHeight
import CCDN.Plane.ProjectivePlaneBezout
import CCDN.Projection.ProjectivePlaneProjection
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace CCDN
noncomputable section

section GridPoly
open Polynomial

private def gridEisensteinCorrection {K : Type*} [Field K] (V : K[X]) (k : ℕ) : K[X] :=
  V * (X ^ k + C (V.coeff 1 / V.coeff 0 + 1) * X)

private def gridEisensteinPolynomial {K : Type*} [Field K] (V : K[X]) (k : ℕ) : K[X][X] :=
  V.map C + C (V * C (V.coeff 0)⁻¹) * (X ^ V.natDegree - V.map C) +
    C (gridEisensteinCorrection V k)

private lemma gridEisensteinPolynomial_coeff {K : Type*} [Field K] (V : K[X]) (k i : ℕ) :
    (gridEisensteinPolynomial V k).coeff i =
      C (V.coeff i) + V * C (V.coeff 0)⁻¹ *
        ((X ^ V.natDegree : K[X][X]).coeff i - C (V.coeff i)) +
      if i = 0 then gridEisensteinCorrection V k else 0 := by
  simp only [gridEisensteinPolynomial, coeff_add, coeff_map, coeff_C_mul, coeff_sub, coeff_C]

private lemma gridEisensteinPolynomial_constantCoeff {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (h0 : V.coeff 0 ≠ 0) (hd : 0 < V.natDegree) :
    (gridEisensteinPolynomial V k).coeff 0 =
      C (V.coeff 0) - V + gridEisensteinCorrection V k := by
  rw [gridEisensteinPolynomial_coeff]
  simp only [coeff_X_pow, ne_of_lt hd, ite_false, zero_sub, ite_true]
  rw [mul_neg, mul_assoc, ← C_mul, inv_mul_cancel₀ h0, C_1, mul_one]; rfl

private theorem gridEisensteinPolynomial_irreducible {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) :
    Irreducible (gridEisensteinPolynomial V k) := by
  have hdle : (gridEisensteinPolynomial V k).natDegree ≤ V.natDegree :=
    natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
      rw [gridEisensteinPolynomial_coeff, ite_eq_right (by omega : i ≠ 0)]
      simp [coeff_eq_zero_of_natDegree_lt hi, coeff_X_pow, ne_of_gt hi]
  have htop : (gridEisensteinPolynomial V k).coeff V.natDegree = 1 := by
    rw [gridEisensteinPolynomial_coeff, hm.coeff_natDegree]; simp [ne_of_gt hd]
  have hmon : (gridEisensteinPolynomial V k).Monic :=
    monic_of_natDegree_le_of_coeff_eq_one V.natDegree hdle htop
  have hdeg : (gridEisensteinPolynomial V k).natDegree = V.natDegree :=
    le_antisymm hdle (le_natDegree_of_ne_zero (htop.symm ▸ one_ne_zero))
  have hred : (gridEisensteinPolynomial V k).map (evalRingHom 0) = X ^ V.natDegree := by
    have he : (evalRingHom (0 : K)).comp C = RingHom.id K := by ext a; simp
    simp only [gridEisensteinPolynomial, gridEisensteinCorrection, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, map_map, he, map_id]
    simp [← coeff_zero_eq_eval_zero, h0, show k ≠ 0 by omega]
  have hsimp : ((gridEisensteinPolynomial V k).coeff 0).coeff 1 = V.coeff 0 := by
    rw [gridEisensteinPolynomial_constantCoeff V k h0 hd]
    simp only [gridEisensteinCorrection, mul_add, coeff_add, coeff_sub, coeff_C,
      one_ne_zero, ite_false, zero_sub]
    rw [coeff_mul_X_pow', ite_eq_right (by omega : ¬ k ≤ 1), ← mul_assoc, coeff_mul_X, coeff_mul_C]
    field_simp; ring
  let P : Ideal K[X] := Ideal.span {X}
  have hp : P.IsPrime := Ideal.isPrime_span_singleton_of_prime prime_X
  apply Polynomial.IsEisensteinAt.irreducible (𝓟 := P) _ hp hmon.isPrimitive (hdeg ▸ hd)
  refine ⟨hmon.leadingCoeff_notMem hp.ne_top, ?_, ?_⟩
  · intro i hi; rw [hdeg] at hi
    exact Ideal.mem_span_singleton.mpr (X_dvd_iff.mpr
      (by simpa [coeff_map, coeff_X_pow, ne_of_lt hi, ← coeff_zero_eq_eval_zero] using
        congrArg (fun q : K[X] => q.coeff i) hred))
  · intro h
    change (gridEisensteinPolynomial V k).coeff 0 ∈ (Ideal.span ({X} : Set K[X])) ^ 2 at h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    exact (hsimp ▸ h0) ((X_pow_dvd_iff.mp h) 1 (by decide))

private theorem gridEisensteinPolynomial_totalDegree {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) (hs : V.natDegree ≤ k + 1) :
    bivariateTotalDegree (gridEisensteinPolynomial V k) = V.natDegree + k := by
  have hadd {f g : K[X][X]} :
      bivariateTotalDegree (f + g) ≤ max (bivariateTotalDegree f) (bivariateTotalDegree g) := by
    unfold bivariateTotalDegree; rw [map_add]; exact MvPolynomial.totalDegree_add _ _
  have hC (f : K[X]) : bivariateTotalDegree (C f) ≤ f.natDegree := by
    rw [bivariateTotalDegree_le_iff]; intro i j hij
    by_cases hi : i = 0
    · subst i; simpa using le_natDegree_of_ne_zero (by simpa using hij : f.coeff j ≠ 0)
    · simp [coeff_C, hi] at hij
  have hmapC (f : K[X]) : bivariateTotalDegree (f.map C) ≤ f.natDegree := by
    rw [bivariateTotalDegree_le_iff]; intro i j hij
    by_cases hj : j = 0
    · subst j; simpa using le_natDegree_of_ne_zero (by simpa using hij : f.coeff i ≠ 0)
    · simp [coeff_map, coeff_C, hj] at hij
  have hcorr : IsMonicOfDegree (gridEisensteinCorrection V k) (V.natDegree + k) := by
    refine IsMonicOfDegree.mul ⟨rfl, hm⟩ ((isMonicOfDegree_X_pow K k).add_right ?_)
    have hh : (C (V.coeff 1 / V.coeff 0 + 1) * X).natDegree ≤ 1 := by
      simpa using natDegree_mul_le (p := (C (V.coeff 1 / V.coeff 0 + 1) : K[X])) (q := X)
    omega
  refine le_antisymm ?_ ?_
  · unfold gridEisensteinPolynomial
    refine hadd.trans (max_le (hadd.trans (max_le ((hmapC V).trans (by omega)) ?_))
      ((hC _).trans hcorr.natDegree_eq.le))
    have hsub : (X ^ V.natDegree - V).natDegree < V.natDegree :=
      IsMonicOfDegree.natDegree_sub_lt hd.ne' (isMonicOfDegree_X_pow K _) ⟨rfl, hm⟩
    rw [show (X ^ V.natDegree : K[X][X]) - V.map C = (X ^ V.natDegree - V).map C by simp]
    have h1 := hC (V * C (V.coeff 0)⁻¹)
    have h2 := hmapC (X ^ V.natDegree - V)
    have h3 : (V * C (V.coeff 0)⁻¹).natDegree ≤ V.natDegree := natDegree_mul_C_le _ _
    exact (bivariateTotalDegree_mul_le _ _).trans (by omega)
  · have hhigh : ((gridEisensteinPolynomial V k).coeff 0).coeff (V.natDegree + k) = 1 := by
      rw [gridEisensteinPolynomial_constantCoeff V k h0 hd, coeff_add, coeff_sub,
        coeff_C, ite_eq_right (by omega : V.natDegree + k ≠ 0),
        coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_zero, zero_add,
        ← hcorr.natDegree_eq]
      exact hcorr.monic.coeff_natDegree
    simpa using bivariateTotalDegree_coeff_le (gridEisensteinPolynomial V k) 0 (V.natDegree + k)
      (hhigh.symm ▸ one_ne_zero)

private theorem exists_absolutely_irreducible_plane_grid
    {K L : Type*} [Field K] [Infinite K] [Field L] (φ : K →+* L)
    (s : Finset K) (hs : 0 < s.card) (d : ℕ)
    (hd : s.card + 2 ≤ d) (hsize : 2 * s.card ≤ d + 1) :
    ∃ f : MvPolynomial (Fin 2) K,
      f.totalDegree = d ∧ Irreducible (MvPolynomial.map φ f) ∧
        ∀ z : Fin 2 → K, (∀ i, z i ∈ s) → MvPolynomial.eval z f = 0 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset s
  let t := s.image fun x => x - a
  have ht : t.card = s.card := Finset.card_image_of_injective _ fun _ _ h => sub_left_inj.mp h
  let V : K[X] := ∏ x ∈ t, (X - C x)
  have hm : V.Monic := monic_prod_X_sub_C id t
  have hvdeg : V.natDegree = s.card := (natDegree_finsetProd_X_sub_C_eq_card t id).trans ht
  have hv0 : V.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [V, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
    refine Finset.prod_ne_zero_iff.mpr fun b hb => neg_ne_zero.mpr fun h => ?_
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (h ▸ hb)
    exact ha (sub_eq_zero.mp he ▸ hx)
  let k := d - s.card
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hvpos : 0 < V.natDegree := by omega
  let g := (bivariatePolynomialEquiv K).symm (gridEisensteinPolynomial V k)
  have hgdeg : g.totalDegree = d := by
    change bivariateTotalDegree (gridEisensteinPolynomial V k) = _
    rw [gridEisensteinPolynomial_totalDegree V k hm hvpos hv0 hk (by dsimp [k]; omega), hvdeg]
    dsimp [k]; omega
  have hgir : Irreducible (MvPolynomial.map φ g) := by
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    rw [← bivariatePolynomialEquiv_map]
    dsimp only [g]; rw [AlgEquiv.apply_symm_apply]
    change Irreducible ((gridEisensteinPolynomial V k).map (Polynomial.mapRingHom φ))
    have he : (Polynomial.mapRingHom φ).comp C = C.comp φ := by ext; simp
    have hmap : (gridEisensteinPolynomial V k).map (Polynomial.mapRingHom φ) =
        gridEisensteinPolynomial (V.map φ) k := by
      simp only [gridEisensteinPolynomial, gridEisensteinCorrection, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, Polynomial.map_one, coe_mapRingHom, map_map, he, coeff_map,
        natDegree_map_eq_of_injective φ.injective, map_inv₀, map_div₀, map_add, map_one]
    rw [hmap]
    exact gridEisensteinPolynomial_irreducible _ k (hm.map φ)
      (by rwa [natDegree_map_eq_of_injective φ.injective])
      (by simpa only [coeff_map, map_ne_zero_iff φ φ.injective] using hv0) hk
  refine ⟨affineTranslation K (fun _ => -a) g, ?_, ?_, fun z hz => ?_⟩
  · rwa [affineTranslation_totalDegree]
  · rwa [affineTranslation_map, affineTranslation_irreducible_iff]
  · rw [affineTranslation_eval]
    have hzV (i) : V.eval (z i - a) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z i, hz i, rfl⟩) (by simp)
    have heC (y : K) : (evalRingHom y).comp C = RingHom.id K := by ext; simp
    have hh : ((gridEisensteinPolynomial V k).map (evalRingHom (z 1 - a))).eval (z 0 - a) = 0 := by
      simp [gridEisensteinPolynomial, gridEisensteinCorrection, map_map, heC, hzV 0, hzV 1]
    have he := bivariatePolynomialEquiv_eval g (z 0 - a) (z 1 - a)
    change ((bivariatePolynomialEquiv K ((bivariatePolynomialEquiv K).symm _)).map
      (evalRingHom (z 1 - a))).eval (z 0 - a) = _ at he
    rw [AlgEquiv.apply_symm_apply, hh] at he
    rw [show z + (fun _ => -a) = ![z 0 - a, z 1 - a] by funext i; fin_cases i <;> simp [sub_eq_add_neg]]
    exact he.symm

end GridPoly

open MvPolynomial

private lemma affineProjectivePoint_integer_height_le {n : ℕ} (z : IntPoint n)
    {B : ℝ} (hB : 1 ≤ B) (hz : InBox z B) :
    (affineProjectivePoint (rationalPoint z)).mulHeight ≤ B := by
  let w : IntPoint (n + 1) := Fin.cons 1 z
  have hw0 : w 0 ≠ 0 := one_ne_zero
  have he : affineProjectivePoint (rationalPoint z) =
      Projectivization.mk ℚ (rationalPoint w)
        (rationalPoint_ne_zero fun h => hw0 (congrFun h 0)) := by
    convert affineProjectivePoint_eq_integer w hw0 using 1
    congr 1; funext j; simp [w, rationalPoint]
  rw [he]
  exact projective_integer_height_le w (fun h => hw0 (congrFun h 0)) fun j =>
    Fin.cases (by simpa [w] using hB) (fun i => hz i) j

private lemma projective_closure_absolute_irreducible {n d : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (hd : f.totalDegree = d) (hf : AbsolutelyIrreducibleRat f) :
    (scaledHomogenize d 1 f).IsHomogeneous d ∧
      (scaledHomogenize d 1 f).totalDegree = d ∧
        AbsolutelyIrreducibleRat (scaledHomogenize d 1 f) := by
  have hhom := scaledHomogenize_homogeneous 1 f hd.le
  have h0 : scaledHomogenize d 1 f ≠ 0 := fun h => by
    have hh := affineChart_scaledHomogenize_one d f
    rw [h, map_zero] at hh; exact hf.ne_zero (by rw [← hh, map_zero])
  refine ⟨hhom, hhom.totalDegree h0, ?_⟩
  dsimp only [AbsolutelyIrreducibleRat]
  rw [scaledHomogenize_map, map_one]
  have hdeg : (map (algebraMap ℚ (AlgebraicClosure ℚ)) f).totalDegree = d :=
    (totalDegree_map_of_injective (algebraMap ℚ (AlgebraicClosure ℚ)).injective _).trans hd
  simpa only [hdeg] using scaledHomogenize_irreducible _ hf one_ne_zero

private lemma degree_square_le_five_fourths_power (d : ℕ) :
    ((d : ℝ) + 1) ^ 2 ≤ 16 * (5 / 4 : ℝ) ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    by_cases hd : d < 8
    · interval_cases d <;> norm_num
    · have hdR : (8 : ℝ) ≤ d := mod_cast (show 8 ≤ d by omega)
      calc (((d + 1 : ℕ) : ℝ) + 1) ^ 2 = ((d : ℝ) + 2) ^ 2 := by push_cast; ring
        _ ≤ (5 / 4 : ℝ) * ((d : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((d : ℝ) - 8)]
        _ ≤ (5 / 4 : ℝ) * (16 * (5 / 4 : ℝ) ^ d) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring

theorem projective_integral_curve_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧
        AbsolutelyIrreducibleRat F ∧
          (Ideal.span {F}).IsPrime ∧ HasProjectiveCurveDegree (Ideal.span {F}) d ∧
            ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
              (projectiveCount (projectiveIdealZeroLocus (Ideal.span {F})) B : ℝ) := by
  classical
  have hplane : ∃ F : MvPolynomial (Fin 3) ℚ, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧ AbsolutelyIrreducibleRat F ∧
        ((d : ℝ) ^ 2 / 5) * (B : ℝ) ^ (2 / (d : ℝ)) ≤
          (projectiveCount (projectiveZeroLocus F) B : ℝ) := by
    by_cases hlarge : 4 ≤ d
    · let q := (d - 1) / 2
      let r := (d - 1) / 4
      let B := q - r
      have hB : 1 ≤ B := by dsimp [B, q, r]; omega
      have hrB : r ≤ B := by dsimp [B, q, r]; omega
      let s : Finset ℤ := Finset.Icc (-(B : ℤ)) (r : ℤ)
      have hs : s.card = q + 1 := by rw [Int.card_Icc]; dsimp [B, q, r]; omega
      let t : Finset ℚ := s.image (Int.castRingHom ℚ)
      have ht : t.card = q + 1 := by
        change (s.image (fun x : ℤ => (x : ℚ))).card = _
        rw [Finset.card_image_of_injective _ Int.cast_injective, hs]
      obtain ⟨f, hfdeg, hfir, hfzero⟩ := exists_absolutely_irreducible_plane_grid
        (algebraMap ℚ (AlgebraicClosure ℚ)) t (by rw [ht]; omega) d
        (by rw [ht]; dsimp [q]; omega) (by rw [ht]; dsimp [q]; omega)
      obtain ⟨hhom, hdeg, hir⟩ := projective_closure_absolute_irreducible f hfdeg hfir
      have hcount : (q + 1) ^ 2 ≤ projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f)) B := by
        rw [← hs, ← show (Fintype.piFinset fun _ : Fin 2 => s).card = s.card ^ 2 by simp]
        refine Finset.card_le_card_of_injOn (fun z => affineProjectivePoint (rationalPoint z)) ?_ ?_
        · intro z hz
          have hz' : ∀ j, z j ∈ s := Fintype.mem_piFinset.mp hz
          refine mem_projectivePoints.mpr ⟨affineProjectivePoint_integer_height_le z (mod_cast hB) fun j => ?_, ?_⟩
          · have hab := Finset.mem_Icc.mp (hz' j)
            exact_mod_cast abs_le.mpr ⟨hab.1, hab.2.trans (mod_cast hrB)⟩
          · unfold affineProjectivePoint
            rw [mem_projectiveZeroLocus_mk hhom, ← affineChart_eval, affineChart_scaledHomogenize_one]
            exact hfzero _ fun j => Finset.mem_image.mpr ⟨z j, hz' j, rfl⟩
        · intro x _ y _ he
          funext j; exact Int.cast_injective (congrFun (affineProjectivePoint_injective 2 he) j)
      have hBeq : B = (d + 1) / 4 := by dsimp [B, q, r]; omega
      rw [hBeq] at hcount hB
      refine ⟨scaledHomogenize d 1 f, (d + 1) / 4, hB, hhom, hdeg, hir, ?_⟩
      let BR : ℝ := ((d + 1) / 4 : ℕ)
      have hBR0 : 0 ≤ BR := Nat.cast_nonneg _
      have hsize : 4 * BR ≤ (d : ℝ) + 1 := by
        dsimp [BR]; exact_mod_cast (by omega : 4 * ((d + 1) / 4) ≤ d + 1)
      have hrpow : BR ^ (2 / (d : ℝ)) ≤ 5 / 4 := by
        have hh := degree_square_le_five_fourths_power d
        have hs2 : (4 * BR) ^ 2 ≤ ((d : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsize 2
        have hpow : BR ^ 2 ≤ (5 / 4 : ℝ) ^ d := by nlinarith
        have hdR : (0 : ℝ) < d := mod_cast hd
        apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hBR0 _) (by norm_num) hdR).mp
        rw [← Real.rpow_mul hBR0, show (2 / (d : ℝ)) * d = 2 by field_simp]
        simpa only [Real.rpow_two, Real.rpow_natCast] using hpow
      have hdsR : (d : ℝ) ≤ 2 * ((q + 1 : ℕ) : ℝ) := mod_cast (by dsimp [q]; omega : d ≤ 2 * (q + 1))
      have hnum : ((d : ℝ) ^ 2 / 5) * BR ^ (2 / (d : ℝ)) ≤ ((q + 1 : ℕ) : ℝ) ^ 2 := calc
        ((d : ℝ) ^ 2 / 5) * BR ^ (2 / (d : ℝ)) ≤ ((d : ℝ) ^ 2 / 5) * (5 / 4) :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ ≤ ((q + 1 : ℕ) : ℝ) ^ 2 := by nlinarith [sq_nonneg (((q + 1 : ℕ) : ℝ) - (d : ℝ) / 2)]
      exact hnum.trans (mod_cast hcount)
    · let f : MvPolynomial (Fin 2) ℚ := X 0 - X 1 ^ d
      have hfdeg : f.totalDegree = d := by
        refine le_antisymm ((totalDegree_sub _ _).trans (by simp [max_eq_right (by omega : 1 ≤ d)])) ?_
        have he : bivariatePolynomialEquiv ℚ f = Polynomial.X - Polynomial.C (Polynomial.X ^ d) := by
          simp [f, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
        have hc : (((bivariatePolynomialEquiv ℚ f).coeff 0).coeff d : ℚ) ≠ 0 := by
          rw [he]
          simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
            Polynomial.coeff_neg, Polynomial.coeff_X_pow, ite_true, zero_sub, neg_ne_zero]
          exact _root_.one_ne_zero
        simpa [bivariateTotalDegree] using bivariateTotalDegree_coeff_le (bivariatePolynomialEquiv ℚ f) 0 d hc
      have hfir : AbsolutelyIrreducibleRat f := by
        apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv (AlgebraicClosure ℚ))).mp
        simp only [f, map_sub, map_pow, map_X, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
        rw [← Polynomial.C_pow]
        exact Polynomial.irreducible_X_sub_C (Polynomial.X ^ d : Polynomial (AlgebraicClosure ℚ))
      obtain ⟨hhom, hdeg, hir⟩ := projective_closure_absolute_irreducible f hfdeg hfir
      have hcount : 2 ≤ projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f)) 1 := by
        conv_lhs => rw [← show ({(0 : ℤ), 1} : Finset ℤ).card = 2 by decide]
        refine Finset.card_le_card_of_injOn
          (fun a : ℤ => affineProjectivePoint (rationalPoint fun _ : Fin 2 => a)) ?_ ?_
        · intro a ha
          have ha' : a = 0 ∨ a = 1 := by simpa using ha
          refine mem_projectivePoints.mpr ⟨affineProjectivePoint_integer_height_le _ le_rfl
            (fun _ => by rcases ha' with rfl | rfl <;> norm_num), ?_⟩
          unfold affineProjectivePoint
          rw [mem_projectiveZeroLocus_mk hhom, ← affineChart_eval, affineChart_scaledHomogenize_one]
          rcases ha' with rfl | rfl <;> simp [f, rationalPoint, hd.ne']
        · intro a _ b _ he
          exact Int.cast_injective (congrFun (affineProjectivePoint_injective 2 he) 0)
      refine ⟨scaledHomogenize d 1 f, 1, le_rfl, hhom, hdeg, hir, ?_⟩
      have hcountR : (2 : ℝ) ≤ projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f)) 1 :=
        mod_cast hcount
      have hdR : (d : ℝ) ≤ 3 := mod_cast (by omega : d ≤ 3)
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      nlinarith [mul_nonneg hd0 (show 0 ≤ 3 - (d : ℝ) by linarith)]
  obtain ⟨F, B, hB, hhom, hdeg, habs, hcount⟩ := hplane
  have hir : Irreducible F :=
    mvPolynomial_irreducible_of_field_map (algebraMap ℚ (AlgebraicClosure ℚ)) F habs
  refine ⟨F, B, hB, hhom, hdeg, habs, Ideal.isPrime_span_singleton_of_prime hir.prime,
    principal_plane_hasProjectiveCurveDegree F hhom hir.ne_zero, ?_⟩
  rwa [projectiveIdealZeroLocus_span_singleton F hhom]

end
end CCDN
