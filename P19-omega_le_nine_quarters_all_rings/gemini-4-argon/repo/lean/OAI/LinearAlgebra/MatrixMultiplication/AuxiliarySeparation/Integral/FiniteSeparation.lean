module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic

public section

@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

noncomputable section
open Foundation
open scoped BigOperators Classical Matrix

def phase (g h u v : ℤ) : ℤ := u - v + 2 * (g - h)

namespace Integral

theorem exists_prime_clearing_convolution (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    ∃ D : ℤ, ∃ d : ℕ, (D : ZMod p) ≠ 0 ∧ ∀ k : ℕ,
      Tensor.RankAtMost
        (fun x y z => D ^ k * Tensor.power (convolution (K := ℤ) a b) k x y z)
        ((a + b - 1) ^ k * d * d) := by
  let h := a + b - 1
  let K := GaloisField p (h + 1)
  let : Fintype K := Fintype.ofFinite K
  let pb : PowerBasis (ZMod p) K := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  have hcard : h ≤ Fintype.card K := by
    rw [show Fintype.card K = p ^ (h + 1) by
      simpa only [Nat.card_eq_fintype_card] using GaloisField.card p (h + 1) (by omega)]
    exact (Nat.le_succ h).trans (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt).le
  obtain ⟨nodes⟩ : Nonempty (Fin h ↪ K) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hcard)
  let ψ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective
      (show Function.Surjective ψ from ZMod.intCast_surjective) (minpoly (ZMod p) pb.gen))
    (minpoly.monic pb.isIntegral_gen)
  have hd : f.natDegree = pb.dim := hdeg.trans pb.natDegree_minpoly
  have hroot : f.eval₂ (Int.castRingHom K) pb.gen = 0 := by
    rw [show Int.castRingHom K = (algebraMap (ZMod p) K).comp ψ by ext; simp [ψ],
      ← Polynomial.eval₂_map, hmap]
    exact minpoly.aeval (ZMod p) pb.gen
  let basis := (AdjoinRoot.powerBasisAux' hf).reindex (finCongr hd)
  let φ := AdjoinRoot.lift (Int.castRingHom K) pb.gen hroot
  have hφ (r : ℤ) : φ (algebraMap ℤ (AdjoinRoot f) r) = algebraMap (ZMod p) K (ψ r) := by
    rw [show algebraMap ℤ (AdjoinRoot f) r = (r : AdjoinRoot f) from map_intCast _ r]
    simp [ψ]
  have hb (i : Fin pb.dim) : φ (basis i) = pb.basis i := by
    dsimp [basis]
    rw [Module.Basis.reindex_apply]
    have hbpow (j : Fin f.natDegree) :
        (AdjoinRoot.powerBasisAux' hf) j = AdjoinRoot.root f ^ j.val :=
      (AdjoinRoot.powerBasis' hf).basis_eq_pow ⟨j.val, j.isLt⟩
    rw [hbpow, pb.basis_eq_pow, map_pow]
    simp only [φ, AdjoinRoot.lift_root]
    rfl
  have hrepr (x : AdjoinRoot f) (i : Fin pb.dim) :
      pb.basis.repr (φ x) i = ψ (basis.repr x i) := by
    have he : φ x = pb.basis.equivFun.symm (fun j => ψ (basis.repr x j)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← basis.sum_repr x, map_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [Algebra.smul_def, map_mul, hφ, hb]
    simpa only [Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
      congrArg (fun y => pb.basis.equivFun y i) he
  have hsurj (y : K) : ∃ x : AdjoinRoot f, φ x = y := by
    choose c hc using fun i =>
      (show Function.Surjective ψ from ZMod.intCast_surjective) (pb.basis.repr y i)
    refine ⟨∑ i, c i • basis i, ?_⟩
    rw [map_sum]
    exact (Finset.sum_congr rfl fun i _ => by simp only [Algebra.smul_def, map_mul, hφ, hb, hc]).trans
      (pb.basis.sum_repr y)
  choose v hv using fun i : Fin h => hsurj (nodes i)
  let delta : AdjoinRoot f := (Matrix.vandermonde v).det
  let D : ℤ := (Algebra.leftMulMatrix basis delta).det
  have hdelta : φ delta ≠ 0 := by
    have hmat : (Matrix.vandermonde v).map φ = Matrix.vandermonde (fun i => nodes i) := by
      ext i j; simp [Matrix.vandermonde, hv]
    dsimp [delta]
    rw [RingHom.map_det]
    change ((Matrix.vandermonde v).map φ).det ≠ 0
    rw [hmat]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr nodes.injective
  have hD : (D : ZMod p) ≠ 0 := by
    change ψ (Algebra.leftMulMatrix basis delta).det ≠ 0
    rw [RingHom.map_det]
    have hmat : (Algebra.leftMulMatrix basis delta).map ψ = Algebra.leftMulMatrix pb.basis (φ delta) := by
      ext i j
      simp only [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
      rw [← hrepr, map_mul, hb]
    change ((Algebra.leftMulMatrix basis delta).map ψ).det ≠ 0
    rw [hmat]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      ((isUnit_iff_ne_zero.mpr hdelta).map (Algebra.leftMulMatrix pb.basis).toMonoidHom)).ne_zero
  let cof : AdjoinRoot f :=
    basis.equivFun.symm ((Algebra.leftMulMatrix basis delta).adjugate *ᵥ basis.repr 1)
  have hcof : delta * cof = algebraMap ℤ (AdjoinRoot f) D := by
    apply basis.equivFun.injective
    simp only [Module.Basis.equivFun_apply]
    rw [← Algebra.leftMulMatrix_mulVec_repr]
    have hw : (basis.repr cof : Fin pb.dim → ℤ) =
        (Algebra.leftMulMatrix basis delta).adjugate *ᵥ basis.repr 1 := by
      simpa only [Module.Basis.equivFun_apply, cof] using basis.equivFun.apply_symm_apply _
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]
    rfl
  have hvand : Tensor.RankAtMost
      (fun (i : Fin a) (j : Fin b) (k : Fin h) =>
        delta * (if i.val + j.val = k.val then 1 else 0)) h := by
    refine ⟨fun r i => v r ^ i.val, fun r j => v r ^ j.val,
      fun r k => (Matrix.vandermonde v).adjugate k r, ?_⟩
    funext i j k
    let m : Fin h := ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
    have heq := congrFun (congrFun (Matrix.adjugate_mul (Matrix.vandermonde v)) k) m
    dsimp [delta]
    simpa [Tensor.rankOne, ← pow_add, Fin.ext_iff, Matrix.mul_apply,
      Matrix.vandermonde, Matrix.one_apply, mul_comm, eq_comm] using heq.symm
  have hr : Tensor.RankAtMost
      (fun i j l => algebraMap ℤ (AdjoinRoot f) (D * convolution (K := ℤ) a b i j l)) h := by
    convert hvand.scale cof using 1
    funext i j k
    simp only [convolution, map_mul, apply_ite, map_one, map_zero, ← hcof]
    split_ifs <;> ring
  refine ⟨D, pb.dim, hD, fun k => ?_⟩
  have hk := hr.descend_finite_basis_powers basis (monicQuotientProjection hf)
    (monicQuotientProjection_one hf (hd.symm ▸ pb.dim_pos)) k
  convert hk using 1
  · funext x y z
    simp only [Tensor.power, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · simp only [Fintype.card_fin, h]

theorem _root_.OAI.MatrixMultiplication.AuxiliarySeparation.Character.value_convolution_le_int
    (χ : Character ℤ) (a b : ℕ) :
    χ.value (convolution (K := ℤ) a b) ≤ ((a + b - 1 : ℕ) : ℝ) := by
  let T := convolution (K := ℤ) a b
  let h := a + b - 1
  let S : Set ℤ := {D | ∃ d : ℕ, ∀ k : ℕ,
    Tensor.RankAtMost (fun x y z => D ^ k * Tensor.power T k x y z) (h ^ k * d * d)}
  have hprime (p : ℕ) (hp : p.Prime) : ∃ D ∈ S, ¬ (p : ℤ) ∣ D := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨D, d, hD, hscheme⟩ := exists_prime_clearing_convolution p a b
    exact ⟨D, ⟨d, hscheme⟩, fun hdiv => hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hdiv)⟩
  let g := Submodule.IsPrincipal.generator (Ideal.span S)
  have hu : IsUnit g := by
    by_contra hunit
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd fun hg => hunit (Int.isUnit_iff_natAbs_eq.mpr hg)
    obtain ⟨D, hDS, hpD⟩ := hprime p hp
    exact hpD ((Int.natCast_dvd.mpr hpg).trans
      ((Submodule.IsPrincipal.mem_iff_generator_dvd (Ideal.span S)).mp (Ideal.subset_span hDS)))
  have htop : Ideal.span S = ⊤ := by
    rw [← Ideal.span_singleton_generator (Ideal.span S)]
    exact Ideal.span_singleton_eq_top.mpr hu
  obtain ⟨t, htS, ht⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp htop)
  rw [← show Set.range (fun i : t => (i : ℤ)) = (↑t : Set ℤ) by ext; simp] at ht
  obtain ⟨u, hu'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp ht
  choose d hscheme using fun i : t => htS i.property
  apply le_of_pow_le_const_mul_pow (C := ((∑ j : t, d j * d j : ℕ) : ℝ)) (Nat.cast_nonneg _)
  intro k
  have hs : Ideal.span (Set.range fun j : t => (j : ℤ)) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr ((Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨u, hu'⟩)
  have hp := Ideal.span_pow_eq_top (Set.range fun j : t => (j : ℤ)) hs k
  rw [show ((fun x : ℤ => x ^ k) '' Set.range fun j : t => (j : ℤ)) =
      Set.range (fun j : t => (j : ℤ) ^ k) by ext; simp] at hp
  obtain ⟨v, hv⟩ : ∃ v : t → ℤ, ∑ j, v j * (j : ℤ) ^ k = 1 := by
    simpa only [smul_eq_mul] using
      (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((Ideal.eq_top_iff_one _).mp hp)
  choose aa bb cc hcomb using fun j : t => (hscheme j k).scale (v j)
  have heq : Tensor.power T k = fun x y z =>
      ∑ q : Σ j : t, Fin (h ^ k * d j * d j), Tensor.rankOne (aa q.1 q.2) (bb q.1 q.2) (cc q.1 q.2) x y z := by
    funext x y z
    simp only [Fintype.sum_sigma]
    calc
      Tensor.power T k x y z = (∑ j : t, v j * (j : ℤ) ^ k) * Tensor.power T k x y z := by rw [hv, one_mul]
      _ = ∑ j : t, v j * ((j : ℤ) ^ k * Tensor.power T k x y z) := by simp [Finset.sum_mul, mul_assoc]
      _ = _ := Finset.sum_congr rfl fun j _ => congrFun (congrFun (congrFun (hcomb j) x) y) z
  have hrank : Tensor.RankAtMost (Tensor.power T k) (h ^ k * ∑ j : t, d j * d j) := by
    rw [heq, Finset.mul_sum]
    simpa only [Fintype.card_sigma, Fintype.card_fin, Nat.mul_assoc] using
      Tensor.rankAtMost_sum_rankOne
        (fun q : Σ j : t, Fin (h ^ k * d j * d j) => aa q.1 q.2)
        (fun q : Σ j : t, Fin (h ^ k * d j * d j) => bb q.1 q.2)
        (fun q : Σ j : t, Fin (h ^ k * d j * d j) => cc q.1 q.2)
  simpa only [T, h, χ.value_power, Nat.cast_mul, Nat.cast_pow, mul_comm] using χ.value_le_rank hrank

abbrev CyclotomicAlgebra (L : ℕ) := AdjoinRoot (Polynomial.cyclotomic L ℤ)

instance cyclotomicAlgebra_isDomain (L : ℕ) [NeZero L] :
    IsDomain (CyclotomicAlgebra L) :=
  AdjoinRoot.isDomain_of_prime (Polynomial.cyclotomic.irreducible (NeZero.pos L)).prime

theorem cyclotomic_natDegree_pos (L : ℕ) [NeZero L] :
    0 < (Polynomial.cyclotomic L ℤ).natDegree := by
  rw [Polynomial.natDegree_cyclotomic]
  exact Nat.totient_pos.mpr (NeZero.pos L)

instance cyclotomicAlgebra_charZero (L : ℕ) [NeZero L] :
    CharZero (CyclotomicAlgebra L) :=
  charZero_of_injective_algebraMap (AdjoinRoot.of.injective_of_monic_of_degree_pos
    (Polynomial.cyclotomic.monic L ℤ)
    (Polynomial.natDegree_pos_iff_degree_pos.mp (cyclotomic_natDegree_pos L)))

theorem cyclotomic_root_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (AdjoinRoot.root (Polynomial.cyclotomic L ℤ)) L := by
  apply (Polynomial.isRoot_cyclotomic_iff_charZero (NeZero.pos L)).mp
  rw [← Polynomial.map_cyclotomic_int L (CyclotomicAlgebra L)]
  exact AdjoinRoot.isRoot_root _

section Weights
variable {E : Type*} [CommRing E]

def leftDegree (g : ℤ) : ℕ := (g ^ 2).toNat
def middleDegree (M : ℕ) (h u : ℤ) : ℕ := ((M : ℤ) ^ 2 + h * u - h ^ 2).toNat
def rightDegree (M : ℕ) (h v : ℤ) : ℕ := ((M : ℤ) ^ 2 - h * v).toNat

theorem degree_sum_cast {M : ℕ} {g h u v : ℤ}
    (hh : 1 ≤ h ∧ h ≤ M) (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    ((leftDegree g + middleDegree M h u + rightDegree M h v : ℕ) : ℤ) =
      2 * (M : ℤ) ^ 2 + (g - h) ^ 2 + h * phase g h u v := by
  have h1 : (leftDegree g : ℤ) = g ^ 2 := Int.toNat_of_nonneg (sq_nonneg g)
  have h2 : (middleDegree M h u : ℤ) = (M : ℤ) ^ 2 + h * u - h ^ 2 := by
    apply Int.toNat_of_nonneg
    have hs : h ^ 2 ≤ (M : ℤ) ^ 2 := sq_le_sq₀ (by omega) (by omega) |>.mpr hh.2
    have hprod : 0 ≤ h * u := mul_nonneg (by omega) (by omega)
    nlinarith
  have h3 : (rightDegree M h v : ℤ) = (M : ℤ) ^ 2 - h * v := by
    apply Int.toNat_of_nonneg
    have hprod : h * v ≤ (M : ℤ) * M := mul_le_mul hh.2 hv.2 (by omega) (by omega)
    nlinarith
  push_cast
  rw [h1, h2, h3]
  unfold phase; ring

variable [IsDomain E]

theorem sum_unit_zpow_primitive_root_of_abs_lt {ζ : Eˣ} {L : ℕ} {e : ℤ}
    (hζ : IsPrimitiveRoot ζ L) (he : |e| < (L : ℤ)) :
    (∑ r ∈ Finset.range L, (↑(ζ ^ ((r : ℤ) * e)) : E)) =
      if e = 0 then (L : E) else 0 := by
  have hpow : (↑(ζ ^ e) : E) ^ L = 1 := by
    have h : (ζ ^ e) ^ L = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h
  have hterm (r : ℕ) : (↑(ζ ^ ((r : ℤ) * e)) : E) = (↑(ζ ^ e) : E) ^ r := by
    have h : ζ ^ ((r : ℤ) * e) = (ζ ^ e) ^ r := by rw [← zpow_natCast, ← zpow_mul, mul_comm]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h
  simp_rw [hterm]
  have hsum : (∑ r ∈ Finset.range L, (↑(ζ ^ e) : E) ^ r) =
      if (↑(ζ ^ e) : E) = 1 then (L : E) else 0 := by
    split_ifs with h
    · simp [h]
    · have hs : (1 - (↑(ζ ^ e) : E)) * ∑ r ∈ Finset.range L, (↑(ζ ^ e) : E) ^ r = 0 := by
        rw [mul_neg_geom_sum, hpow, sub_self]
      exact (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr (Ne.symm h))
  rw [hsum]
  have hone : (↑(ζ ^ e) : E) = 1 ↔ e = 0 := by
    rw [← Units.val_one, Units.val_inj, hζ.zpow_eq_one_iff_dvd]
    exact ⟨fun hd => abs_eq_zero.mp (Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg e) he
      ((dvd_abs (L : ℤ) e).mpr hd)), fun h => h ▸ dvd_zero _⟩
  simp only [hone]

end Weights

section Polynomial
variable {E : Type*} [CommRing E]
variable {M L : ℕ} {X Y Z : Type*}

def leftPolynomialMap (ζ : Eˣ) : (X × Fin M) → (Fin L × X) → Polynomial E :=
  fun x r => if r.2 = x.1 then
    Polynomial.monomial (leftDegree (sectorNumber x.2))
      (↑(ζ ^ ((r.1.val : ℤ) * (2 * sectorNumber x.2))) : E) else 0

def middlePolynomialMap (ζ : Eˣ) :
    ((Fin M × Y) × Fin M) → (Fin L × (Fin M × Y)) → Polynomial E :=
  fun y r => if r.2 = y.1 then
    Polynomial.monomial (middleDegree M (sectorNumber y.1.1) (sectorNumber y.2))
      (↑(ζ ^ ((r.1.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1))) : E) else 0

def rightPolynomialMap (ζ : Eˣ) :
    ((Fin M × Z) × Fin M) → (Fin L × (Fin M × Z)) → Polynomial E :=
  fun z r => if r.2 = z.1 then
    Polynomial.monomial (rightDegree M (sectorNumber z.1.1) (sectorNumber z.2))
      (↑(ζ ^ ((r.1.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) : E) else 0

theorem integralSeparationPolynomial_restrict [IsDomain E] [Fintype X] [Fintype Y] [Fintype Z]
    {ζ : Eˣ} (hL : 5 * M ≤ L) (hζ : IsPrimitiveRoot ζ L)
    (B : Fin M → Tensor E X Y Z) (x : X × Fin M)
    (y : (Fin M × Y) × Fin M) (z : (Fin M × Z) × Fin M) :
    Tensor.restrict (leftPolynomialMap ζ) (middlePolynomialMap ζ) (rightPolynomialMap ζ)
      (fun x y z => Polynomial.C (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) x y z))
      x y z =
      if y.1.1 = z.1.1 ∧ phase (sectorNumber x.2) (sectorNumber y.1.1)
          (sectorNumber y.2) (sectorNumber z.2) = 0 then
        Polynomial.monomial
          (leftDegree (sectorNumber x.2) + middleDegree M (sectorNumber y.1.1) (sectorNumber y.2) +
            rightDegree M (sectorNumber y.1.1) (sectorNumber z.2))
          ((L : E) * B y.1.1 x.1 y.1.2 z.1.2)
      else 0 := by
  have hC : (fun x y z => Polynomial.C
      (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) x y z)) =
      Tensor.directSum (fun _ : Fin L => fun x y z => Polynomial.C (sharedFirstTensor B x y z)) := by
    funext x y z; simp only [Tensor.directSum]; split_ifs <;> simp
  rw [hC]
  unfold leftPolynomialMap middlePolynomialMap rightPolynomialMap
  rw [restrict_constantCopies_delta (R := Fin L)
    (fun x y z => Polynomial.C (sharedFirstTensor B x y z)) Prod.fst Prod.fst Prod.fst
    (fun x r => Polynomial.monomial (leftDegree (sectorNumber x.2))
      (↑(ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2))) : E))
    (fun y r => Polynomial.monomial (middleDegree M (sectorNumber y.1.1) (sectorNumber y.2))
      (↑(ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1))) : E))
    (fun z r => Polynomial.monomial (rightDegree M (sectorNumber z.1.1) (sectorNumber z.2))
      (↑(ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber z.1.1))) : E)) x y z]
  by_cases hyz : y.1.1 = z.1.1
  · simp only [sharedFirstTensor, hyz, ↓reduceIte, true_and]
    rw [← hyz]
    have hterm (r : Fin L) :
        Polynomial.monomial (leftDegree (sectorNumber x.2))
          (↑(ζ ^ ((r.val : ℤ) * (2 * sectorNumber x.2))) : E) *
        Polynomial.monomial (middleDegree M (sectorNumber y.1.1) (sectorNumber y.2))
          (↑(ζ ^ ((r.val : ℤ) * (sectorNumber y.2 - sectorNumber y.1.1))) : E) *
        Polynomial.monomial (rightDegree M (sectorNumber y.1.1) (sectorNumber z.2))
          (↑(ζ ^ ((r.val : ℤ) * (-sectorNumber z.2 - sectorNumber y.1.1))) : E) =
        Polynomial.monomial
          (leftDegree (sectorNumber x.2) + middleDegree M (sectorNumber y.1.1) (sectorNumber y.2) +
            rightDegree M (sectorNumber y.1.1) (sectorNumber z.2))
          (↑(ζ ^ ((r.val : ℤ) * phase (sectorNumber x.2) (sectorNumber y.1.1)
            (sectorNumber y.2) (sectorNumber z.2))) : E) := by
      rw [Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial]
      congr 1
      rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add]
      congr 2; unfold phase; ring
    simp_rw [hterm]
    rw [← map_sum, Polynomial.monomial_mul_C, Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      (↑(ζ ^ ((r : ℤ) * phase (sectorNumber x.2) (sectorNumber y.1.1)
        (sectorNumber y.2) (sectorNumber z.2))) : E))]
    have he : |phase (sectorNumber x.2) (sectorNumber y.1.1)
        (sectorNumber y.2) (sectorNumber z.2)| < (L : ℤ) := by
      have := sectorNumber_bounds x.2
      have := sectorNumber_bounds y.1.1
      have := sectorNumber_bounds y.2
      have := sectorNumber_bounds z.2
      rw [abs_lt]; unfold phase; constructor <;> omega
    rw [sum_unit_zpow_primitive_root_of_abs_lt hζ he]
    split_ifs <;> simp
  · simp [sharedFirstTensor, hyz]

def mapDegreeBound {A B : Type*} [Fintype A] [Fintype B]
    (P : A → B → Polynomial E) : ℕ :=
  Finset.univ.sup (fun q : A × B => (P q.1 q.2).natDegree)

theorem degree_le_mapDegreeBound {A B : Type*} [Fintype A] [Fintype B]
    (P : A → B → Polynomial E) (a : A) (b : B) :
    (P a b).degree ≤ mapDegreeBound P :=
  Polynomial.degree_le_of_natDegree_le
    (Finset.le_sup (f := fun q : A × B => (P q.1 q.2).natDegree) (Finset.mem_univ (a, b)))

def integralSeparationDegeneration [IsDomain E] [Fintype X] [Fintype Y] [Fintype Z]
    {ζ : Eˣ} (_hM : 0 < M) (hL : 5 * M ≤ L) (hζ : IsPrimitiveRoot ζ L)
    (B : Fin M → Tensor E X Y Z) :
    Tensor.PolynomialRestrictionDegeneration
      (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B))
      (fun x y z => (L : E) * separationTarget B x y z) (2 * M ^ 2)
      (mapDegreeBound (leftPolynomialMap ζ : (X × Fin M) → (Fin L × X) → Polynomial E))
      (mapDegreeBound (middlePolynomialMap ζ :
        ((Fin M × Y) × Fin M) → (Fin L × (Fin M × Y)) → Polynomial E))
      (mapDegreeBound (rightPolynomialMap ζ :
        ((Fin M × Z) × Fin M) → (Fin L × (Fin M × Z)) → Polynomial E)) where
  leftMap := leftPolynomialMap ζ
  middleMap := middlePolynomialMap ζ
  rightMap := rightPolynomialMap ζ
  left_degree := degree_le_mapDegreeBound _
  middle_degree := degree_le_mapDegreeBound _
  right_degree := degree_le_mapDegreeBound _
  vanishes x y z j hj := by
    rw [integralSeparationPolynomial_restrict hL hζ]
    split_ifs with h
    · apply Polynomial.coeff_monomial_of_ne
      have hc := degree_sum_cast (sectorNumber_bounds y.1.1) (sectorNumber_bounds y.2)
        (sectorNumber_bounds z.2) (g := sectorNumber x.2)
      have hsq : 0 ≤ (sectorNumber x.2 - sectorNumber y.1.1) ^ 2 := sq_nonneg _
      have hge : 2 * M ^ 2 ≤ leftDegree (sectorNumber x.2) +
          middleDegree M (sectorNumber y.1.1) (sectorNumber y.2) +
          rightDegree M (sectorNumber y.1.1) (sectorNumber z.2) := by
        exact_mod_cast (show 2 * (M : ℤ) ^ 2 ≤
          ((leftDegree (sectorNumber x.2) + middleDegree M (sectorNumber y.1.1) (sectorNumber y.2) +
            rightDegree M (sectorNumber y.1.1) (sectorNumber z.2) : ℕ) : ℤ) by
          rw [hc, h.2]; omega)
      omega
    · simp
  leading x y z := by
    rw [integralSeparationPolynomial_restrict hL hζ]
    split_ifs with h
    · have hc := degree_sum_cast (sectorNumber_bounds y.1.1) (sectorNumber_bounds y.2)
        (sectorNumber_bounds z.2) (g := sectorNumber x.2)
      have hcast : ((2 * M ^ 2 : ℕ) : ℤ) = 2 * (M : ℤ) ^ 2 := by norm_cast
      have hp := h.2
      rw [hp, mul_zero, add_zero] at hc
      have heq : leftDegree (sectorNumber x.2) +
          middleDegree M (sectorNumber y.1.1) (sectorNumber y.2) +
          rightDegree M (sectorNumber y.1.1) (sectorNumber z.2) = 2 * M ^ 2 ↔
          x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 := by
        rw [and_left_comm (a := x.2 = y.1.1), and_iff_right h.1,
          show leftDegree (sectorNumber x.2) +
            middleDegree M (sectorNumber y.1.1) (sectorNumber y.2) +
            rightDegree M (sectorNumber y.1.1) (sectorNumber z.2) = 2 * M ^ 2 ↔
            (sectorNumber x.2 - sectorNumber y.1.1) ^ 2 = 0 by omega,
          sq_eq_zero_iff, ← sectorNumber_injective.eq_iff (a := x.2),
          ← sectorNumber_injective.eq_iff (a := y.2)]
        unfold phase at hp; omega
      simp only [Polynomial.coeff_monomial, heq, separationTarget, mul_ite, mul_zero]
    · have hn : ¬ (x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2) := by
        rintro ⟨h1, h2, h3⟩; exact h ⟨h2, by simp [phase, h1, h3]⟩
      simp [separationTarget, hn]

end Polynomial

abbrev ExtractionIndex (Lx Ly n : ℕ) := Fin (Lx * n + 1) × Fin (Ly * n + 1)

def descentSource {X Y Z ι : Type} [DecidableEq ι]
    (T : Tensor ℤ X Y Z) (Lx Ly n : ℕ) :
    Tensor ℤ ((ι × ι) × (ExtractionIndex Lx Ly n × (Fin n → X)))
      ((ι × ι) × (ExtractionIndex Lx Ly n × (Fin n → Y)))
      ((ι × ι) × (ExtractionIndex Lx Ly n × (Fin n → Z))) :=
  Tensor.directSum (fun _ : ι × ι =>
    Tensor.directSum (fun _ : ExtractionIndex Lx Ly n => Tensor.power T n))

variable {M L : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

abbrev CyclotomicIndex (L : ℕ) := Fin (Polynomial.cyclotomic L ℤ).natDegree

theorem separation_scalar_power_restrictions (hM : 0 < M) (hL : 5 * M ≤ L)
    (B : Fin M → Tensor ℤ X Y Z) :
    ∃ Lx Ly : ℕ, ∀ n : ℕ,
      ∃ (A : (Fin n → X × Fin M) →
          ((CyclotomicIndex L × CyclotomicIndex L) ×
            (ExtractionIndex Lx Ly n × (Fin n → Fin L × X))) → ℤ)
        (C : (Fin n → (Fin M × Y) × Fin M) →
          ((CyclotomicIndex L × CyclotomicIndex L) ×
            (ExtractionIndex Lx Ly n × (Fin n → Fin L × (Fin M × Y)))) → ℤ)
        (D : (Fin n → (Fin M × Z) × Fin M) →
          ((CyclotomicIndex L × CyclotomicIndex L) ×
            (ExtractionIndex Lx Ly n × (Fin n → Fin L × (Fin M × Z)))) → ℤ),
        Tensor.restrict A C D
          (descentSource (ι := CyclotomicIndex L)
            (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) Lx Ly n) =
          fun x y z => (L : ℤ) ^ n * Tensor.power (separationTarget B) n x y z := by
  let : NeZero L := ⟨by omega⟩
  let E := CyclotomicAlgebra L
  let BE : Fin M → Tensor E X Y Z := fun i x y z => algebraMap ℤ E (B i x y z)
  let ζ : Eˣ := ((cyclotomic_root_primitive L).isUnit (NeZero.ne L)).unit
  have hζ : IsPrimitiveRoot ζ L := (cyclotomic_root_primitive L).isUnit_unit (NeZero.ne L)
  let D := integralSeparationDegeneration hM hL hζ BE
  let Lx := mapDegreeBound (leftPolynomialMap ζ : (X × Fin M) → (Fin L × X) → Polynomial E)
  let Ly := mapDegreeBound (middlePolynomialMap ζ :
    ((Fin M × Y) × Fin M) → (Fin L × (Fin M × Y)) → Polynomial E)
  let Lz := mapDegreeBound (rightPolynomialMap ζ :
    ((Fin M × Z) × Fin M) → (Fin L × (Fin M × Z)) → Polynomial E)
  have hs : Tensor.directSum (fun _ : Fin L => sharedFirstTensor BE) =
      fun x y z => algebraMap ℤ E (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) x y z) := by
    funext x y z; simp only [Tensor.directSum, sharedFirstTensor, BE]; split_ifs <;> simp
  have ht : (fun x y z => (L : E) * separationTarget BE x y z) =
      fun x y z => algebraMap ℤ E ((L : ℤ) * separationTarget B x y z) := by
    funext x y z; simp only [separationTarget, BE]; split_ifs <;> simp
  have D' : Tensor.PolynomialRestrictionDegeneration
      (fun x y z => algebraMap ℤ E (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) x y z))
      (fun x y z => algebraMap ℤ E ((L : ℤ) * separationTarget B x y z))
      (2 * M ^ 2) Lx Ly Lz := by
    simpa only [hs, ht] using D
  refine ⟨Lx, Ly, fun n => ?_⟩
  let T := Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)
  let S := separationTarget B
  let Tn := Tensor.directSum (fun _ : ExtractionIndex Lx Ly n => Tensor.power T n)
  let Sn := fun x y z => (L : ℤ) ^ n * Tensor.power S n x y z
  let A := fun x (q : ExtractionIndex Lx Ly n × (Fin n → Fin L × X)) =>
    ((D'.power n).leftMap x q.2).coeff q.1.1
  let B' := fun y (q : ExtractionIndex Lx Ly n × (Fin n → Fin L × (Fin M × Y))) =>
    ((D'.power n).middleMap y q.2).coeff q.1.2
  let C := fun z (q : ExtractionIndex Lx Ly n × (Fin n → Fin L × (Fin M × Z))) =>
    shiftedCoeff ((D'.power n).rightMap z q.2) (2 * M ^ 2 * n) (q.1.1.val + q.1.2.val)
  have hsource : (fun x y z => algebraMap ℤ E (Tn x y z)) =
      Tensor.directSum (fun _ : ExtractionIndex Lx Ly n =>
        Tensor.power (fun x y z => algebraMap ℤ E (T x y z)) n) := by
    funext x y z; simp only [Tn, Tensor.directSum, Tensor.power]; split_ifs <;> simp [map_prod]
  have htarget : Tensor.power (fun x y z => algebraMap ℤ E ((L : ℤ) * S x y z)) n =
      fun x y z => algebraMap ℤ E (Sn x y z) := by
    funext x y z; simp [Tensor.power, Sn, map_mul, map_pow, map_prod, Finset.prod_mul_distrib]
  have heq : Tensor.restrict A B' C (fun x y z => algebraMap ℤ E (Tn x y z)) =
      fun x y z => algebraMap ℤ E (Sn x y z) := by
    rw [hsource, ← htarget]; exact (D'.power n).extract.symm
  exact ⟨_, _, _, (descend_restriction_basis (R := ℤ) (E := E) (ι := CyclotomicIndex L)
    (AdjoinRoot.powerBasisAux' (Polynomial.cyclotomic.monic L ℤ))
    (monicQuotientProjection (Polynomial.cyclotomic.monic L ℤ))
    (monicQuotientProjection_one (Polynomial.cyclotomic.monic L ℤ) (cyclotomic_natDegree_pos L))
    Sn Tn A B' C heq).symm⟩

theorem finiteSeparation_bound_int (χ : Character ℤ) (hM : 0 < M)
    (B : Fin M → Tensor ℤ X Y Z) :
    (∑ i, χ.value (B i)) * (M : ℝ) ^ χ.pX ≤
      6 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  let L := 5 * M
  obtain ⟨Ax, Ay, hA⟩ := separation_scalar_power_restrictions hM (L := L) le_rfl B
  obtain ⟨Bx, By, hB⟩ := separation_scalar_power_restrictions hM (L := L + 1) (by omega) B
  let cA : ℝ := (Fintype.card (CyclotomicIndex L) : ℝ) ^ 2
  let cB : ℝ := (Fintype.card (CyclotomicIndex (L + 1)) : ℝ) ^ 2
  have hbound : χ.value (separationTarget B) ≤ (L + 1 : ℝ) * χ.value (sharedFirstTensor B) := by
    apply χ.value_le_mul_of_power_comparisons
      (sharedFirstTensor B) (separationTarget B) (Ax + Bx) (Ay + By) (cA + cB) (L + 1) (by positivity)
    intro n
    let SA := descentSource (ι := CyclotomicIndex L)
      (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) Ax Ay n
    let SB := descentSource (ι := CyclotomicIndex (L + 1))
      (Tensor.directSum (fun _ : Fin (L + 1) => sharedFirstTensor B)) Bx By n
    have hcoprime : IsCoprime (L : ℤ) ((L : ℤ) + 1) := ⟨-1, 1, by ring⟩
    have hc := χ.value_le_add_of_coprime_scaled_restrictions
      (Tensor.power (separationTarget B) n) SA SB hcoprime n
      (hA n) (by simpa only [Nat.cast_add, Nat.cast_one] using hB n)
    have hv : 0 ≤ χ.value (sharedFirstTensor B) := χ.nonneg _
    have hdesc {L' Lx Ly : ℕ} (hL' : L' ≤ L + 1) (hLx : (Lx : ℝ) ≤ Ax + Bx) (hLy : (Ly : ℝ) ≤ Ay + By) :
        χ.value (descentSource (ι := CyclotomicIndex L')
          (Tensor.directSum (fun _ : Fin L' => sharedFirstTensor B)) Lx Ly n) ≤
          (Fintype.card (CyclotomicIndex L') : ℝ) ^ 2 * ((n : ℝ) * (Ax + Bx) + 1) *
            (n * (Ay + By) + 1) * (L + 1 : ℝ) ^ n * χ.value (sharedFirstTensor B) ^ n := by
      have hval : χ.value (descentSource (ι := CyclotomicIndex L')
          (Tensor.directSum (fun _ : Fin L' => sharedFirstTensor B)) Lx Ly n) =
          (Fintype.card (CyclotomicIndex L') : ℝ) ^ 2 * ((n : ℝ) * Lx + 1) *
            (n * Ly + 1) * (L' : ℝ) ^ n * χ.value (sharedFirstTensor B) ^ n := by
        simp only [descentSource, χ.map_directSum, χ.value_power, mul_pow,
          Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      rw [hval]
      simp only [mul_assoc]
      have hLreal : (L' : ℝ) ≤ L + 1 := by exact_mod_cast hL'
      gcongr
    have ha := hdesc (Lx := Ax) (Ly := Ay) (show L ≤ L + 1 by omega)
      (by linarith [Nat.cast_nonneg (α := ℝ) Bx])
      (by linarith [Nat.cast_nonneg (α := ℝ) By])
    have hb := hdesc (Lx := Bx) (Ly := By) le_rfl
      (by linarith [Nat.cast_nonneg (α := ℝ) Ax])
      (by linarith [Nat.cast_nonneg (α := ℝ) Ay])
    have hsum := hc.trans (add_le_add ha hb)
    simp only [χ.value_power, cA, cB] at hsum ⊢
    convert hsum using 1; ring
  have hL : (L + 1 : ℝ) ≤ 6 * (M : ℝ) := by
    dsimp [L]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have h := hbound.trans (mul_le_mul_of_nonneg_right hL (χ.nonneg _))
  rw [separationTarget_eq_directSum, χ.value_reindex, χ.map_directSum] at h
  simpa only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul] using h

end Integral
end
end OAI.MatrixMultiplication.AuxiliarySeparation
