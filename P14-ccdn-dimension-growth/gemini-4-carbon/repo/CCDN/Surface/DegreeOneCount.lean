module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Algebra.AffineLineLeading
import CCDN.Algebra.BinaryHomogeneousIrreducibility
import CCDN.Algebra.HomogeneousTranslation
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomial
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Noether.ShearNormalization
import CCDN.Noether.UniversalPlaneSpecialization
import CCDN.Plane.Bezout
import CCDN.Plane.DegreeOneAffineLine
import CCDN.Plane.FiniteFieldBadPlanes
import CCDN.Plane.ProjectivePlaneLinearCount
import CCDN.Surface.CurveComponents
import CCDN.Surface.TopFormBadPrimes
import CCDN.Surface.TopFormIrreducibility

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma eval_affineLinePolynomial {K σ : Type*} [Field K]
    (a v : σ → K) (f : MvPolynomial σ K) (t : K) :
    (affineLinePolynomial a v f).eval t = eval (a + t • v) f := by
  have he : (Polynomial.evalRingHom t).comp (affineLinePolynomial a v) = eval (a + t • v) :=
    MvPolynomial.ringHom_ext (fun _ => by simp [affineLinePolynomial])
      fun _ => by simp [affineLinePolynomial]; ring
  exact RingHom.congr_fun he f

private def directionalDerivative {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, C (v i) * pderiv i f

private lemma pderiv_homogeneousComponent {R σ : Type*} [CommRing R]
    (i : σ) (f : MvPolynomial σ R) {d : ℕ} (hd : 0 < d) :
    pderiv i (homogeneousComponent d f) = homogeneousComponent (d - 1) (pderiv i f) := by
  classical
  ext m
  rw [coeff_pderiv, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_pderiv]
  have he : (m + Finsupp.single i 1).degree = m.degree + 1 := by
    change (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]; simp
  rw [he]
  by_cases hm : m.degree = d - 1
  · simp [hm, Nat.sub_add_cancel hd]
  · simp [hm, show m.degree + 1 ≠ d by omega]

private theorem surface_directionalDerivative_ne_zero
    (f : MvPolynomial (Fin 3) ℤ) (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree)
    (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    directionalDerivative v (map (Int.castRingHom ℚ) f) ≠ 0 := by
  classical
  intro hz
  let K := AlgebraicClosure ℚ
  let φ := algebraMap ℚ K
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  let vK : Fin 3 → K := fun i => φ (v i)
  have hjK : vK j ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hj
  let d := f.totalDegree
  let H₀ := map φ (homogeneousComponent d (map (Int.castRingHom ℚ) f))
  have hH0_hom : H₀.IsHomogeneous d := by
    dsimp [H₀]; rw [map_homogeneousComponent]; exact homogeneousComponent_isHomogeneous _ _
  have hH0_ir : Irreducible H₀ := by
    dsimp [H₀, d]; rw [← map_homogeneousComponent, map_map]
    convert hir using 1; congr 1
  have hdH0 : directionalDerivative vK H₀ = 0 := by
    dsimp [H₀, vK]
    have hmap : directionalDerivative (fun i => φ (v i)) (map φ (homogeneousComponent d (map (Int.castRingHom ℚ) f))) =
        map φ (directionalDerivative v (homogeneousComponent d (map (Int.castRingHom ℚ) f))) := by
      simp [directionalDerivative, pderiv_map]
    have hcomp : directionalDerivative v (homogeneousComponent d (map (Int.castRingHom ℚ) f)) =
        homogeneousComponent (d - 1) (directionalDerivative v (map (Int.castRingHom ℚ) f)) := by
      simp only [directionalDerivative, map_sum, homogeneousComponent_C_mul,
        pderiv_homogeneousComponent _ _ (by omega : 0 < d)]
    rw [hmap, hcomp, hz, map_zero, map_zero]
  let esw : Fin 3 ≃ Fin 3 := Equiv.swap j 0
  let w : Fin 3 → K := fun i => vK (esw.symm i)
  have hw0 : w 0 ≠ 0 := by simpa [w, esw] using hjK
  let F := rename esw H₀
  have hF_hom : F.IsHomogeneous d := hH0_hom.rename_isHomogeneous
  have hF_ir : Irreducible F :=
    (MulEquiv.irreducible_iff (f := (renameEquiv K esw).toMulEquiv)).mpr hH0_ir
  have hdF : directionalDerivative w F = 0 := by
    have hren : directionalDerivative w F = rename esw (directionalDerivative vK H₀) := by
      dsimp [directionalDerivative, w, F]
      rw [← esw.sum_comp]
      simp only [Equiv.symm_apply_apply, pderiv_rename esw.injective, map_sum, map_mul, rename_C]
    rw [hren, hdH0, map_zero]
  let a : Fin 2 → K := fun i => w i.succ / w 0
  let e := homogeneousTranslation K a
  let G := e F
  have hG_hom : G.IsHomogeneous d := homogeneousTranslation_homogeneous a hF_hom
  have hG_ir : Irreducible G := (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr hF_ir
  have hX (i : Fin 3) : C (w 0) * pderiv 0 (e (X i)) = C (w i) := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [e, homogeneousTranslation, homogeneousTranslationHom]
    · simp only [e, a, homogeneousTranslation, homogeneousTranslationHom, AlgEquiv.ofAlgHom_apply,
        aeval_X, Fin.cons_succ, map_add, pderiv_mul, pderiv_X_of_ne (Fin.succ_ne_zero k), pderiv_C,
        zero_mul, pderiv_X_self, mul_one, zero_add]
      rw [← C_mul]; congr 1; exact mul_div_cancel₀ _ hw0
  have hp0G : C (w 0) * pderiv 0 G = e (directionalDerivative w F) := by
    have hchain := MvPolynomial.pderiv_algHom e.toAlgHom F 0
    change pderiv 0 G = ∑ i, e (pderiv i F) * pderiv 0 (e (X i)) at hchain
    rw [hchain, Finset.mul_sum]
    simp only [directionalDerivative, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hC : e (C (w i)) = C (w i) := e.commutes _
    rw [hC, show C (w 0) * (e (pderiv i F) * pderiv 0 (e (X i))) =
      (C (w 0) * pderiv 0 (e (X i))) * e (pderiv i F) by ring, hX]
  rw [hdF, map_zero] at hp0G
  have hp0 : pderiv 0 G = 0 := (mul_eq_zero.mp hp0G).resolve_left (by simpa using hw0)
  have hv0 := notMem_vars_of_pderiv_eq_zero hp0 fun n hn _ => Nat.cast_ne_zero.mpr hn.ne'
  have hs : ↑G.vars ⊆ Set.range (Fin.succ : Fin 2 → Fin 3) := fun i =>
    Fin.cases (fun hi => (hv0 hi).elim) (fun k _ => ⟨k, rfl⟩) i
  obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range G Fin.succ (Fin.succ_injective 2) hs
  have hgh : g.IsHomogeneous d :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective 2)).mp (hg ▸ hG_hom)
  have he_ret (p : MvPolynomial (Fin 2) K) : eval₂Hom C (Fin.cons 0 X) (rename Fin.succ p) = p := by
    rw [eval₂Hom_rename, show Fin.cons (0 : MvPolynomial (Fin 2) K) X ∘ Fin.succ = X by funext; simp]
    simp
  have hgi : Irreducible g := by
    have hrg : Irreducible (rename Fin.succ g) := hg ▸ hG_ir
    refine ⟨fun hu => hrg.not_isUnit (hu.map (rename Fin.succ)), fun p q hpq => ?_⟩
    exact (hrg.isUnit_or_isUnit (by rw [hpq, map_mul])).imp
      (fun hp => by simpa only [he_ret] using hp.map (eval₂Hom C (Fin.cons 0 X)))
      (fun hq => by simpa only [he_ret] using hq.map (eval₂Hom C (Fin.cons 0 X)))
  have := binary_homogeneous_irreducible_degree_le_one g hgh hgi
  omega

private theorem rationalAffineLine_contained_directionalDerivative {n : ℕ}
    (a v : RatPoint n) (f : CoordinatePolynomial n)
    (hline : rationalAffineLine a v ⊆ zeroLocus f) :
    rationalAffineLine a v ⊆ zeroLocus (directionalDerivative v f) := by
  classical
  have hder (g : CoordinatePolynomial n) :
      Polynomial.derivative (affineLinePolynomial a v g) =
        affineLinePolynomial a v (directionalDerivative v g) := by
    induction g using MvPolynomial.induction_on with
    | C r => simp [affineLinePolynomial, directionalDerivative]
    | add p q hp hq =>
      simp [directionalDerivative, mul_add, Finset.sum_add_distrib] at hp hq ⊢
      rw [hp, hq]
    | mul_X p j hp =>
      have hmul : directionalDerivative v (p * X j) =
          directionalDerivative v p * X j + p * C (v j) := by
        simp only [directionalDerivative, pderiv_mul, pderiv_X, Pi.single_apply, mul_add,
          Finset.sum_add_distrib, Finset.sum_mul]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · simp [mul_comm]
      rw [map_mul, Polynomial.derivative_mul, hp, hmul, map_add, map_mul, map_mul]
      simp [affineLinePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]
  have hpoly : affineLinePolynomial a v f = 0 :=
    Polynomial.zero_of_eval_zero _ fun t => (eval_affineLinePolynomial a v f t).trans (hline ⟨t, rfl⟩)
  rintro _ ⟨t, rfl⟩
  change eval (a + t • v) (directionalDerivative v f) = 0
  rw [← eval_affineLinePolynomial, ← hder, hpoly, Polynomial.derivative_zero, Polynomial.eval_zero]

private def affinePlaneMap {K σ : Type*} [CommRing K] (a b c : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1)

private lemma affinePlaneMap_eval {K σ : Type*} [CommRing K] (a b c : σ → K)
    (f : MvPolynomial σ K) (z : Fin 2 → K) :
    eval z (affinePlaneMap a b c f) = eval (fun i => a i + b i * z 0 + c i * z 1) f := by
  have he : (eval z).comp (affinePlaneMap a b c).toRingHom =
      eval (fun i => a i + b i * z 0 + c i * z 1) :=
    MvPolynomial.ringHom_ext (fun _ => by simp [affinePlaneMap]) fun _ => by simp [affinePlaneMap]
  exact RingHom.congr_fun he f

private lemma affinePlaneMap_totalDegree_le {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    (affinePlaneMap a b c f).totalDegree ≤ f.totalDegree := by
  change (eval₂Hom C (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1) f).totalDegree ≤ _
  apply linear_eval₂_totalDegree_le (RingHom.id K) _ _ f
  intro i
  have hx (j : Fin 2) : (X j : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    simpa [X] using totalDegree_monomial_le (Finsupp.single j 1) (1 : K)
  exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
    (max_le (by simp) ((totalDegree_mul _ _).trans (by simpa using hx 0))))
    ((totalDegree_mul _ _).trans (by simpa using hx 1)))

private def planeDirectionMatrix {K : Type*} [CommRing K] (b c v : Fin 3 → K) :
    Matrix (Fin 3) (Fin 3) K :=
  fun i j => ![b i, c i, v i] j

private theorem exists_surface_transverse_plane
    (f : MvPolynomial (Fin 3) ℤ) (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (g : MvPolynomial (Fin 3) ℚ) (hg : g ≠ 0) :
    ∃ a b c : Fin 3 → ℚ,
      (planeDirectionMatrix b c v).det ≠ 0 ∧
      Irreducible (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) ∧
      (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree ∧
      affinePlaneMap a b c g ≠ 0 := by
  classical
  let P_tr : MvPolynomial (PlaneParameters (Fin 3)) ℚ :=
    (planeDirectionMatrix (fun i => X (i, 1)) (fun i => X (i, 2)) (fun i => C (v i))).det
  have htr_eval (u : PlaneParameters (Fin 3) → ℚ) :
      eval u P_tr = (planeDirectionMatrix (fun i => u (i, 1)) (fun i => u (i, 2)) v).det := by
    dsimp [P_tr]; rw [RingHom.map_det]; congr 1; ext i j
    fin_cases j <;> simp [planeDirectionMatrix, Matrix.map_apply]
  have hP_tr : P_tr ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    intro he
    have hz (b c : Fin 3 → ℚ) : (planeDirectionMatrix b c v).det = 0 := by
      have hh := congrArg (eval fun i : PlaneParameters (Fin 3) => ![0, b i.1, c i.1] i.2) he
      rwa [htr_eval, map_zero] at hh
    fin_cases j
    · exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hz ![0, 1, 0] ![0, 0, 1])
    · exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hz ![1, 0, 0] ![0, 0, 1])
    · exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hz ![1, 0, 0] ![0, 1, 0])
  let P := P_tr * rename (fun i : Fin 3 => (i, (0 : Fin 3))) g
  have hP : P ≠ 0 := mul_ne_zero hP_tr
    ((map_ne_zero_iff _ (rename_injective _ fun _ _ h => congrArg Prod.fst h)).mpr hg)
  let e : Fin 3 ≃ Option (Fin 2) := finSuccEquiv' 0
  let ep : PlaneParameters (Fin 3) ≃ PlaneParameters (Option (Fin 2)) :=
    Equiv.prodCongr e (Equiv.refl _)
  let F := rename e f
  have hF : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, show F = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv _ e)).mpr hir
  have hFd : F.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  obtain ⟨PZ, t, _, ht, hmodel⟩ := exists_primitive_integer_model P hP
  have hPZ : PZ ≠ 0 := fun h => mul_ne_zero (C_eq_zero.not.mpr ht) hP (by simpa [h] using hmodel.symm)
  obtain ⟨u, _, hu, _, hdeg, hgood⟩ := exists_integer_geometrically_good_plane_avoiding F hF
    (hFd ▸ hd) (rename ep PZ) ((map_ne_zero_iff _ (rename_injective ep ep.injective)).mpr hPZ)
  let aZ : Fin 3 → ℤ := fun i => u (e i, 0)
  let bZ : Fin 3 → ℤ := fun i => u (e i, 1)
  let cZ : Fin 3 → ℤ := fun i => u (e i, 2)
  let q : MvPolynomial (Fin 2) ℤ := affinePlaneMap aZ bZ cZ f
  have hsec : universalPlaneSection F u = bivariatePolynomialEquiv ℤ q := by
    have hev : eval u = planeParameterEval (RingHom.id ℤ)
        (fun i => u (i, 0)) (fun i => u (i, 1)) (fun i => u (i, 2)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [planeParameterEval]
      · rintro ⟨i, j⟩; fin_cases j <;> simp [planeParameterEval]
    rw [universalPlaneSection, hev, universalPlanePolynomial_specialize]
    change bivariatePolynomialEquiv ℤ (affinePlaneMap _ _ _ (rename e f)) = _
    congr 1
    change eval₂Hom _ _ (rename e f) = eval₂Hom _ _ f
    simp only [eval₂Hom_rename, Function.comp_def, aZ, bZ, cZ]
  rw [hsec, bivariatePolynomialEquiv_map] at hgood hdeg
  have hqir : AbsolutelyIrreducible q :=
    (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv _)).mp hgood
  have hqd : q.totalDegree = f.totalDegree := by
    rw [bivariateTotalDegree_equiv] at hdeg
    have hm : (map (Int.castRingHom (AlgebraicClosure ℚ)) q).totalDegree = q.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
    simpa only [hm, hFd] using hdeg
  let a := (Int.castRingHom ℚ) ∘ aZ
  let b := (Int.castRingHom ℚ) ∘ bZ
  let c := (Int.castRingHom ℚ) ∘ cZ
  have hmap_aff : map (Int.castRingHom ℚ) q = affinePlaneMap a b c (map (Int.castRingHom ℚ) f) := by
    have he : (map (Int.castRingHom ℚ)).comp (affinePlaneMap aZ bZ cZ).toRingHom =
        (affinePlaneMap a b c).toRingHom.comp (map (Int.castRingHom ℚ)) :=
      MvPolynomial.ringHom_ext (fun _ => by simp [affinePlaneMap, a, b, c])
        fun _ => by simp [affinePlaneMap, a, b, c]
    exact RingHom.congr_fun he f
  have hu' : eval (fun i : PlaneParameters (Fin 3) => ![aZ i.1, bZ i.1, cZ i.1] i.2) PZ ≠ 0 := by
    rw [show (fun i : PlaneParameters (Fin 3) => ![aZ i.1, bZ i.1, cZ i.1] i.2) = u ∘ ep from
      funext fun ⟨_, j⟩ => by fin_cases j <;> rfl]
    simpa only [eval_rename] using hu
  have havoid : eval (fun i : PlaneParameters (Fin 3) => ![a i.1, b i.1, c i.1] i.2) P ≠ 0 := by
    have hh : (Int.castRingHom ℚ)
        (eval (fun i : PlaneParameters (Fin 3) => ![aZ i.1, bZ i.1, cZ i.1] i.2) PZ) ≠ 0 :=
      (map_ne_zero_iff _ Int.cast_injective).mpr hu'
    rw [map_eval] at hh
    have hmap : eval (fun i : PlaneParameters (Fin 3) => ![a i.1, b i.1, c i.1] i.2)
        (map (Int.castRingHom ℚ) PZ) ≠ 0 := by
      convert hh using 1; congr 2; funext ⟨_, j⟩; fin_cases j <;> rfl
    rw [hmodel, map_mul, eval_C] at hmap
    exact (mul_ne_zero_iff.mp hmap).2
  rw [show P = _ * _ from rfl, map_mul, htr_eval, eval_rename] at havoid
  obtain ⟨htrans, hbase⟩ := mul_ne_zero_iff.mp havoid
  refine ⟨a, b, c, htrans, hmap_aff ▸ rational_irreducible_of_charZero_map q hqir,
    hmap_aff ▸ (rational_map_totalDegree q).trans hqd, fun hz => hbase ?_⟩
  have hh := affinePlaneMap_eval a b c g 0
  rw [hz, map_zero] at hh
  change eval a g = 0
  simpa using hh.symm

private theorem surface_parallel_lines_card_le
    (f : MvPolynomial (Fin 3) ℤ) (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree)
    (v : RatPoint 3) (hv : v ≠ 0) (S : Finset (Set (RatPoint 3)))
    (hlines : ∀ L ∈ S, ∃ a, L = rationalAffineLine a v)
    (hSf : ∀ L ∈ S, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) :
    S.card ≤ f.totalDegree * (f.totalDegree - 1) := by
  classical
  let g := directionalDerivative v (map (Int.castRingHom ℚ) f)
  have hg : g ≠ 0 := surface_directionalDerivative_ne_zero f hir hd v hv
  have hgdeg : g.totalDegree ≤ f.totalDegree - 1 := by
    have : g.totalDegree ≤ (map (Int.castRingHom ℚ) f).totalDegree - 1 :=
      totalDegree_finsetSum_le fun i _ =>
        (totalDegree_mul _ _).trans (by simpa using pderiv_totalDegree_le _ i)
    simpa only [rational_map_totalDegree] using this
  obtain ⟨a, b, c, hdet, hF, hFd, hG⟩ := exists_surface_transverse_plane f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir) (by omega) v hv g hg
  choose x hx using fun L : S => hlines L.val L.property
  have hinter (L : S) : ∃ (z : Fin 2 → ℚ) (t : ℚ),
      (fun i => a i + b i * z 0 + c i * z 1) = x L + t • v := by
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)) (x L - a)
    refine ⟨![w 0, w 1], -w 2, funext fun i => ?_⟩
    have hi := congrFun hw i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, planeDirectionMatrix] at hi
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  choose z t hzt using hinter
  have hz_inj : Function.Injective z := fun L M he => Subtype.ext <|
    (hx L).trans <| ((rationalAffineLine_shift_base _ _ _).symm.trans
      (by rw [← hzt L, ← hzt M, he])).trans ((rationalAffineLine_shift_base _ _ _).trans (hx M).symm)
  have hFG : ¬ affinePlaneMap a b c (map (Int.castRingHom ℚ) f) ∣ affinePlaneMap a b c g := by
    rintro ⟨q, hq⟩
    have hq0 : q ≠ 0 := fun hz => hG (by rw [hq, hz, mul_zero])
    have hh : f.totalDegree ≤ (affinePlaneMap a b c g).totalDegree := by
      rw [hq, totalDegree_mul_of_isDomain hF.ne_zero hq0, hFd]; omega
    have := hh.trans (affinePlaneMap_totalDegree_le a b c g)
    omega
  have hcount := plane_common_zeros_card_le
    (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) (affinePlaneMap a b c g) hF hFG z hz_inj
    (fun L => by
      rw [affinePlaneMap_eval, hzt L]
      exact hSf L.val L.property (by rw [hx L]; exact ⟨t L, rfl⟩))
    (fun L => by
      rw [affinePlaneMap_eval, hzt L]
      exact rationalAffineLine_contained_directionalDerivative (x L) v _
        (by rw [← hx L]; exact hSf L.val L.property) ⟨t L, rfl⟩)
  rw [Fintype.card_coe, hFd] at hcount
  exact hcount.trans (Nat.mul_le_mul_left _ ((affinePlaneMap_totalDegree_le a b c g).trans hgdeg))

private theorem sum_inv_height_geometric_bound {α : Type*}
    (s : Finset α) (h : α → ℝ) (M : ℝ) (N : ℕ)
    (hheight : ∀ x ∈ s, 1 ≤ h x) (hmax : ∀ x ∈ s, h x ≤ (8 : ℝ) ^ N)
    (hcount : ∀ k : ℕ, ((s.filter fun x => h x ≤ (8 : ℝ) ^ k).card : ℝ) ≤ M * 4 ^ k) :
    ∑ x ∈ s, 1 / h x ≤ 9 * M - 8 * M * (1 / 2 : ℝ) ^ N := by
  classical
  induction N generalizing s with
  | zero =>
    have he (x) (hx : x ∈ s) : h x = 1 := by
      have := hmax x hx; have := hheight x hx; norm_num at *; linarith
    have hc := hcount 0
    rw [Finset.filter_eq_self.mpr hmax] at hc
    rw [Finset.sum_congr rfl fun x hx => show 1 / h x = (1 : ℝ) by rw [he x hx]; norm_num,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    simpa only [pow_zero, mul_one, show 9 * M - 8 * M = M by ring] using hc
  | succ N ih =>
    let t := s.filter fun x => h x ≤ (8 : ℝ) ^ N
    let u := s.filter fun x => ¬ h x ≤ (8 : ℝ) ^ N
    have ht := ih t (fun x hx => hheight x (Finset.mem_filter.mp hx).1)
      (fun x hx => (Finset.mem_filter.mp hx).2) fun k =>
        (Nat.cast_le.mpr (Finset.card_le_card fun x hx => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1, (Finset.mem_filter.mp hx).2⟩)).trans
          (hcount k)
    have hscard : (s.card : ℝ) ≤ M * 4 ^ (N + 1) := by
      simpa only [Finset.filter_eq_self.mpr hmax] using hcount (N + 1)
    have hu : ∑ x ∈ u, 1 / h x ≤ 4 * M * (1 / 2 : ℝ) ^ N := calc
      ∑ x ∈ u, 1 / h x ≤ ∑ _x ∈ u, 1 / (8 : ℝ) ^ N :=
        Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le (by positivity)
          (le_of_not_ge (Finset.mem_filter.mp hx).2)
      _ = (u.card : ℝ) / (8 : ℝ) ^ N := by simp [div_eq_mul_inv]
      _ ≤ (M * 4 ^ (N + 1)) / (8 : ℝ) ^ N := div_le_div_of_nonneg_right
          ((Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ s))).trans hscard)
          (by positivity)
      _ = 4 * M * (1 / 2 : ℝ) ^ N := by
          rw [pow_succ, show M * ((4 : ℝ) ^ N * 4) / (8 : ℝ) ^ N =
            4 * M * ((4 : ℝ) ^ N / (8 : ℝ) ^ N) by ring, ← div_pow]; norm_num
    have he := Finset.sum_filter_add_sum_filter_not s (fun x => h x ≤ (8 : ℝ) ^ N) (fun x => 1 / h x)
    rw [pow_succ]; linarith

private theorem integer_projective_plane_reciprocal_height_sum :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ (d : ℕ), 3 ≤ d →
      ∀ F : MvPolynomial (Fin 3) ℤ, F.IsHomogeneous d → AbsolutelyIrreducible F →
      ∀ s : Finset (ProjectivePoint 2),
        (∀ x ∈ s, x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) F)) →
        ∑ x ∈ s, 1 / x.mulHeight ≤ K₀ * (d : ℝ) ^ 4 := by
  classical
  refine ⟨9 * projectivePlaneAbsoluteConstant, mul_pos (by norm_num) projectivePlaneAbsoluteConstant_pos,
    fun d hd F hF hir s hs => ?_⟩
  let f := map (Int.castRingHom ℚ) F
  have hf : f.IsHomogeneous d := hF.map _
  have hfir : Irreducible f := rational_irreducible_of_charZero_map F hir
  have hC := projectivePlaneAbsoluteConstant_pos
  have hd0 : (0 : ℝ) < d := mod_cast (by omega : 0 < d)
  have hd3 : (3 : ℝ) ≤ d := mod_cast hd
  let M := projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ x ∈ s, x.mulHeight) (by norm_num : (1 : ℝ) < 8)
  have hmax (x) (hx : x ∈ s) : x.mulHeight ≤ (8 : ℝ) ^ N :=
    (Finset.single_le_sum (fun y _ => zero_le_one.trans y.one_le_mulHeight) hx).trans hN.le
  have hh := sum_inv_height_geometric_bound s (fun x => x.mulHeight) M N
    (fun x _ => x.one_le_mulHeight) hmax fun k => by
      have hB : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
      have hc : ((s.filter fun x => x.mulHeight ≤ (8 : ℝ) ^ k).card : ℝ) ≤
          projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) :=
        mod_cast Finset.card_le_card fun x hx => mem_projectivePoints.mpr
          ⟨(Finset.mem_filter.mp hx).2, hs x (Finset.mem_filter.mp hx).1⟩
      have he8 : ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) = (4 : ℝ) ^ k := by
        have h84 : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (k : ℝ),
          Real.rpow_mul_natCast (by norm_num), h84]
      have hp : ((8 : ℝ) ^ k) ^ (2 / (d : ℝ)) ≤ (4 : ℝ) ^ k :=
        (Real.rpow_le_rpow_of_exponent_le hB
          ((div_le_div_iff₀ hd0 (by norm_num)).mpr (by linarith))).trans_eq he8
      exact (hc.trans (projective_plane_equation_bound f hf (by omega) hfir hB)).trans
        (mul_le_mul_of_nonneg_left hp (by positivity))
  have : 0 ≤ 8 * M * (1 / 2 : ℝ) ^ N := by positivity
  dsimp [M] at hh; linarith

private theorem surface_line_projective_direction
    (f : MvPolynomial (Fin 3) ℤ) (L : Set (RatPoint 3))
    (hL : ∃ a v, L = rationalAffineLine a v)
    (hLf : L ⊆ zeroLocus (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 0 ≤ B) (hcount : 1 < count L B) :
    ∃ p : ProjectivePoint 2,
      p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      0 < p.mulHeight ∧ p.mulHeight ≤ 2 * B ∧
      (∃ a, L = rationalAffineLine a p.rep) ∧
      (count L B : ℝ) ≤ 4 * B / p.mulHeight := by
  obtain ⟨a, v, rfl⟩ := hL
  obtain ⟨z, w, hw, hprim, _, hheight, hline, hcnt⟩ :=
    rationalAffineLine_integer_rep_and_count a v hB hcount
  let p := Projectivization.mk ℚ (rationalPoint w) (rationalPoint_ne_zero hw)
  have hpheight : p.mulHeight = (integerDirectionHeight w : ℝ) :=
    projective_direction_height w hw hprim
  have hp0 : 0 < p.mulHeight := hpheight ▸ mod_cast integerDirectionHeight_pos hw
  have hpoly : affineLinePolynomial (rationalPoint z) (rationalPoint w) (map (Int.castRingHom ℚ) f) = 0 :=
    Polynomial.zero_of_eval_zero _ fun t =>
      (eval_affineLinePolynomial _ _ _ t).trans ((hline ▸ hLf) ⟨t, rfl⟩)
  have hzero : eval (rationalPoint w)
      (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) = 0 := by
    have hc := affineLinePolynomial_top_coefficient (rationalPoint z) (rationalPoint w)
      (map (Int.castRingHom ℚ) f) f.totalDegree (totalDegree_map_le _ _)
    rwa [hpoly, Polynomial.coeff_zero, ← map_homogeneousComponent, eq_comm] at hc
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ (rationalPoint w) p.rep
    (rationalPoint_ne_zero hw) p.rep_nonzero).mp p.mk_rep.symm
  refine ⟨p, (mem_projectiveZeroLocus_mk ((homogeneousComponent_isHomogeneous _ _).map _) _ _).mpr hzero,
    hp0, hpheight ▸ hheight,
    ⟨rationalPoint z, hline.trans (hc.symm ▸ rationalAffineLine_smul_direction _ p.rep c.ne_zero)⟩, ?_⟩
  rw [← hpheight] at hcnt
  have htwo : 1 ≤ 2 * B / p.mulHeight :=
    (le_div_iff₀ hp0).mpr (by simpa only [one_mul, hpheight] using hheight)
  calc (count (rationalAffineLine a v) B : ℝ) ≤ 1 + 2 * B / p.mulHeight := hcnt
    _ ≤ 2 * B / p.mulHeight + 2 * B / p.mulHeight := by linarith
    _ = 4 * B / p.mulHeight := by ring

theorem surface_degree_one_component_contribution :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree → ∀ B : ℝ, 0 ≤ B →
      ∀ S : Finset (Ideal (CoordinatePolynomial 3)),
      (∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1) →
      (∀ P ∈ S, map (Int.castRingHom ℚ) f ∈ P) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
        K₀ * (f.totalDegree : ℝ) ^ 6 * B + S.card := by
  classical
  obtain ⟨K, hK, hweight⟩ := integer_projective_plane_reciprocal_height_sum
  refine ⟨4 * K, by positivity, fun f hir hd B hB S hcurve hSf => ?_⟩
  let S_ne := S.filter fun P => (idealZeroLocus P).Nonempty
  let s := S_ne.image idealZeroLocus
  have hs_card : s.card ≤ S.card :=
    Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hcover : (⋃ P ∈ S, idealZeroLocus P) = ⋃ L ∈ s, L := by
    ext x; constructor
    · intro hx
      obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨idealZeroLocus P, Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨hPS, ⟨x, hxP⟩⟩, rfl⟩, hxP⟩⟩
    · intro hx
      obtain ⟨L, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hLs, hxL⟩ := Set.mem_iUnion.mp hx
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hLs
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hPT).1, hxL⟩⟩
  have hlines (L) (hL : L ∈ s) : ∃ a v, L = rationalAffineLine a v := by
    obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hPS, z, hz⟩ := Finset.mem_filter.mp hPT
    obtain ⟨hp, hht, hdeg⟩ := hcurve P hPS
    have : P.IsPrime := hp
    obtain ⟨v, _, he, _⟩ := degree_one_zeroLocus_eq_rationalAffineLine P hht hdeg z hz
    exact ⟨z, v, he⟩
  have hsurface (L) (hL : L ∈ s) : L ⊆ zeroLocus (map (Int.castRingHom ℚ) f) := by
    obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
    exact fun x hx => hx _ (hSf P (Finset.mem_filter.mp hPT).1)
  let t := s.filter fun L => 1 < count L B
  have hdir (L) (hL : L ∈ t) := surface_line_projective_direction f L
    (hlines L (Finset.mem_filter.mp hL).1) (hsurface L (Finset.mem_filter.mp hL).1)
    hB (Finset.mem_filter.mp hL).2
  let p : Set (RatPoint 3) → ProjectivePoint 2 := fun L =>
    if hL : L ∈ t then (hdir L hL).choose else Classical.choice inferInstance
  have hp (L) (hL : L ∈ t) :
      p L ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      0 < (p L).mulHeight ∧ (p L).mulHeight ≤ 2 * B ∧
      (∃ a, L = rationalAffineLine a (p L).rep) ∧
      (count L B : ℝ) ≤ 4 * B / (p L).mulHeight := by
    simpa only [p, dite_eq_left hL] using (hdir L hL).choose_spec
  have hfib (q) (_hq : q ∈ t.image p) :
      ((t.filter fun L => p L = q).card : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by
    have hc := surface_parallel_lines_card_le f hir (by omega) q.rep q.rep_nonzero
      (t.filter fun L => p L = q)
      (fun L hL => by
        obtain ⟨hLt, he⟩ := Finset.mem_filter.mp hL
        simpa only [he] using (hp L hLt).2.2.2.1)
      (fun L hL => hsurface L (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).1)
    exact_mod_cast hc.trans (by nlinarith [Nat.sub_le f.totalDegree 1])
  have himage : ∑ q ∈ t.image p, 1 / q.mulHeight ≤ K * (f.totalDegree : ℝ) ^ 4 :=
    hweight f.totalDegree hd _ (homogeneousComponent_isHomogeneous _ _) hir _ fun q hq => by
      obtain ⟨L, hLt, rfl⟩ := Finset.mem_image.mp hq; exact (hp L hLt).1
  have hsum : ∑ L ∈ t, 1 / (p L).mulHeight ≤ K * (f.totalDegree : ℝ) ^ 6 := calc
    ∑ L ∈ t, 1 / (p L).mulHeight
        = ∑ q ∈ t.image p, ∑ L ∈ t.filter (fun x => p x = q), 1 / (p L).mulHeight :=
          (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem p hx) _).symm
    _ ≤ ∑ q ∈ t.image p, (f.totalDegree : ℝ) ^ 2 * (1 / q.mulHeight) :=
        Finset.sum_le_sum fun q hq => by
          rw [Finset.sum_congr rfl fun L hL => by rw [(Finset.mem_filter.mp hL).2]]
          simpa using mul_le_mul_of_nonneg_right (hfib q hq) (by positivity : 0 ≤ 1 / q.mulHeight)
    _ = (f.totalDegree : ℝ) ^ 2 * ∑ q ∈ t.image p, 1 / q.mulHeight := (Finset.mul_sum _ _ _).symm
    _ ≤ (f.totalDegree : ℝ) ^ 2 * (K * (f.totalDegree : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left himage (by positivity)
    _ = K * (f.totalDegree : ℝ) ^ 6 := by ring
  have hgood : ∑ L ∈ t, (count L B : ℝ) ≤ (4 * K) * (f.totalDegree : ℝ) ^ 6 * B := calc
    ∑ L ∈ t, (count L B : ℝ) ≤ ∑ L ∈ t, 4 * B / (p L).mulHeight :=
      Finset.sum_le_sum fun L hL => (hp L hL).2.2.2.2
    _ = 4 * B * ∑ L ∈ t, 1 / (p L).mulHeight := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ 4 * B * (K * (f.totalDegree : ℝ) ^ 6) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (4 * K) * (f.totalDegree : ℝ) ^ 6 * B := by ring
  have hbad : ∑ L ∈ s.filter (fun L => ¬ 1 < count L B), (count L B : ℝ) ≤ S.card := calc
    ∑ L ∈ s.filter (fun L => ¬ 1 < count L B), (count L B : ℝ)
        ≤ ∑ _L ∈ s.filter (fun L => ¬ 1 < count L B), (1 : ℝ) :=
          Finset.sum_le_sum fun L hL => mod_cast Nat.le_of_not_gt (Finset.mem_filter.mp hL).2
    _ = ((s.filter fun L => ¬ 1 < count L B).card : ℝ) := by simp
    _ ≤ S.card := mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans hs_card
  rw [hcover]
  have hc : (count (⋃ L ∈ s, L) B : ℝ) ≤ ∑ L ∈ s, (count L B : ℝ) :=
    mod_cast count_biUnion_finset_le s id B
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun L => 1 < count L B)
    (fun L => (count L B : ℝ))
  linarith

end
end CCDN
