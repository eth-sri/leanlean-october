/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.FiniteFieldBadPlanes
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.Determinant.PlaneMultiplicity
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.ShearNormalization
import CCDN.Noether.UniversalPlaneSpecialization

/-! Irreducible plane sections transverse to a prescribed direction.
The avoidance condition also ensures that a second equation restricts
nontrivially, by requiring its value at the plane's base point to be nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The algebra map restricting a polynomial to the plane parametrized by
`(s, t) ↦ a + s b + t c`, sending `Xᵢ` to `aᵢ + bᵢ X 0 + cᵢ X 1`. -/
def affinePlaneMap {K σ : Type*} [CommRing K] (a b c : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1)

/-- Evaluating the restriction of `f` to the plane `a + s b + t c` at `z` gives the value of
`f` at `a + z 0 • b + z 1 • c`. -/
lemma affinePlaneMap_eval {K σ : Type*} [CommRing K] (a b c : σ → K)
    (f : MvPolynomial σ K) (z : Fin 2 → K) :
    eval z (affinePlaneMap a b c f) =
      eval (fun i => a i + b i * z 0 + c i * z 1) f := by
  have he : (eval z).comp (affinePlaneMap a b c).toRingHom =
      eval (fun i => a i + b i * z 0 + c i * z 1) := by
    apply MvPolynomial.ringHom_ext <;> intro _ <;> simp [affinePlaneMap]
  exact RingHom.congr_fun he f

/-- Restricting a polynomial to an affine plane does not increase its total degree. -/
lemma affinePlaneMap_totalDegree_le {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    (affinePlaneMap a b c f).totalDegree ≤ f.totalDegree := by
  change (eval₂Hom C (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1) f).totalDegree ≤ _
  apply linear_eval₂_totalDegree_le (RingHom.id K) _ _ f
  intro i
  have hx (j : Fin 2) : (X j : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
    simpa [X] using totalDegree_monomial_le (Finsupp.single j 1) (1 : K)
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (by simp)
      ((totalDegree_mul _ _).trans (by simpa using hx 0))))
    ((totalDegree_mul _ _).trans (by simpa using hx 1)))

/-- The `3 × 3` matrix with columns `b`, `c` and `v`; over a field, its determinant is nonzero
exactly when `b`, `c` and `v` are linearly independent. -/
def planeDirectionMatrix {K : Type*} [CommRing K] (b c v : Fin 3 → K) :
    Matrix (Fin 3) (Fin 3) K :=
  fun i j => ![b i, c i, v i] j

/-- A geometrically irreducible surface admits a transverse plane
whose restriction of any prescribed nonzero second equation is nonzero. -/
theorem exists_surface_transverse_plane
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (g : MvPolynomial (Fin 3) ℚ) (hg : g ≠ 0) :
    ∃ a b c : Fin 3 → ℚ,
      (planeDirectionMatrix b c v).det ≠ 0 ∧
      Irreducible (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) ∧
      (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)).totalDegree = f.totalDegree ∧
      affinePlaneMap a b c g ≠ 0 := by
  classical
  let T : MvPolynomial (PlaneParameters (Fin 3)) ℚ :=
    (planeDirectionMatrix (fun i => X (i,1)) (fun i => X (i,2)) (fun i => C (v i))).det
  have hT_eval (u : PlaneParameters (Fin 3) → ℚ) :
      eval u T = (planeDirectionMatrix (fun i => u (i,1)) (fun i => u (i,2)) v).det := by
    rw [RingHom.map_det]
    congr 1; ext i j; fin_cases j <;> simp [planeDirectionMatrix, Matrix.map_apply]
  have htrans_ne : T ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    intro he
    have hz (b c : Fin 3 → ℚ) : (planeDirectionMatrix b c v).det = 0 := by
      have hh := congrArg (eval (fun i : PlaneParameters (Fin 3) => ![0, b i.1, c i.1] i.2)) he
      rwa [hT_eval, map_zero] at hh
    fin_cases j
    · exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hz ![0,1,0] ![0,0,1])
    · exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hz ![1,0,0] ![0,0,1])
    · exact hj (by simpa [planeDirectionMatrix, Matrix.det_fin_three] using hz ![1,0,0] ![0,1,0])
  let P := T * rename (fun i : Fin 3 => (i, (0 : Fin 3))) g
  have hP : P ≠ 0 := mul_ne_zero htrans_ne
    ((map_ne_zero_iff _ (rename_injective _ (fun _ _ h => congrArg Prod.fst h))).mpr hg)
  let e : Fin 3 ≃ Option (Fin 2) := finSuccEquiv' 0
  let ep : PlaneParameters (Fin 3) ≃ PlaneParameters (Option (Fin 2)) :=
    Equiv.prodCongr e (Equiv.refl _)
  let F := rename e f
  have hF : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, show F = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv _ e)).mpr hir
  have hFd : F.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  obtain ⟨PZ, t, _, ht, hmodel⟩ := exists_primitive_integer_model P hP
  have hPZ : PZ ≠ 0 := fun h => mul_ne_zero (C_eq_zero.not.mpr ht) hP
    (by rw [h, map_zero] at hmodel; exact hmodel.symm)
  obtain ⟨u, _, hu, _, hdeg, hgood⟩ := exists_integer_geometrically_good_plane_avoiding
    F hF (hFd ▸ hd) (rename ep PZ) ((map_ne_zero_iff _ (rename_injective ep ep.injective)).mpr hPZ)
  let a : Fin 3 → ℤ := fun i => u (e i,0)
  let b : Fin 3 → ℤ := fun i => u (e i,1)
  let c : Fin 3 → ℤ := fun i => u (e i,2)
  let q : MvPolynomial (Fin 2) ℤ := affinePlaneMap a b c f
  have hsection : universalPlaneSection F u = bivariatePolynomialEquiv ℤ q := by
    have he : eval u = planeParameterEval (RingHom.id ℤ)
        (fun i => u (i,0)) (fun i => u (i,1)) (fun i => u (i,2)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [planeParameterEval]
      · rintro ⟨i, j⟩; fin_cases j <;> simp [planeParameterEval]
    rw [universalPlaneSection, he, universalPlanePolynomial_specialize]
    change bivariatePolynomialEquiv ℤ (affinePlaneMap _ _ _ (rename e f)) = _
    congr 1
    change eval₂Hom _ _ (rename e f) = eval₂Hom _ _ f
    simp only [eval₂Hom_rename, Function.comp_def]
    rfl
  rw [hsection, bivariatePolynomialEquiv_map] at hgood hdeg
  have hqir : AbsolutelyIrreducible q :=
    (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv _)).mp hgood
  have hqd : q.totalDegree = f.totalDegree := by
    rw [bivariateTotalDegree_equiv] at hdeg
    have hm : (map (Int.castRingHom (AlgebraicClosure ℚ)) q).totalDegree = q.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
    simpa only [hm, hFd] using hdeg
  have hu' : eval (fun i => ![a i.1, b i.1, c i.1] i.2) PZ ≠ 0 := by
    rw [show (fun i : PlaneParameters (Fin 3) => ![a i.1, b i.1, c i.1] i.2) = u ∘ ep by
      funext ⟨i, j⟩; fin_cases j <;> rfl]
    simpa only [eval_rename] using hu
  have hmap : eval (fun i => ![((Int.castRingHom ℚ) ∘ a) i.1,
        ((Int.castRingHom ℚ) ∘ b) i.1, ((Int.castRingHom ℚ) ∘ c) i.1] i.2)
      (map (Int.castRingHom ℚ) PZ) ≠ 0 := by
    have hh : (Int.castRingHom ℚ) (eval (fun i => ![a i.1, b i.1, c i.1] i.2) PZ) ≠ 0 :=
      (map_ne_zero_iff _ Int.cast_injective).mpr hu'
    rw [map_eval] at hh
    convert hh using 1; congr 2; funext ⟨i, j⟩; fin_cases j <;> rfl
  rw [hmodel, map_mul, eval_C] at hmap
  have havoid := (mul_ne_zero_iff.mp hmap).2
  rw [show P = _ * _ from rfl, map_mul, hT_eval, eval_rename] at havoid
  obtain ⟨htrans, hbase⟩ := mul_ne_zero_iff.mp havoid
  have hmap_aff : map (Int.castRingHom ℚ) q =
      affinePlaneMap ((Int.castRingHom ℚ) ∘ a) ((Int.castRingHom ℚ) ∘ b)
        ((Int.castRingHom ℚ) ∘ c) (map (Int.castRingHom ℚ) f) := by
    have he : (map (Int.castRingHom ℚ)).comp (affinePlaneMap a b c).toRingHom =
        (affinePlaneMap ((Int.castRingHom ℚ) ∘ a) ((Int.castRingHom ℚ) ∘ b)
          ((Int.castRingHom ℚ) ∘ c)).toRingHom.comp (map (Int.castRingHom ℚ)) := by
      apply MvPolynomial.ringHom_ext <;> intro _ <;> simp [affinePlaneMap]
    exact RingHom.congr_fun he f
  refine ⟨(Int.castRingHom ℚ) ∘ a, (Int.castRingHom ℚ) ∘ b, (Int.castRingHom ℚ) ∘ c,
    htrans, ?_, ?_, ?_⟩
  · rw [← hmap_aff]; exact rational_irreducible_of_charZero_map q hqir
  · rw [← hmap_aff]; exact (rational_map_totalDegree q).trans hqd
  · intro hz
    have hh := affinePlaneMap_eval ((Int.castRingHom ℚ) ∘ a) ((Int.castRingHom ℚ) ∘ b)
      ((Int.castRingHom ℚ) ∘ c) g (0 : Fin 2 → ℚ)
    rw [hz, map_zero] at hh
    change eval (fun i => (a i : ℚ)) g ≠ 0 at hbase
    exact hbase (by simpa [Function.comp_def] using hh.symm)

end
end CCDN
