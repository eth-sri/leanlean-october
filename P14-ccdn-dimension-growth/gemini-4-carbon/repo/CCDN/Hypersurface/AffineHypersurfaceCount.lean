/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.Algebra.AffineTranslation
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.AffineLeadingTranslation
import CCDN.Determinant.PlaneMultiplicity
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.UniversalPlaneBadWitness
import CCDN.Plane.FullDegreeSectionIrreducibility
import CCDN.Plane.IntegerPlaneHeight
import CCDN.Plane.SectionBounds
import CCDN.Surface.AffineSurfaceDimensionGrowth
import CCDN.Surface.TopFormIrreducibility
import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
open scoped Matrix

private def graphRestr {K σ : Type*} [CommRing K] [Fintype σ]
    (a : σ → K) : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => Option.elim i (∑ j, C (a j) * X j) X)

private lemma graphRestr_eval {K σ : Type*} [CommRing K] [Fintype σ]
    (a x : σ → K) (f : MvPolynomial (Option σ) K) :
    eval x (graphRestr a f) = eval (fun i => Option.elim i (∑ j, a j * x j) x) f := by
  have he : (eval x).comp (graphRestr a).toRingHom =
      eval (fun i => Option.elim i (∑ j, a j * x j) x) :=
    MvPolynomial.ringHom_ext (fun _ => by simp [graphRestr]) fun i => by cases i <;> simp [graphRestr]
  exact RingHom.congr_fun he f

private lemma graphRestr_map {K L σ : Type*} [CommRing K] [CommRing L] [Fintype σ]
    (φ : K →+* L) (a : σ → K) (f : MvPolynomial (Option σ) K) :
    map φ (graphRestr a f) = graphRestr (φ ∘ a) (map φ f) := by
  have he : (map φ).comp (graphRestr a).toRingHom =
      (graphRestr (φ ∘ a)).toRingHom.comp (map φ) :=
    MvPolynomial.ringHom_ext (fun _ => by simp [graphRestr]) fun i => by cases i <;> simp [graphRestr]
  exact RingHom.congr_fun he f

private lemma graphRestr_homogeneousComponent {K σ : Type*} [CommRing K] [Fintype σ]
    (a : σ → K) (f : MvPolynomial (Option σ) K) (d : ℕ) :
    graphRestr a (homogeneousComponent d f) = homogeneousComponent d (graphRestr a f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isHomogeneous_monomial c (rfl : m.degree = m.degree)
    have hgh : (graphRestr a (monomial m c)).IsHomogeneous m.degree := by
      have haev := hm.aeval (fun i => Option.elim i (∑ j, C (a j) * X j) X) fun i => by
        cases i
        · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X K j).C_mul (a j)
        · exact isHomogeneous_X K _
      simpa only [one_mul, graphRestr] using haev
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hgh]
    split_ifs <;> simp
  | add _ _ hf hg => simp only [map_add, hf, hg]

private lemma planeSec_eval {K τ : Type*} [CommRing K]
    (q : MvPolynomial τ K) (u : PlaneParameters τ → K) (t : Fin 2 → K) :
    eval t (planeSectionPolynomial q u) =
      eval (fun i => u (i, 0) + u (i, 1) * t 0 + u (i, 2) * t 1) q := by
  rw [← bivariateEval_equiv, planeSectionPolynomial, AlgEquiv.apply_symm_apply]
  exact universalPlaneSection_eval q u (t 0) (t 1)

private theorem graphRestr_irreducible_of_plane {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (a : σ → K) (v : PlaneParameters (Option σ) → K)
    (hv : ∀ j : Fin 3, v (none, j) = ∑ i, a i * v (some i, j))
    (hir : Irreducible (universalPlaneSection f v))
    (hdeg : bivariateTotalDegree (universalPlaneSection f v) = f.totalDegree) :
    Irreducible (graphRestr a f) := by
  let w : PlaneParameters σ → K := fun p => v (some p.1, p.2)
  have he : planeSectionPolynomial (graphRestr a f) w = planeSectionPolynomial f v := by
    apply MvPolynomial.funext; intro t
    rw [planeSec_eval, graphRestr_eval, planeSec_eval]
    refine congrArg (eval · f) (funext fun i => ?_)
    cases i
    · simp [w, hv, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    · rfl
  have hle : (graphRestr a f).totalDegree ≤ f.totalDegree :=
    linear_eval₂_totalDegree_le _ _ (fun i => by
      cases i
      · exact totalDegree_finsetSum_le fun _ _ => (totalDegree_mul _ _).trans (by simp)
      · simp) f
  have hfull : (graphRestr a f).totalDegree = f.totalDegree := by
    have hh := planeSectionPolynomial_totalDegree (graphRestr a f) w
    rw [he] at hh
    exact le_antisymm hle (hdeg ▸ hh)
  refine irreducible_of_full_degree_map (planeSectionPolynomialHom w)
    (fun g => planeSectionPolynomial_totalDegree g w) _ ?_ ?_
  · change Irreducible (planeSectionPolynomial (graphRestr a f) w)
    rw [he]; exact (MulEquiv.irreducible_iff (f := (bivariatePolynomialEquiv K).symm)).mpr hir
  · change (planeSectionPolynomial (graphRestr a f) w).totalDegree = (graphRestr a f).totalDegree
    rw [he, hfull]; exact hdeg

private theorem exists_good_int_hyperplane {n : ℕ}
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hf : f.IsHomogeneous d) (hir : AbsolutelyIrreducible f) :
    ∃ a : Fin (3 + n) → ℤ, (∀ i, |a i| ≤ (2 * d ^ 3 : ℕ)) ∧
      AbsolutelyIrreducible (graphRestr a f) := by
  classical
  have hf0 : f ≠ 0 := fun hz => hir.ne_zero (by rw [hz, map_zero])
  have hfdeg : f.totalDegree = d := hf.totalDegree hf0
  obtain ⟨rows, cols, hW, hWdeg⟩ :=
    exists_integer_universalPlane_badWitness f hir (hfdeg ▸ by omega)
  let W := universalPlaneBadWitness f rows cols
  let A : MvPolynomial (PlaneParameters (Option (Fin (3 + n)))) ℤ :=
    Matrix.det (Matrix.of fun i j : Fin 3 => X (some (i.castAdd n), j))
  have hA : A ≠ 0 := fun hz => one_ne_zero (α := ℤ) <| by
    let u : PlaneParameters (Option (Fin (3 + n))) → ℤ :=
      fun p => if p.1 = some (p.2.castAdd n) then 1 else 0
    have hu : eval u A = 1 := by
      rw [show A = _ from rfl, RingHom.map_det]
      convert Matrix.det_one (n := Fin 3) (R := ℤ) using 2; ext i j
      simp [u, (Fin.castAdd_injective 3 n).eq_iff, Matrix.one_apply]
    rw [hz, map_zero] at hu; exact hu.symm
  obtain ⟨v, _, hvWA⟩ := exists_integer_grid_eval_ne_zero_of_totalDegree (W * A)
    (mul_ne_zero hW hA) _ le_rfl
  rw [eval_mul] at hvWA
  obtain ⟨hvW, hvA⟩ := mul_ne_zero_iff.mp hvWA
  let M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i j => (v (some (i.castAdd n), j) : ℚ)
  have hMdet : M.det ≠ 0 := by
    have hcast : M.det = (eval v A : ℚ) := by simp [M, A, Matrix.det_fin_three]
    rw [hcast]; exact_mod_cast hvA
  let w0 : Fin 3 → ℚ := fun k => (v (none, k) : ℚ)
  let b₀ : Fin 3 → ℚ := (M.det)⁻¹ • Mᵀ.cramer w0
  have hb₀ : Mᵀ *ᵥ b₀ = w0 := by
    dsimp only [b₀]
    rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, Matrix.det_transpose, inv_smul_smul₀ hMdet]
  let α₀ : Fin (3 + n) → ℚ := Fin.addCases b₀ 0
  let Φ : PlaneParameters (Option (Fin (3 + n))) → MvPolynomial (Fin (3 + n)) ℚ := fun p =>
    Option.elim p.1 (∑ j, C (v (some j, p.2) : ℚ) * X j) fun i => C (v (some i, p.2) : ℚ)
  let P : MvPolynomial (Fin (3 + n)) ℚ := eval₂Hom (C.comp (Int.castRingHom ℚ)) Φ W
  have hP_deg : P.totalDegree ≤ 2 * d ^ 3 :=
    (linear_eval₂_totalDegree_le (Int.castRingHom ℚ) Φ
      (fun ⟨o, k⟩ => by
        cases o with
        | none =>
          dsimp only [Φ, Option.elim_none]
          exact totalDegree_finsetSum_le fun _ _ =>
            (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
        | some i => dsimp only [Φ, Option.elim_some]; rw [totalDegree_C]; omega) W).trans (hfdeg ▸ hWdeg)
  have hP_eval (β : Fin (3 + n) → ℚ) : eval β P = eval₂ (Int.castRingHom ℚ)
      (fun p => Option.elim p.1 (∑ j, β j * (v (some j, p.2) : ℚ))
        fun i => (v (some i, p.2) : ℚ)) W := by
    have he : (eval β).comp (eval₂Hom (C.comp (Int.castRingHom ℚ)) Φ) =
        eval₂Hom (Int.castRingHom ℚ)
          (fun p => Option.elim p.1 (∑ j, β j * (v (some j, p.2) : ℚ))
            fun i => (v (some i, p.2) : ℚ)) :=
      MvPolynomial.ringHom_ext (fun _ => by simp) fun ⟨o, _⟩ => by cases o <;> simp [Φ, mul_comm]
    exact RingHom.congr_fun he W
  have hP_ne : P ≠ 0 := fun h0 => by
    have hev : eval α₀ P = 0 := by rw [h0, map_zero]
    rw [hP_eval, show (fun p : PlaneParameters (Option (Fin (3 + n))) =>
        Option.elim p.1 (∑ j, α₀ j * (v (some j, p.2) : ℚ))
          fun i => (v (some i, p.2) : ℚ)) = fun p => (v p : ℚ) by
      funext ⟨o, k⟩; cases o with
      | none =>
        have hk := congrFun hb₀ k
        dsimp only [Option.elim_none]
        rw [Fin.sum_univ_add]
        simpa [α₀, w0, Matrix.mulVec, dotProduct, M, mul_comm] using hk
      | some i => rfl, ← eval_map] at hev
    change eval ((Int.castRingHom ℚ) ∘ v) (map (Int.castRingHom ℚ) W) = 0 at hev
    rw [← map_eval] at hev
    exact hvW (Int.cast_injective hev)
  obtain ⟨a, ha, ha_ne⟩ := exists_integer_grid_eval_ne_zero_of_totalDegree P hP_ne _ hP_deg
  let α : Fin (3 + n) → ℚ := fun i => (a i : ℚ)
  let φ : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  let ψ : ℤ →+* AlgebraicClosure ℚ := Int.castRingHom (AlgebraicClosure ℚ)
  let vQ : PlaneParameters (Option (Fin (3 + n))) → ℚ :=
    fun p => Option.elim p.1 (∑ j, α j * (v (some j, p.2) : ℚ)) fun i => (v (some i, p.2) : ℚ)
  have hwK : (φ.comp (eval₂Hom (Int.castRingHom ℚ) vQ)) W ≠ 0 := by
    change φ (eval₂ (Int.castRingHom ℚ) vQ W) ≠ 0
    rw [← hP_eval α]; exact (map_ne_zero_iff φ φ.injective).mpr ha_ne
  have hspec := universalPlaneBadWitness_good_specialization f (hfdeg ▸ by omega)
    (.of_charZero _) rows cols (φ.comp (eval₂Hom (Int.castRingHom ℚ) vQ)) hwK
  have hhom_eq : φ.comp (eval₂Hom (Int.castRingHom ℚ) vQ) = (eval (φ ∘ vQ)).comp (map ψ) :=
    MvPolynomial.ringHom_ext (fun _ => by simp [ψ]) fun _ => by simp
  rw [hhom_eq, bivariateMap_comp_apply, ← universalPlanePolynomial_map] at hspec
  have hgood := graphRestr_irreducible_of_plane (map ψ f) (φ ∘ α) (φ ∘ vQ)
    (fun _ => by simp [vQ]) hspec.2.2
    (hspec.2.1.trans (totalDegree_map_of_injective Int.cast_injective f).symm)
  refine ⟨a, fun i => by rw [abs_of_nonneg (ha i).1]; exact_mod_cast (ha i).2, ?_⟩
  rw [AbsolutelyIrreducible, graphRestr_map,
    show (Int.castRingHom (AlgebraicClosure ℚ)) ∘ a = φ ∘ α by funext i; simp [φ, α]]
  exact hgood

private theorem AffineHypersurfaceGrowth.succ {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    AffineHypersurfaceGrowth (n + 1) (e + 3) := by
  classical
  obtain ⟨K₀, hK₀, hbound⟩ := h
  rw [show n + 3 = 3 + n by omega] at hbound
  unfold AffineHypersurfaceGrowth
  rw [show n + 1 + 3 = 3 + n + 1 by omega]
  set m := 3 + n
  refine ⟨(4 * (m + 1 : ℕ) + 1) * K₀, by positivity, fun f hir hd B hB => ?_⟩
  set d := f.totalDegree
  let e₀ : Fin (m + 1) ≃ Option (Fin m) := _root_.finSuccEquiv m
  let F := rename e₀ f
  have hFd : F.totalDegree = d := totalDegree_renameEquiv e₀ f
  have hFtop : AbsolutelyIrreducible (homogeneousComponent d F) := by
    rw [AbsolutelyIrreducible, ← rename_homogeneousComponent, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv _ e₀)).mpr hir
  obtain ⟨a, ha, hgir0⟩ := exists_good_int_hyperplane (homogeneousComponent d F) d (by omega)
    (homogeneousComponent_isHomogeneous _ _) hFtop
  let shift (k : ℤ) : MvPolynomial (Option (Fin m)) ℤ →ₐ[ℤ] MvPolynomial (Option (Fin m)) ℤ :=
    aeval fun o => o.elim (X none + C k) fun j => X (some j)
  let g (k : ℤ) : MvPolynomial (Fin m) ℤ := graphRestr a (shift k F)
  have hgtop (k : ℤ) : homogeneousComponent d (g k) = graphRestr a (homogeneousComponent d F) := by
    rw [← graphRestr_homogeneousComponent]
    congr 1
    apply rename_injective e₀.symm e₀.symm.injective
    have hsh : rename e₀.symm (shift k F) = affineTranslation ℤ (Fin.cons k 0) (rename e₀.symm F) := by
      have he : (rename e₀.symm).toRingHom.comp (shift k).toRingHom =
          (affineTranslation ℤ (Fin.cons k (0 : Fin m → ℤ))).toRingHom.comp (rename e₀.symm).toRingHom :=
        MvPolynomial.ringHom_ext (fun _ => by simp [shift, affineTranslation]) fun o => by
          cases o <;> simp [e₀, shift, affineTranslation]
      exact RingHom.congr_fun he F
    rw [rename_homogeneousComponent, hsh, rename_homogeneousComponent]
    have hdeg' : (rename e₀.symm F).totalDegree = d := (totalDegree_renameEquiv e₀.symm F).trans hFd
    simpa only [affineTranslation_totalDegree, hdeg'] using
      affineTranslation_leading_homogeneousComponent (Fin.cons k 0) (rename e₀.symm F)
  have hgdeg (k : ℤ) : (g k).totalDegree = d := by
    refine le_antisymm ?_ ?_
    · rw [← hFd]
      have heq : g k = eval₂Hom C (fun o => o.elim ((∑ j, C (a j) * X j) + C k) X) F := by
        have he : (graphRestr a).toRingHom.comp (shift k).toRingHom =
            eval₂Hom C (fun o => o.elim ((∑ j, C (a j) * X j) + C k) X) :=
          MvPolynomial.ringHom_ext (fun _ => by simp [graphRestr, shift]) fun o => by
            cases o <;> simp [graphRestr, shift]
        exact RingHom.congr_fun he F
      rw [heq]
      refine linear_eval₂_totalDegree_le (RingHom.id ℤ) _ (fun o => ?_) F
      cases o
      · refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
        exact totalDegree_finsetSum_le fun _ _ =>
          (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
      · simp
    · by_contra hlt
      have hz := homogeneousComponent_eq_zero d (g k) (by omega)
      rw [hgtop] at hz
      dsimp only [AbsolutelyIrreducible] at hgir0
      exact hgir0.ne_zero (by rw [hz, map_zero])
  have hgir (k : ℤ) : HasAbsIrreducibleTopForm (g k) := by
    rw [HasAbsIrreducibleTopForm, hgdeg, hgtop]; exact hgir0
  let S := integralPoints (zeroLocus (map (Int.castRingHom ℚ) f)) B
  let lvl (x : IntPoint (m + 1)) : ℤ := x 0 - ∑ i : Fin m, a i * x i.succ
  have hcard : S.card = ∑ k ∈ S.image lvl, (S.filter (lvl · = k)).card :=
    Finset.card_eq_sum_card_image lvl S
  have hfiber (k : ℤ) : ((S.filter (lvl · = k)).card : ℝ) ≤ K₀ * (d : ℝ) ^ e * B ^ (n + 1) := by
    have hle : (S.filter (lvl · = k)).card ≤ count (zeroLocus (map (Int.castRingHom ℚ) (g k))) B := by
      refine Finset.card_le_card_of_injOn Fin.tail (fun x hx => ?_) (fun x hx y hy hxy => ?_)
      · obtain ⟨hxS, hxk⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxB, hxf⟩ := mem_integralPoints.mp hxS
        refine mem_integralPoints.mpr ⟨fun i => hxB i.succ, ?_⟩
        change eval (rationalPoint (Fin.tail x)) (map (Int.castRingHom ℚ) (g k)) = 0
        have hgZ : eval (Fin.tail x) (g k) = 0 := by
          have hshift_ev : eval (Fin.tail x) (g k) =
              eval (fun o => o.elim ((∑ j, a j * x j.succ) + k) (Fin.tail x)) F := by
            rw [show g k = graphRestr a (shift k F) from rfl, graphRestr_eval]
            have he : (eval (fun o => o.elim (∑ j, a j * x j.succ) (Fin.tail x))).comp
                (shift k).toRingHom =
                eval (fun o => o.elim ((∑ j, a j * x j.succ) + k) (Fin.tail x)) :=
              MvPolynomial.ringHom_ext (fun _ => by simp [shift]) fun o => by
                cases o <;> simp [shift, Fin.tail]
            exact RingHom.congr_fun he F
          rw [hshift_ev, show F = rename e₀ f from rfl, eval_rename,
            show (fun o => o.elim ((∑ j, a j * x j.succ) + k) (Fin.tail x)) ∘ e₀ = x by
              funext j; refine Fin.cases ?_ (fun i => rfl) j
              simp only [Function.comp_apply, e₀, _root_.finSuccEquiv_zero, Option.elim_none]
              dsimp only [lvl, m] at hxk ⊢; omega]
          exact Int.cast_injective (α := ℚ) ((map_eval (Int.castRingHom ℚ) x f).trans hxf)
        exact (map_eval (Int.castRingHom ℚ) (Fin.tail x) (g k)).symm.trans (by simp [hgZ])
      · ext j
        refine Fin.cases ?_ (fun i => congrFun hxy i) j
        have hxk := (Finset.mem_filter.mp hx).2
        have hyk := (Finset.mem_filter.mp hy).2
        have hsum : ∑ i : Fin m, a i * x i.succ = ∑ i : Fin m, a i * y i.succ :=
          Finset.sum_congr rfl fun i _ => by rw [show x i.succ = y i.succ from congrFun hxy i]
        dsimp only [lvl] at hxk hyk; omega
    exact (Nat.cast_le.mpr hle).trans (by simpa only [hgdeg k] using hbound (g k) (hgir k) (by rw [hgdeg]; omega) B hB)
  set R : ℝ := (m + 1 : ℕ) * (2 * (d : ℝ) ^ 3) * B
  have hR0 : 0 ≤ R := by positivity
  have hlvl_card : ((S.image lvl).card : ℝ) ≤ 2 * R + 1 := by
    have hsub : S.image lvl ⊆ Finset.Icc (-⌊R⌋) ⌊R⌋ := by
      intro _ hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      have hxB := (mem_integralPoints.mp hx).1
      have habs : |(lvl x : ℝ)| ≤ R := by
        dsimp only [lvl]
        push_cast
        have h1 : |(x 0 : ℝ) - ∑ i : Fin m, (a i : ℝ) * (x i.succ : ℝ)| ≤
            |(x 0 : ℝ)| + ∑ i : Fin m, |(a i : ℝ)| * |(x i.succ : ℝ)| :=
          (abs_sub _ _).trans (add_le_add le_rfl
            ((Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun _ _ => abs_mul _ _)))
        have h2 : ∑ i : Fin m, |(a i : ℝ)| * |(x i.succ : ℝ)| ≤
            ∑ _ : Fin m, (2 * (d : ℝ) ^ 3) * B := Finset.sum_le_sum fun i _ =>
          mul_le_mul (by exact_mod_cast ha i) (hxB i.succ) (abs_nonneg _) (by positivity)
        have hd1 : (1 : ℝ) ≤ d ^ 3 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ d by omega))
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
        dsimp only [R]; push_cast; nlinarith [hxB 0]
      exact Finset.mem_Icc.mpr ⟨by
        have hneg : ((-lvl x : ℤ) : ℝ) ≤ R := by
          simpa only [Int.cast_neg] using (neg_le_abs _).trans habs
        have := Int.le_floor.mpr hneg; omega,
        Int.le_floor.mpr ((le_abs_self _).trans habs)⟩
    have hc := Finset.card_le_card hsub
    rw [Int.card_Icc] at hc
    have hfl : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR0
    have hcZ : ((S.image lvl).card : ℤ) ≤ 2 * ⌊R⌋ + 1 := by
      have : ((S.image lvl).card : ℤ) ≤ ((⌊R⌋ + 1 - -⌊R⌋).toNat : ℤ) := mod_cast hc
      rw [Int.toNat_of_nonneg (by omega)] at this; omega
    calc ((S.image lvl).card : ℝ) ≤ (2 * ⌊R⌋ + 1 : ℤ) := mod_cast hcZ
      _ ≤ 2 * R + 1 := by push_cast; linarith [Int.floor_le R]
  change (S.card : ℝ) ≤ _
  rw [hcard, Nat.cast_sum]
  have hK0 : 0 ≤ K₀ * (d : ℝ) ^ e * B ^ (n + 1) := by positivity
  have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ d by omega))
  calc (∑ k ∈ S.image lvl, ((S.filter (lvl · = k)).card : ℝ))
      ≤ ∑ _ ∈ S.image lvl, K₀ * (d : ℝ) ^ e * B ^ (n + 1) := Finset.sum_le_sum fun k _ => hfiber k
    _ = (S.image lvl).card * (K₀ * (d : ℝ) ^ e * B ^ (n + 1)) := by simp
    _ ≤ (2 * R + 1) * (K₀ * (d : ℝ) ^ e * B ^ (n + 1)) := mul_le_mul_of_nonneg_right hlvl_card hK0
    _ ≤ ((4 * (m + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B) * (K₀ * (d : ℝ) ^ e * B ^ (n + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ hK0
        dsimp only [R]; nlinarith [one_le_mul_of_one_le_of_one_le hd3 hB]
    _ = _ := by rw [pow_add, pow_succ]; ring

theorem affineHypersurfaceGrowth : ∀ n : ℕ, AffineHypersurfaceGrowth n (18 + 3 * n)
  | 0 => by simpa only [AffineHypersurfaceGrowth, Nat.zero_add, pow_one] using affine_surface_dimension_growth
  | n + 1 => by simpa only [Nat.mul_succ, ← Nat.add_assoc] using (affineHypersurfaceGrowth n).succ

theorem AffineHypersurfaceGrowth.rational {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    RationalAffineHypersurfaceGrowth n e := by
  classical
  obtain ⟨K₀, hK₀, hbound⟩ := h
  refine ⟨K₀, hK₀, fun f hir hd B hB => ?_⟩
  have hf : f ≠ 0 := fun hz => hir.ne_zero (by simp [hz])
  obtain ⟨g, r, _, hr, he⟩ := exists_primitive_integer_model f hf
  have hdeg := rational_scalar_model_degree hr hf he
  let φ : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hmodel : map (Int.castRingHom (AlgebraicClosure ℚ)) g = C (φ r) * map φ f := by
    simpa only [map_mul, map_C, map_map, show φ.comp (Int.castRingHom ℚ) = Int.castRingHom _ by ext; simp]
      using congrArg (map φ) he
  have htop : HasAbsIrreducibleTopForm g := by
    rw [HasAbsIrreducibleTopForm, AbsolutelyIrreducible, map_homogeneousComponent, hmodel,
      homogeneousComponent_C_mul, hdeg, ← map_homogeneousComponent]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ((map_ne_zero_iff φ φ.injective).mpr hr)).map C)).mpr hir
  have hpts : integralPoints (zeroLocus (map (Int.castRingHom ℚ) g)) B =
      integralPoints (zeroLocus f) B := by
    ext x; simp only [mem_integralPoints, zeroLocus, Set.mem_ofPred_eq]
    have hx : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = (eval x g : ℚ) :=
      (map_eval (Int.castRingHom ℚ) x g).symm
    rw [hx, Int.cast_eq_zero]
    exact and_congr_right' ⟨fun h0 => (rational_scalar_model_zero_iff hr he (rationalPoint x)).mp
        (hx.trans (by simp [h0])),
      fun h0 => Int.cast_injective (α := ℚ) (hx.symm.trans
        ((rational_scalar_model_zero_iff hr he (rationalPoint x)).mpr h0))⟩
  simpa only [hdeg, count, hpts] using hbound g htop (by omega) B hB

end
end CCDN
