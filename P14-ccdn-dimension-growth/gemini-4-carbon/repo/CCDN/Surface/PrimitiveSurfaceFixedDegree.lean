module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Curve.AffineCurveCount
import CCDN.Determinant.PlaneSingularities
import CCDN.Height.IntegerCoefficientHeight
import CCDN.Height.PolynomialBoxHeight
import CCDN.Hypersurface.NonabsoluteSurfaceCount
import CCDN.Hypersurface.SingularHypersurfaceCount
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.CongruenceFamily
import CCDN.Surface.CongruencePrimeWindow
import CCDN.Surface.CurveComponents
import CCDN.Surface.CurveCrossing
import CCDN.Surface.DegreeOneCount
import CCDN.Surface.TopFormBadPrimes
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private def surfaceResidueLogBudget (B L : ℝ) : ℝ :=
  1 + Real.log B + (Real.log 4 + 4) * scalingPrimeRatio * L

private lemma exp_sum_log_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, Real.log p) = ∏ p ∈ P, (p : ℝ) := by
  rw [Real.exp_sum]
  exact prod_congr rfl fun p hp => Real.exp_log (mod_cast (hP p hp).pos)

private theorem exists_minimal_product_subset (P : Finset ℕ) {X U : ℝ}
    (hX : 1 < X) (hP : ∀ p ∈ P, (0 : ℝ) < p) (hU : ∀ p ∈ P, (p : ℝ) ≤ U)
    (hprod : X ≤ ∏ p ∈ P, (p : ℝ)) :
    ∃ R : Finset ℕ, R ⊆ P ∧ X ≤ ∏ p ∈ R, (p : ℝ) ∧
      (∀ T ⊂ R, (∏ p ∈ T, (p : ℝ)) < X) ∧ (∏ p ∈ R, (p : ℝ)) < U * X := by
  classical
  let S := P.powerset.filter fun R : Finset ℕ => X ≤ ∏ p ∈ R, (p : ℝ)
  obtain ⟨R, hRS, hmin⟩ := S.exists_min_image Finset.card
    ⟨P, mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hprod⟩⟩
  obtain ⟨hRP, hRX⟩ := mem_filter.mp hRS
  have hRP' : R ⊆ P := mem_powerset.mp hRP
  have hRne : R.Nonempty := nonempty_iff_ne_empty.mpr fun he => by
    simp only [he, prod_empty] at hRX; linarith
  have hproper (T) (hTR : T ⊂ R) : (∏ p ∈ T, (p : ℝ)) < X := by
    by_contra hn
    exact (not_le_of_gt (card_lt_card hTR))
      (hmin T (mem_filter.mpr ⟨mem_powerset.mpr (hTR.subset.trans hRP'), le_of_not_gt hn⟩))
  obtain ⟨p, hp⟩ := hRne
  have hmul := mul_lt_mul_of_pos_left (hproper (R.erase p) (erase_ssubset hp)) (hP p (hRP' hp))
  rw [mul_prod_erase R _ hp] at hmul
  exact ⟨R, hRP', hRX, hproper, hmul.trans_le (mul_le_mul_of_nonneg_right (hU p (hRP' hp)) (by linarith))⟩

private theorem exists_subset_erase_boundary {α : Type*} [DecidableEq α] (R : Finset α)
    (W : Finset α → Prop) (hempty : ¬ W ∅) (hR : W R) :
    ∃ T : Finset α, T ⊆ R ∧ ∃ p ∈ T, W T ∧ ¬ W (T.erase p) := by
  classical
  let S := R.powerset.filter W
  obtain ⟨T, hTS, hmin⟩ := S.exists_min_image Finset.card
    ⟨R, mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hR⟩⟩
  obtain ⟨hTR, hWT⟩ := mem_filter.mp hTS
  obtain ⟨p, hp⟩ : T.Nonempty := nonempty_iff_ne_empty.mpr (by rintro rfl; exact hempty hWT)
  refine ⟨T, mem_powerset.mp hTR, p, hp, hWT, fun he => ?_⟩
  exact (not_le_of_gt (card_lt_card (erase_ssubset hp)))
    (hmin _ (mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset p T).trans (mem_powerset.mp hTR)), he⟩))

private theorem exists_smooth_prime_window_subset
    (f : MvPolynomial (Fin 3) ℤ) {H B L : ℝ} (hH : 1 ≤ H) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : 4 * Real.log ((f.totalDegree : ℝ) + 1) + Real.log H + f.totalDegree * Real.log B ≤ L)
    (x : IntPoint 3) (hx : InBox x B) (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ P : Finset ℕ, P ⊆ congruencePrimeWindow L ∧ Real.exp L ≤ ∏ p ∈ P, (p : ℝ) ∧
      ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
        (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := hsmooth
  have hH0 : 0 < H := by linarith
  have hB0 : 0 < B := by linarith
  have hpd_coeff : CoefficientHeightLE (pderiv j f) (((f.totalDegree : ℝ) + 1) * H) := fun e => by
    rw [coeff_pderiv]
    by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
    · simp only [hz, zero_mul, Int.cast_zero, abs_zero]; positivity
    · have he : e j + 1 ≤ f.totalDegree := by
        simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using
          (degreeOf_le_iff.mp (degreeOf_le_totalDegree f j)) _ (mem_support_iff.mpr hz)
      push_cast; rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (e j : ℝ) + 1)]
      have heR : (e j : ℝ) + 1 ≤ (f.totalDegree : ℝ) + 1 := mod_cast (by omega : e j + 1 ≤ f.totalDegree + 1)
      calc |(f.coeff (e + Finsupp.single j 1) : ℝ)| * ((e j : ℝ) + 1)
          ≤ H * ((e j : ℝ) + 1) := mul_le_mul_of_nonneg_right (hcoeff _) (by positivity)
        _ ≤ H * ((f.totalDegree : ℝ) + 1) := mul_le_mul_of_nonneg_left heR hH0.le
        _ = ((f.totalDegree : ℝ) + 1) * H := mul_comm _ _
  have hb := polynomial_eval₂_box_bound (pderiv j f) (((f.totalDegree : ℝ) + 1) * H) B
    (by positivity) hB hpd_coeff (fun i => (x i : ℝ)) hx
  have heval : (eval x (pderiv j f) : ℝ) =
      eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) (pderiv j f) := by
    simpa only [eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
      eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
  rw [← heval, Fintype.card_fin] at hb
  have hdeg : (pderiv j f).totalDegree ≤ f.totalDegree := by
    rw [← rational_map_totalDegree (pderiv j f), ← pderiv_map]
    exact (pderiv_totalDegree_le (map (Int.castRingHom ℚ) f) j).trans
      (by rw [rational_map_totalDegree]; omega)
  have hdegR : ((pderiv j f).totalDegree : ℝ) ≤ f.totalDegree := mod_cast hdeg
  have hev_le : |(eval x (pderiv j f) : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) ^ 4 * H * B ^ f.totalDegree :=
    hb.trans ((show (((pderiv j f).totalDegree : ℝ) + 1) ^ 3 * (((f.totalDegree : ℝ) + 1) * H) *
        B ^ (pderiv j f).totalDegree ≤ ((f.totalDegree : ℝ) + 1) ^ 3 *
          (((f.totalDegree : ℝ) + 1) * H) * B ^ f.totalDegree by gcongr).trans_eq (by ring))
  have hdpos : (0 : ℝ) < (f.totalDegree : ℝ) + 1 := by positivity
  have hlog := Real.log_le_log (abs_pos.mpr (mod_cast hj)) hev_le
  rw [Real.log_mul (mul_pos (pow_pos hdpos _) hH0).ne' (pow_pos hB0 _).ne',
    Real.log_mul (pow_pos hdpos _).ne' hH0.ne', Real.log_pow, Real.log_pow] at hlog
  have hbound : Real.log |(eval x (pderiv j f) : ℝ)| ≤ L := (by push_cast at hlog; linarith)
  let P := (congruencePrimeWindow L).filter fun p : ℕ => ¬ (p : ℤ) ∣ eval x (pderiv j f)
  refine ⟨P, filter_subset _ _, congruencePrimeWindow_avoiding_product hL hj hbound, fun p hp => ⟨j, ?_⟩⟩
  have he : eval (fun i => (x i : ZMod p)) (pderiv j (map (Int.castRingHom (ZMod p)) f)) =
      (eval x (pderiv j f) : ZMod p) := by
    rw [pderiv_map]; exact (map_eval (Int.castRingHom (ZMod p)) x (pderiv j f)).symm
  rw [he]
  exact fun h => (mem_filter.mp hp).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)

open Classical in
private def surfaceResidueCrossing {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) : Set (RatPoint 3) :=
  let g := map (Int.castRingHom ℚ)
    (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq)) (r.restrict (erase_subset p R)))
  let h := map (Int.castRingHom ℚ) (F.auxiliary R hR r)
  ⋃ I ∈ S.filter (fun I => g ∈ I ∧ h ∉ I), idealZeroLocus I ∩ zeroLocus h

private def surfaceResidueSubsetLocus {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (L X : ℝ) (hL : 1 ≤ L) (R : Finset ℕ) : Set (RatPoint 3) :=
  if hR : R ⊆ congruencePrimeWindow L then
    if (∏ p ∈ R, (p : ℝ)) ≤ scalingPrimeRatio * L * X then
      ⋃ p ∈ R, ⋃ r : SmoothAffineResidueFamily f R,
        surfaceResidueCrossing F S R
          (fun _q hq => ((mem_congruencePrimeWindow hL).mp (hR hq)).1) p r
    else ∅
  else ∅

private def surfaceResidueResidualLocus {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (L X : ℝ) (hL : 1 ≤ L) : Set (RatPoint 3) :=
  ⋃ R ∈ (congruencePrimeWindow L).powerset, surfaceResidueSubsetLocus F S L X hL R

private lemma SurfaceCongruenceFamily.scaled_degree_le
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (R : Finset ℕ) (hRW : R ⊆ congruencePrimeWindow L)
    (hR : ∀ p ∈ R, p.Prime) (r : SmoothAffineResidueFamily f R) :
    ((F.auxiliary R hR r).totalDegree : ℝ) * (∏ p ∈ R, (p : ℝ)) ≤
      A * (X + ∏ p ∈ R, (p : ℝ)) * surfaceResidueLogBudget B L := by
  have hlogB := Real.log_nonneg hB
  have hQ : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg fun p _ => Real.log_natCast_nonneg p
  have hlog : ∑ p ∈ R, Real.log p ≤ (Real.log 4 + 4) * scalingPrimeRatio * L :=
    (sum_le_sum_of_subset_of_nonneg hRW fun p _ _ => Real.log_natCast_nonneg p).trans
      (congruencePrimeWindow_log_upper hL)
  have hq : 0 < ∏ p ∈ R, (p : ℝ) := prod_pos fun p hp => mod_cast (hR p hp).pos
  have hX0 : 0 ≤ X := (Real.rpow_nonneg (by linarith) _).trans hX
  have hd := F.degree_le R hR r
  rw [exp_sum_log_primes R hR] at hd
  have hh := mul_le_mul_of_nonneg_right hd hq.le
  rw [show A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) / (∏ p ∈ R, (p : ℝ)) + 1) *
    (1 + Real.log B + ∑ p ∈ R, Real.log p) * (∏ p ∈ R, (p : ℝ)) =
    A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + ∏ p ∈ R, (p : ℝ)) *
      (1 + Real.log B + ∑ p ∈ R, Real.log p) by field_simp] at hh
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left
      (show B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + ∏ p ∈ R, (p : ℝ) ≤ X + ∏ p ∈ R, (p : ℝ) by linarith) hA)
    (by dsimp [surfaceResidueLogBudget]; linarith) (by positivity) (by positivity))

private theorem surface_residue_residual_count_le
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hd : 1 ≤ f.totalDegree) (hX0 : 0 ≤ X) (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3))) (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I)) :
    (count (surfaceResidueResidualLocus F S L X hL) B : ℝ) ≤
      2 * f.totalDegree * A ^ 2 * (surfaceResidueLogBudget B L) ^ 2 *
        (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2 *
        (congruencePrimeWindow L).card *
        (2 * f.totalDegree : ℝ) ^ (congruencePrimeWindow L).card := by
  classical
  let W := congruencePrimeWindow L
  let K₀ : ℝ := 2 * f.totalDegree * A ^ 2 * (surfaceResidueLogBudget B L) ^ 2 *
    (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2
  have hK0 : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hdR : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
  have hsubset (R : Finset ℕ) (hRW : R ∈ W.powerset) :
      (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) ≤
        K₀ * W.card * (f.totalDegree : ℝ) ^ W.card := by
    have hRW' : R ⊆ congruencePrimeWindow L := mem_powerset.mp hRW
    have hcard : R.card ≤ W.card := card_le_card hRW'
    have hR (p : ℕ) (hp : p ∈ R) : p.Prime := ((mem_congruencePrimeWindow hL).mp (hRW' hp)).1
    by_cases hq : (∏ p ∈ R, (p : ℝ)) ≤ scalingPrimeRatio * L * X
    · have hedge (p : ℕ) (hp : p ∈ R) :
          (count (⋃ r : SmoothAffineResidueFamily f R,
            surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
          K₀ * (f.totalDegree : ℝ) ^ R.card := by
        let (t : R) : NeZero t.val := ⟨(hR t.val t.property).ne_zero⟩
        let : Fintype (SmoothAffineResidueFamily f R) := Pi.instFintype
        let q : ℝ := ∏ t ∈ R, (t : ℝ)
        have hqpos : 0 < q := prod_pos fun t ht => mod_cast (hR t ht).pos
        have hpt (r : SmoothAffineResidueFamily f R) :
            (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2 ≤ K₀ := by
          let U := scalingPrimeRatio * L
          let T := surfaceResidueLogBudget B L
          let g := F.auxiliary (R.erase p) (fun t ht => hR t (mem_of_mem_erase ht))
            (r.restrict (erase_subset p R))
          let h := F.auxiliary R hR r
          have hU : 0 ≤ U := by dsimp [U]; have := scalingPrimeRatio_one_le; positivity
          have hT : 0 ≤ T := by
            dsimp [T, surfaceResidueLogBudget]
            have := scalingPrimeRatio_one_le
            have := Real.log_nonneg hB
            have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
            positivity
          have hpU : (p : ℝ) ≤ U := ((mem_congruencePrimeWindow hL).mp (hRW' hp)).2.2
          have hqp : (∏ t ∈ R.erase p, (t : ℝ)) * p = q := prod_erase_mul R _ hp
          have hpar := mul_le_mul_of_nonneg_right
            (F.scaled_degree_le hA hB hL hX (R.erase p) ((erase_subset p R).trans hRW')
              (fun t ht => hR t (mem_of_mem_erase ht)) (r.restrict (erase_subset p R)))
            (Nat.cast_nonneg (α := ℝ) p)
          have hpar' : (g.totalDegree : ℝ) * q ≤ A * (2 * (U + 1) * X) * T := by
            have h1 : (g.totalDegree : ℝ) * q ≤ A * (X * p + q) * T := by
              calc (g.totalDegree : ℝ) * q
                  = (g.totalDegree : ℝ) * (∏ t ∈ R.erase p, (t : ℝ)) * p := by rw [mul_assoc, hqp]
                _ ≤ _ := hpar
                _ = A * (X * p + q) * T := by dsimp [T]; rw [← hqp]; ring
            have hxp : X * p + q ≤ 2 * (U + 1) * X := by
              change q ≤ U * X at hq; nlinarith [mul_le_mul_of_nonneg_left hpU hX0]
            exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxp hA) hT)
          have hch' : (h.totalDegree : ℝ) * q ≤ A * ((U + 1) * X) * T :=
            (F.scaled_degree_le hA hB hL hX R hRW' hR r).trans
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (by change q ≤ U * X at hq; linarith) hA) hT)
          have hpair := mul_le_mul hpar' hch' (by dsimp [q]; positivity) (by positivity)
          have hcr_le : (count (surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
              (f.totalDegree : ℝ) * g.totalDegree * h.totalDegree := by
            have hh := surface_curve_crossing_count_le (map (Int.castRingHom ℚ) f)
              (map (Int.castRingHom ℚ) g) (map (Int.castRingHom ℚ) h) hir (F.proper _ _ _)
              (S.filter fun I => map (Int.castRingHom ℚ) g ∈ I) δ
              (fun I hI => ⟨hS I (mem_filter.mp hI).1, (mem_filter.mp hI).2⟩) B
            rw [show (S.filter fun I => map (Int.castRingHom ℚ) g ∈ I).filter
              (fun I => map (Int.castRingHom ℚ) h ∉ I) =
              S.filter fun I => map (Int.castRingHom ℚ) g ∈ I ∧ map (Int.castRingHom ℚ) h ∉ I by
              ext; simp only [mem_filter]; tauto,
              rational_map_totalDegree, rational_map_totalDegree, rational_map_totalDegree] at hh
            exact_mod_cast hh
          have hc := mul_le_mul_of_nonneg_right hcr_le (sq_nonneg q)
          have hm := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (α := ℝ) f.totalDegree)
          dsimp [K₀, U, T, q] at hc hm ⊢; nlinarith [hc, hm]
        have hun : (count (⋃ r : SmoothAffineResidueFamily f R,
            surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
            ∑ r : SmoothAffineResidueFamily f R, (count (surfaceResidueCrossing F S R hR p r) B : ℝ) := by
          have hh := count_biUnion_finset_le (univ : Finset (SmoothAffineResidueFamily f R))
            (fun r => surfaceResidueCrossing F S R hR p r) B
          exact_mod_cast (by simpa only [Finset.mem_univ, Set.iUnion_true] using hh)
        have hcard_r : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
            (f.totalDegree : ℝ) ^ R.card * q ^ 2 := by
          have hh := smoothAffineResidueFamily_card_le (n := 2) f R hR
          rw [Nat.card_eq_fintype_card] at hh
          have hhR : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
              ((f.totalDegree ^ R.card * (∏ p ∈ R, p) ^ 2 : ℕ) : ℝ) := mod_cast hh
          simpa only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using hhR
        refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hqpos)
        calc (count (⋃ r : SmoothAffineResidueFamily f R,
              surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2
            ≤ (∑ r : SmoothAffineResidueFamily f R,
                (count (surfaceResidueCrossing F S R hR p r) B : ℝ)) * q ^ 2 :=
              mul_le_mul_of_nonneg_right hun (sq_nonneg q)
          _ = ∑ r : SmoothAffineResidueFamily f R,
                (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2 := sum_mul _ _ _
          _ ≤ ∑ _r : SmoothAffineResidueFamily f R, K₀ := sum_le_sum fun r _ => hpt r
          _ = (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) * K₀ := by simp
          _ ≤ ((f.totalDegree : ℝ) ^ R.card * q ^ 2) * K₀ := mul_le_mul_of_nonneg_right hcard_r hK0
          _ = K₀ * (f.totalDegree : ℝ) ^ R.card * q ^ 2 := by ring
      have hcntR : (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) ≤
          ∑ p ∈ R, (count (⋃ r : SmoothAffineResidueFamily f R,
            surfaceResidueCrossing F S R hR p r) B : ℝ) := by
        simp only [surfaceResidueSubsetLocus, dite_eq_left hRW', ite_eq_left hq]
        exact_mod_cast count_biUnion_finset_le R
          (fun p => ⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B
      calc (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ)
          ≤ ∑ _p ∈ R, K₀ * (f.totalDegree : ℝ) ^ R.card := hcntR.trans (sum_le_sum hedge)
        _ = K₀ * R.card * (f.totalDegree : ℝ) ^ R.card := by simp; ring
        _ ≤ K₀ * W.card * (f.totalDegree : ℝ) ^ W.card :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mod_cast hcard) hK0)
            (pow_le_pow_right₀ hdR hcard) (by positivity) (by positivity)
    · simp only [surfaceResidueSubsetLocus, dite_eq_left hRW', ite_eq_right hq]
      have hz : count (∅ : Set (RatPoint 3)) B = 0 := by simp [count, integralPoints]
      rw [hz, Nat.cast_zero]; positivity
  calc (count (surfaceResidueResidualLocus F S L X hL) B : ℝ)
      ≤ ∑ R ∈ W.powerset, (count (surfaceResidueSubsetLocus F S L X hL R) B : ℝ) :=
        mod_cast count_biUnion_finset_le W.powerset (surfaceResidueSubsetLocus F S L X hL) B
    _ ≤ ∑ _R ∈ W.powerset, K₀ * W.card * (f.totalDegree : ℝ) ^ W.card := sum_le_sum hsubset
    _ = (2 : ℝ) ^ W.card * (K₀ * W.card * (f.totalDegree : ℝ) ^ W.card) := by
        simp only [sum_const, card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = _ := by dsimp [K₀, W]; rw [mul_pow]; ring

private theorem large_curve_point_mem_surfaceResidueResidualLocus
    (f : MvPolynomial (Fin 3) ℤ) (hir : Irreducible (map (Int.castRingHom ℚ) f))
    {A B H L X : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcoeff : CoefficientHeightLE f H)
    (hlog_win : 4 * Real.log ((f.totalDegree : ℝ) + 1) + Real.log H + f.totalDegree * Real.log B ≤ L)
    (hX1 : 1 < X) (hBX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X) (hXL : X ≤ Real.exp L)
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (I : Ideal (CoordinatePolynomial 3)) (hIS : I ∈ S) {d : ℕ}
    (hI : IsSurfaceCurve (map (Int.castRingHom ℚ) f) I d)
    (hinitI : map (Int.castRingHom ℚ) F.initial ∈ I)
    (hlarge : 2 * f.totalDegree * A * surfaceResidueLogBudget B L < d)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)
    (hxI : rationalPoint x ∈ idealZeroLocus I) (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    rationalPoint x ∈ surfaceResidueResidualLocus F S L X hL := by
  classical
  obtain ⟨P, hPW, hPprod, hPsmooth⟩ :=
    exists_smooth_prime_window_subset f hH hB hL hcoeff hlog_win x hx hsmooth
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime := ((mem_congruencePrimeWindow hL).mp (hPW hp)).1
  obtain ⟨R₀, hR₀P, hR₀prod, _, hR₀upper⟩ := exists_minimal_product_subset P hX1
    (fun p hp => mod_cast (hPprime p hp).pos)
    (fun p hp => ((mem_congruencePrimeWindow hL).mp (hPW hp)).2.2) (hXL.trans hPprod)
  have hR₀W : R₀ ⊆ congruencePrimeWindow L := hR₀P.trans hPW
  have hR₀prime (q : ℕ) (hq : q ∈ R₀) : q.Prime := hPprime q (hR₀P hq)
  have hR₀smooth (q : ℕ) (hq : q ∈ R₀) := hPsmooth q (hR₀P hq)
  let aux (T : Finset ℕ) : MvPolynomial (Fin 3) ℤ :=
    if hT : T ⊆ R₀ then F.auxiliary T (fun q hq => hR₀prime q (hT hq))
      (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) else 1
  have haux (T : Finset ℕ) (hT : T ⊆ R₀) :
      aux T = F.auxiliary T (fun q hq => hR₀prime q (hT hq))
        (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) := by
    simp only [aux, dite_eq_left hT]
  have hterminal : map (Int.castRingHom ℚ) (aux R₀) ∉ I := fun hmem => by
    rw [haux R₀ Subset.rfl] at hmem
    let r₀ := smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth
    have hQ : 0 ≤ ∑ p ∈ R₀, Real.log p := sum_nonneg fun p _ => Real.log_natCast_nonneg p
    have hlogB := Real.log_nonneg hB
    have hlog : ∑ p ∈ R₀, Real.log p ≤ (Real.log 4 + 4) * scalingPrimeRatio * L :=
      (sum_le_sum_of_subset_of_nonneg hR₀W fun p _ _ => Real.log_natCast_nonneg p).trans
        (congruencePrimeWindow_log_upper hL)
    have hden : 0 < ∏ p ∈ R₀, (p : ℝ) := prod_pos fun p hp => mod_cast (hR₀prime p hp).pos
    have hratio : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) / Real.exp (∑ p ∈ R₀, Real.log p) ≤ 1 := by
      rw [exp_sum_log_primes R₀ hR₀prime]; exact (div_le_one hden).mpr (hBX.trans hR₀prod)
    have hdeg : ((F.auxiliary R₀ hR₀prime r₀).totalDegree : ℝ) ≤
        2 * A * surfaceResidueLogBudget B L :=
      (F.degree_le R₀ hR₀prime r₀).trans
        ((mul_le_mul (mul_le_mul_of_nonneg_left
          (show B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) / Real.exp (∑ p ∈ R₀, Real.log p) + 1 ≤ 2 by linarith) hA)
          (show 1 + Real.log B + ∑ p ∈ R₀, Real.log p ≤ surfaceResidueLogBudget B L by
            dsimp [surfaceResidueLogBudget]; linarith) (by positivity) (by positivity)).trans_eq
          (by ring))
    have hcurve := surface_prime_curve_degree_sum_le (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (F.auxiliary R₀ hR₀prime r₀)) hir (F.proper _ _ _) {I} (fun _ => d)
      fun Q hQ => by obtain rfl := mem_singleton.mp hQ; exact ⟨hI, hmem⟩
    rw [sum_singleton, rational_map_totalDegree, rational_map_totalDegree] at hcurve
    have hcurveR : (d : ℝ) ≤ (f.totalDegree : ℝ) * (F.auxiliary R₀ hR₀prime r₀).totalDegree :=
      mod_cast hcurve
    nlinarith [mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg (α := ℝ) f.totalDegree)]
  have hempty : ¬ (map (Int.castRingHom ℚ) (aux ∅) ∉ I) := by
    rw [haux ∅ (empty_subset _), F.initial_eq]; exact not_not.mpr hinitI
  obtain ⟨R, hRR₀, p, hp, hchild, hparent⟩ := exists_subset_erase_boundary R₀
    (fun T => map (Int.castRingHom ℚ) (aux T) ∉ I) hempty hterminal
  have hRprime (q : ℕ) (hq : q ∈ R) : q.Prime := hR₀prime q (hRR₀ hq)
  have hRsmooth (q : ℕ) (hq : q ∈ R) := hR₀smooth q (hRR₀ hq)
  let r := smoothResidueFamilyOfPoint x hxf R hRsmooth
  have hRW : R ⊆ congruencePrimeWindow L := hRR₀.trans hR₀W
  have hprod : (∏ q ∈ R, (q : ℝ)) ≤ scalingPrimeRatio * L * X :=
    (prod_le_prod_of_subset_of_one_le₀ hRR₀ (fun _ _ => Nat.cast_nonneg _)
      fun q hq _ => mod_cast (hR₀prime q hq).one_le).trans hR₀upper.le
  refine Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨mem_powerset.mpr hRW, ?_⟩⟩
  simp only [surfaceResidueSubsetLocus, dite_eq_left hRW, ite_eq_left hprod]
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, Set.mem_iUnion.mpr ⟨r, ?_⟩⟩⟩
  refine Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨hIS, ?_, ?_⟩, hxI, ?_⟩⟩
  · have hparEq : aux (R.erase p) = F.auxiliary (R.erase p)
        (fun q hq => hRprime q (mem_of_mem_erase hq)) (r.restrict (erase_subset p R)) := by
      rw [haux (R.erase p) ((erase_subset p R).trans hRR₀)]; rfl
    exact hparEq ▸ not_not.mp hparent
  · rwa [← haux R hRR₀]
  · have hh := congrArg (Int.castRingHom ℚ) (F.point_vanishes x hx hxf R hRprime hRsmooth)
    rwa [map_eval, map_zero] at hh

private theorem congruencePrimeWindow_surface_residual_bound {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 ≤ R) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (d : ℕ), 5 ≤ d → ∀ B : ℝ, 1 ≤ B →
      ((congruencePrimeWindow (K * (Real.log B + 1))).card *
        R ^ (congruencePrimeWindow (K * (Real.log B + 1))).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4 ≤ K₀ * B := by
  let A := (Real.log 4 + 4) * scalingPrimeRatio
  have hA : 0 < A := by
    have := scalingPrimeRatio_one_le
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [A]; positivity
  have hK0 : 0 < K := by linarith
  let R₂ := 2 * R
  have hR2_1 : 1 ≤ R₂ := by dsimp [R₂]; linarith
  have hR2_0 : 0 < R₂ := by linarith
  have hlogR2 : 0 ≤ Real.log R₂ := Real.log_nonneg hR2_1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := A * K * Real.log R₂ / (1 / 40 : ℝ) + 1
  let E := A * Real.exp D / Real.log 2 * Real.log R₂
  let K₁ := Real.exp (E + 1 / 40)
  let K₂ := (Nat.factorial 4 : ℝ) / (1 / 40 : ℝ) ^ 4 * Real.exp (1 / 40)
  have hK1 : 0 < K₁ := Real.exp_pos _
  have hK2 : 0 < K₂ := by dsimp [K₂]; positivity
  refine ⟨K₁ * K₂, mul_pos hK1 hK2, fun d hd B hB => ?_⟩
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  let L := K * (Real.log B + 1)
  let m := (congruencePrimeWindow L).card
  have hL : 1 ≤ L := by dsimp [L]; nlinarith
  have hcard : (m : ℝ) * Real.log L ≤ A * L := congruencePrimeWindow_card_log_bound hL
  have hcard2 : (m : ℝ) * Real.log 2 ≤ A * L := calc
    (m : ℝ) * Real.log 2 = ∑ _p ∈ congruencePrimeWindow L, Real.log 2 := by simp [m]
    _ ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p := sum_le_sum fun p hp =>
      Real.log_le_log (by norm_num) (mod_cast ((mem_congruencePrimeWindow hL).mp hp).1.two_le)
    _ ≤ A * L := congruencePrimeWindow_log_upper hL
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hbound : (m : ℝ) * Real.log R₂ ≤ E + (1 / 40 : ℝ) * (Real.log B + 1) := by
    by_cases hlarge : D ≤ Real.log L
    · have hd_div : A * K * Real.log R₂ / (1 / 40 : ℝ) ≤ Real.log L := by
        dsimp [D] at hlarge; linarith
      have hd' : A * K * Real.log R₂ ≤ (1 / 40 : ℝ) * Real.log L := by
        have hh := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 40)).mp hd_div
        nlinarith
      have hmain : (m : ℝ) * Real.log R₂ ≤ (1 / 40 : ℝ) * (Real.log B + 1) :=
        (mul_le_mul_iff_left₀ (mul_pos hA hK0)).mp
          (by dsimp [L] at hcard; nlinarith [mul_le_mul_of_nonneg_left hd' hm0,
            mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 1 / 40)])
      have hE0 : 0 ≤ E := by dsimp [E]; positivity
      linarith
    · have hLb : L ≤ Real.exp D := by
        simpa only [Real.exp_log (by linarith : 0 < L)] using Real.exp_le_exp.mpr (le_of_not_ge hlarge)
      have hm' : (m : ℝ) ≤ A * Real.exp D / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr (hcard2.trans (mul_le_mul_of_nonneg_left hLb hA.le))
      have hh := mul_le_mul_of_nonneg_right hm' hlogR2
      change (m : ℝ) * Real.log R₂ ≤ E at hh; nlinarith
  have hexp := Real.exp_le_exp.mpr hbound
  rw [← Real.log_pow, Real.exp_log (pow_pos hR2_0 _),
    show Real.exp (E + (1 / 40 : ℝ) * (Real.log B + 1)) = K₁ * B ^ (1 / 40 : ℝ) by
      dsimp [K₁]; rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]; congr 1; ring] at hexp
  have hm_pow : (m : ℝ) * R ^ m ≤ K₁ * B ^ (1 / 40 : ℝ) := calc
    (m : ℝ) * R ^ m ≤ (2 : ℝ) ^ m * R ^ m :=
      mul_le_mul_of_nonneg_right (mod_cast m.lt_two_pow_self.le) (by positivity)
    _ = R₂ ^ m := (mul_pow _ _ _).symm
    _ ≤ K₁ * B ^ (1 / 40 : ℝ) := hexp
  have h₂ := logarithm_add_one_pow_le_rpow 4 (by norm_num : (0 : ℝ) < 1 / 40) hB
  change (Real.log B + 1) ^ 4 ≤ K₂ * B ^ (1 / 40 : ℝ) at h₂
  have h920 := surface_inverse_sqrt_le_nine_twentieths hd
  calc ((m : ℝ) * R ^ m) * B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4
      ≤ (K₁ * B ^ (1 / 40 : ℝ)) * B ^ (2 / Real.sqrt (d : ℝ)) * (K₂ * B ^ (1 / 40 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hm_pow (by positivity)) h₂ (by positivity) (by positivity)
    _ = (K₁ * K₂) * B ^ (2 / Real.sqrt (d : ℝ) + 1 / 20) := by
        have hh : B ^ (1 / 20 : ℝ) = B ^ (1 / 40 : ℝ) * B ^ (1 / 40 : ℝ) := by
          rw [← Real.rpow_add hB0]; norm_num
        rw [Real.rpow_add hB0, hh]; ring
    _ ≤ (K₁ * K₂) * B ^ (1 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB
          (show 2 / Real.sqrt (d : ℝ) + 1 / 20 ≤ 1 by
            rw [show 2 / Real.sqrt (d : ℝ) = 2 * (1 / Real.sqrt (d : ℝ)) by ring]; linarith))
        (mul_pos hK1 hK2).le
    _ = (K₁ * K₂) * B := by rw [Real.rpow_one]

private theorem retained_surface_curve_union_bound :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), HasAbsIrreducibleTopForm f → 5 ≤ f.totalDegree →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (A D B : ℝ),
      0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I) ∧ 0 < δ I) →
      (∀ I ∈ S, (δ I : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ I ∈ S, (δ I : ℝ)) ≤ A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) →
      (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
        K₀ * ((f.totalDegree : ℝ) ^ 6 + A * (D ^ 2 * (D + 1) + 1)) * B := by
  obtain ⟨K_ln, hK_ln, hline⟩ := surface_degree_one_component_contribution
  obtain ⟨K_ac, hK_ac, hac⟩ := affine_curve_count 3 (by omega)
  let K_wt := (Nat.factorial 4 : ℝ) / (1 / 20 : ℝ) ^ 4 * Real.exp (1 / 20)
  let K_cv := K_ac * K_wt
  have hK_cv : 0 < K_cv := by dsimp [K_cv, K_wt]; positivity
  let K_cd := 20 * Real.exp (1 / 20 : ℝ)
  have hK_cd : 0 < K_cd := by dsimp [K_cd]; positivity
  let K₀ := K_ln + K_cv + K_cd
  refine ⟨K₀, by dsimp [K₀]; positivity, fun f hir hd S δ A D B hA hD hB hS hcap hbudget => ?_⟩
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  let lines := S.filter fun I => δ I = 1
  let curves := S.filter fun I => 2 ≤ δ I
  have hlineCount := hline f hir (by omega) B hB0.le lines
    (fun I hI => by
      obtain ⟨hIS, h1⟩ := mem_filter.mp hI
      exact ⟨(hS I hIS).1.isPrime, (hS I hIS).1.height_eq, h1 ▸ (hS I hIS).1.degree⟩)
    (fun I hI => (hS I (mem_filter.mp hI).1).1.mem)
  have hcv_bud : ∑ I ∈ curves, (δ I : ℝ) ≤
      A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity).trans hbudget
  have hcv_pt (I) (hI : I ∈ curves) : curveBound (δ I) B ≤
      (δ I : ℝ) * D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
    have hδ2 : (2 : ℝ) ≤ δ I := mod_cast (mem_filter.mp hI).2
    have hpow : B ^ (1 / (δ I : ℝ)) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (one_div_le_one_div_of_le (by norm_num) hδ2)
    have hδD := hcap I (mem_filter.mp hI).1
    have hsq : (δ I : ℝ) ^ 2 ≤ (D * (Real.log B + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hδD 2
    have hcube : (δ I : ℝ) ^ 3 ≤ (δ I : ℝ) * (D * (Real.log B + 1)) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (δ I))]
    unfold curveBound
    refine (mul_le_mul (mul_le_mul hcube hpow (by positivity) (by positivity))
      (show Real.log B + δ I ≤ (D + 1) * (Real.log B + 1) by nlinarith)
      (by positivity) (by positivity)).trans_eq (by ring)
  have hcv_sum : ∑ I ∈ curves, curveBound (δ I) B ≤ K_wt * A * D ^ 2 * (D + 1) * B := calc
    ∑ I ∈ curves, curveBound (δ I) B
        ≤ ∑ I ∈ curves, (δ I : ℝ) * D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 :=
          sum_le_sum hcv_pt
    _ = (∑ I ∈ curves, (δ I : ℝ)) * D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
        simp only [Finset.sum_mul]
    _ ≤ (A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1)) * D ^ 2 * (D + 1) *
          B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by gcongr
    _ = (A * D ^ 2 * (D + 1)) *
          (B ^ (1 / Real.sqrt (f.totalDegree : ℝ) + 1 / 2) * (Real.log B + 1) ^ 4) := by
        rw [Real.rpow_add hB0]; ring
    _ ≤ (A * D ^ 2 * (D + 1)) * (K_wt * B) := mul_le_mul_of_nonneg_left
        (surface_nonlinear_polylog_weight hd 4 hB) (by positivity)
    _ = K_wt * A * D ^ 2 * (D + 1) * B := by ring
  have hcurveCount : (count (⋃ I ∈ curves, idealZeroLocus I) B : ℝ) ≤
      K_cv * A * D ^ 2 * (D + 1) * B := calc
    (count (⋃ I ∈ curves, idealZeroLocus I) B : ℝ) ≤ ∑ I ∈ curves, (count (idealZeroLocus I) B : ℝ) :=
      mod_cast count_biUnion_finset_le curves idealZeroLocus B
    _ ≤ ∑ I ∈ curves, K_ac * curveBound (δ I) B := sum_le_sum fun I hI => by
      obtain ⟨hIS, hδ⟩ := mem_filter.mp hI
      exact hac I (hS I hIS).1.isPrime (δ I) (by omega) (hS I hIS).1.degree B hB
    _ = K_ac * ∑ I ∈ curves, curveBound (δ I) B := (Finset.mul_sum _ _ _).symm
    _ ≤ K_ac * (K_wt * A * D ^ 2 * (D + 1) * B) := mul_le_mul_of_nonneg_left hcv_sum hK_ac.le
    _ = K_cv * A * D ^ 2 * (D + 1) * B := by dsimp [K_cv]; ring
  have hcard : (lines.card : ℝ) ≤ ∑ I ∈ S, (δ I : ℝ) := calc
    (lines.card : ℝ) ≤ S.card := mod_cast card_le_card (filter_subset _ S)
    _ = ∑ _I ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ I ∈ S, (δ I : ℝ) := sum_le_sum fun I hI => mod_cast (hS I hI).2
  have hwt1 : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) ≤ K_cd * B := calc
    B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1)
        ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ) + 1 / 2) * (Real.log B + 1) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by linarith)
    _ ≤ K_cd * B := by
        have hh := surface_nonlinear_polylog_weight hd 1 hB
        norm_num only [Nat.factorial, Nat.cast_one, pow_one, div_one] at hh
        convert hh using 1
  have hcardBound : (lines.card : ℝ) ≤ A * K_cd * B :=
    (hcard.trans hbudget).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hwt1 hA)
  have hsub : (⋃ I ∈ S, idealZeroLocus I) ⊆
      (⋃ I ∈ lines, idealZeroLocus I) ∪ ⋃ I ∈ curves, idealZeroLocus I := fun x hx => by
    obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
    by_cases hδ : δ I = 1
    · exact Or.inl (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨hIS, hδ⟩, hxI⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨hIS, by have := (hS I hIS).2; omega⟩, hxI⟩⟩)
  have hcnt : (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
      (count (⋃ I ∈ lines, idealZeroLocus I) B : ℝ) + count (⋃ I ∈ curves, idealZeroLocus I) B :=
    mod_cast (count_mono hsub le_rfl).trans (count_union_le _ _ B)
  have h1 : K_ln ≤ K₀ := by dsimp [K₀]; linarith
  have h2 : K_cv ≤ K₀ := by dsimp [K₀]; linarith
  have h3 : K_cd ≤ K₀ := by dsimp [K₀]; linarith
  nlinarith [hcnt, hlineCount, hcurveCount, hcardBound,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1
      (by positivity : 0 ≤ (f.totalDegree : ℝ) ^ 6)) hB0.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hA) hB0.le,
    mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ A * D ^ 2 * (D + 1) * B)]

private theorem primitive_surface_coefficient_reduction
    (f : MvPolynomial (Fin 3) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hf : Irreducible (map (Int.castRingHom ℚ) f)) {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      (((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        (Real.log ((3 + f.totalDegree).choose f.totalDegree) + f.totalDegree) + 1) *
        (Real.log B + 1) ∨
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ 3 * (f.totalDegree : ℝ) ^ 2 * B := by
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by rw [h, map_zero])
  rcases affine_coefficient_height_dichotomy f hf0 hprim hB with hht | ⟨g, ⟨_, hprop, hz0⟩, hgdeg⟩
  · left
    have hlog := Real.log_nonneg hB
    have hNlog := Real.log_natCast_nonneg ((3 + f.totalDegree).choose f.totalDegree)
    nlinarith [show (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree by positivity,
      show (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) by positivity]
  · right
    have hB0 : 0 ≤ B := by linarith
    have hpropQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g := fun h =>
      hprop (hprim.rational_map_dvd_iff.mp h)
    obtain ⟨S, δ, hcv, hcov, hbud, _⟩ := exists_completeIntersection_curve_components
      (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) g) hf hpropQ
    have hcnt : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
        count (zeroLocus (map (Int.castRingHom ℚ) f) ∩ zeroLocus (map (Int.castRingHom ℚ) g)) B :=
      card_le_card fun x hx => by
        obtain ⟨hxB, hxf⟩ := mem_integralPoints.mp hx
        have hf_x : eval x f = 0 := Int.cast_injective (α := ℚ)
          (by change (Int.castRingHom ℚ) (eval x f) = (Int.castRingHom ℚ) 0; rwa [map_eval, map_zero])
        have hg_x : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = 0 := by
          have hh := congrArg (Int.castRingHom ℚ) (hz0 x hxB hf_x); rwa [map_eval, map_zero] at hh
        exact mem_integralPoints.mpr ⟨hxB, hxf, hg_x⟩
    rw [hcov] at hcnt
    rw [rational_map_totalDegree, rational_map_totalDegree] at hbud
    have hsumR : ∑ P ∈ S, (δ P : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree := by
      have hh : ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤ ((f.totalDegree * g.totalDegree : ℕ) : ℝ) := mod_cast hbud
      simpa only [Nat.cast_sum, Nat.cast_mul] using hh
    have hsec : (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
        (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) :=
      (finite_curve_union_count_le_box_side S δ
        (fun P hP => ⟨(hcv P hP).isPrime, (hcv P hP).height_eq, (hcv P hP).degree⟩) hB0).trans
        (mul_le_mul_of_nonneg_right hsumR (by linarith))
    have hgdegR : (g.totalDegree : ℝ) ≤ f.totalDegree := mod_cast hgdeg
    exact ((Nat.cast_le.mpr hcnt).trans hsec).trans
      ((show (f.totalDegree : ℝ) * g.totalDegree * (2 * B + 1) ≤
        (f.totalDegree : ℝ) * f.totalDegree * (3 * B) by gcongr; linarith).trans_eq (by ring))

private def surfaceWindowSize (W_sc B : ℝ) : ℝ := W_sc * (Real.log B + 1)

private lemma surfaceWindowSize_one_le {W_sc B : ℝ} (hW : 2 ≤ W_sc) (hB : 1 ≤ B) :
    1 ≤ surfaceWindowSize W_sc B := by
  unfold surfaceWindowSize; nlinarith [Real.log_nonneg hB]

private theorem surface_residue_linear_count (d : ℕ) (hd : 5 ≤ d)
    (W_sc A : ℝ) (hW_sc : 2 ≤ W_sc) (hA : 0 ≤ A) :
    ∃ K_res : ℝ, 0 < K_res ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), f.totalDegree = d →
      ∀ B : ℝ, ∀ hB : 1 ≤ B, ∀ F : SurfaceCongruenceFamily f B A,
      Irreducible (map (Int.castRingHom ℚ) f) →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I)) →
      (count (surfaceResidueResidualLocus F S (surfaceWindowSize W_sc B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) (surfaceWindowSize_one_le hW_sc hB)) B : ℝ) ≤
          K_res * B := by
  have hratio := scalingPrimeRatio_one_le
  have hdR : (5 : ℝ) ≤ d := mod_cast hd
  let L_sc := 1 + (Real.log 4 + 4) * scalingPrimeRatio * W_sc
  have hL_sc : 1 ≤ L_sc := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have : 0 ≤ (Real.log 4 + 4) * scalingPrimeRatio * W_sc := by positivity
    dsimp [L_sc]; linarith
  let U := scalingPrimeRatio * W_sc + 1
  have hU : 0 ≤ U := by dsimp [U]; positivity
  obtain ⟨K₀, hK₀, hbound⟩ := congruencePrimeWindow_surface_residual_bound
    (show 1 ≤ W_sc by linarith) (show 1 ≤ 2 * (d : ℝ) by linarith)
  let E := 8 * (d : ℝ) * A ^ 2 * L_sc ^ 2 * U ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E * K₀ + 1, by positivity, fun f hfd B hB F hir S δ hS => ?_⟩
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  have hL := surfaceWindowSize_one_le hW_sc hB
  have hpoly := surface_residue_residual_count_le F hA hB hL (by omega)
    (show 0 ≤ 2 * B ^ (1 / Real.sqrt (d : ℝ)) by positivity)
    (by rw [hfd]; linarith [Real.rpow_pos_of_pos hB0 (1 / Real.sqrt (d : ℝ))])
    hir S δ hS
  have hbud_eq : surfaceResidueLogBudget B (surfaceWindowSize W_sc B) = L_sc * (Real.log B + 1) := by
    dsimp [surfaceResidueLogBudget, surfaceWindowSize, L_sc]; ring
  have hx : (2 * B ^ (1 / Real.sqrt (d : ℝ))) ^ 2 = 4 * B ^ (2 / Real.sqrt (d : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (B ^ _) 2, ← Real.rpow_mul hB0.le]
    norm_num only [Nat.cast_ofNat]; congr 2; ring
  rw [hfd, hbud_eq, hx] at hpoly
  have hu : scalingPrimeRatio * surfaceWindowSize W_sc B + 1 ≤ U * (Real.log B + 1) := by
    dsimp [surfaceWindowSize, U]; nlinarith
  have hest : (count (surfaceResidueResidualLocus F S (surfaceWindowSize W_sc B)
      (2 * B ^ (1 / Real.sqrt (d : ℝ))) hL) B : ℝ) ≤
      E * (((congruencePrimeWindow (surfaceWindowSize W_sc B)).card *
        (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceWindowSize W_sc B)).card) *
        B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4) :=
    hpoly.trans ((show 2 * (d : ℝ) * A ^ 2 * (L_sc * (Real.log B + 1)) ^ 2 *
        (scalingPrimeRatio * surfaceWindowSize W_sc B + 1) ^ 2 *
        (4 * B ^ (2 / Real.sqrt (d : ℝ))) *
        (congruencePrimeWindow (surfaceWindowSize W_sc B)).card *
        (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceWindowSize W_sc B)).card ≤
        2 * (d : ℝ) * A ^ 2 * (L_sc * (Real.log B + 1)) ^ 2 *
        (U * (Real.log B + 1)) ^ 2 * (4 * B ^ (2 / Real.sqrt (d : ℝ))) *
        (congruencePrimeWindow (surfaceWindowSize W_sc B)).card *
        (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceWindowSize W_sc B)).card by gcongr).trans_eq
        (by dsimp [E]; ring))
  have hh := hest.trans (mul_le_mul_of_nonneg_left (hbound d hd B hB) hE)
  nlinarith only [hh, hB0]

theorem primitive_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ K_tot : ℝ, 0 < K_tot ∧
      ∀ f : MvPolynomial (Fin 3) ℤ, PrimitiveIntegerPolynomial f →
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ K_tot * B := by
  classical
  let K : ℝ := ((3 + d).choose d : ℝ) * (Real.log ((3 + d).choose d) + d) + 1
  have hK : 0 ≤ K := by
    have := Real.log_natCast_nonneg ((3 + d).choose d)
    dsimp [K]; positivity
  obtain ⟨A, hA, hfam⟩ := exists_surface_congruence_family d (by omega) K hK
  let A₀ := 2 * (d : ℝ) * A
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  let W_sc := 4 * Real.log ((d : ℝ) + 1) + K + d + 2
  have hW_sc : 2 ≤ W_sc := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (d : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) d])
    dsimp [W_sc]; linarith [Nat.cast_nonneg (α := ℝ) d]
  let L_sc := 1 + (Real.log 4 + 4) * scalingPrimeRatio * W_sc
  have hL_sc : 1 ≤ L_sc := by
    have := scalingPrimeRatio_one_le
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have : 0 ≤ (Real.log 4 + 4) * scalingPrimeRatio * W_sc := by positivity
    dsimp [L_sc]; linarith
  let D := A₀ * L_sc
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨K_cv, hK_cv, hcurve⟩ := retained_surface_curve_union_bound
  obtain ⟨K_res, hK_res, hres⟩ := surface_residue_linear_count d hd W_sc A hW_sc hA
  let K_ret := K_cv * ((d : ℝ) ^ 6 + A₀ * (D ^ 2 * (D + 1) + 1))
  have hK_ret : 0 ≤ K_ret := by dsimp [K_ret]; positivity
  refine ⟨12 * (d : ℝ) ^ 2 + K_ret + K_res + 1, by positivity,
    fun f hprim htop hfd B hB => ?_⟩
  subst d
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f htop
  have hir := rational_irreducible_of_charZero_map f habs
  have hf0 : f ≠ 0 := fun hz => hir.ne_zero (by rw [hz, map_zero])
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  rcases primitive_surface_coefficient_reduction f hprim hir hB with hheight | hlarge
  · have hH : 1 ≤ (integerCoefficientHeight f : ℝ) := mod_cast integerCoefficientHeight_pos f hf0
    obtain ⟨F⟩ := hfam f habs rfl hH hB (coefficient_abs_le_integerCoefficientHeight f) hheight
    have hL := surfaceWindowSize_one_le hW_sc hB
    have hrt1 : 1 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) := Real.one_le_rpow hB (by positivity)
    have hXL : 2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤
        Real.exp (surfaceWindowSize W_sc B) := by
      have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast (by omega : 1 ≤ f.totalDegree)
      have hrt_le1 : 1 / Real.sqrt (f.totalDegree : ℝ) ≤ 1 :=
        by simpa using one_div_le_one_div_of_le zero_lt_one (Real.le_sqrt_of_sq_le (by simpa using hd1))
      have hlog2 : Real.log 2 ≤ (2 : ℝ) := Real.log_le_self (by norm_num)
      have hlogX : Real.log (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) ≤
          surfaceWindowSize W_sc B := by
        unfold surfaceWindowSize
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hB0]
        nlinarith only [hW_sc, hlog2, hlogB, mul_le_mul_of_nonneg_right hrt_le1 hlogB]
      simpa only [Real.exp_log (show 0 < 2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) by linarith)] using
        Real.exp_le_exp.mpr hlogX
    have hlog_win : 4 * Real.log ((f.totalDegree : ℝ) + 1) +
        Real.log (integerCoefficientHeight f : ℝ) + f.totalDegree * Real.log B ≤
        surfaceWindowSize W_sc B := by
      unfold surfaceWindowSize; dsimp only [W_sc]
      have hld := Real.log_nonneg (show (1 : ℝ) ≤ (f.totalDegree : ℝ) + 1 by
        linarith [Nat.cast_nonneg (α := ℝ) f.totalDegree])
      nlinarith only [hheight, hld, hlogB, Nat.cast_nonneg (α := ℝ) f.totalDegree]
    obtain ⟨S, δ, hS, hsec_cov, hbud_raw, _⟩ := exists_completeIntersection_curve_components
      (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) F.initial) hir
      (F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f))
    rw [rational_map_totalDegree, rational_map_totalDegree] at hbud_raw
    have hinit_deg : (F.initial.totalDegree : ℝ) ≤
        A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
      simpa only [SurfaceCongruenceFamily.initial, sum_empty, Real.exp_zero, div_one, add_zero] using
        F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
    have hbud_cast : ∑ I ∈ S, (δ I : ℝ) ≤ (f.totalDegree : ℝ) * F.initial.totalDegree := by
      have hh : ((∑ I ∈ S, δ I : ℕ) : ℝ) ≤ ((f.totalDegree * F.initial.totalDegree : ℕ) : ℝ) :=
        mod_cast hbud_raw
      simpa only [Nat.cast_sum, Nat.cast_mul] using hh
    have hbudget : ∑ I ∈ S, (δ I : ℝ) ≤ (f.totalDegree : ℝ) * A *
        (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) :=
      hbud_cast.trans ((mul_le_mul_of_nonneg_left hinit_deg (Nat.cast_nonneg _)).trans_eq (by ring))
    have hbud_eq : surfaceResidueLogBudget B (surfaceWindowSize W_sc B) = L_sc * (Real.log B + 1) := by
      dsimp [surfaceResidueLogBudget, surfaceWindowSize, L_sc]; ring
    let small := S.filter fun I => (δ I : ℝ) ≤
      2 * f.totalDegree * A * surfaceResidueLogBudget B (surfaceWindowSize W_sc B)
    have hcov_pts : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
        count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B +
        count (⋃ I ∈ small, idealZeroLocus I) B +
        count (surfaceResidueResidualLocus F S (surfaceWindowSize W_sc B)
          (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) hL) B := by
      have hrat {p : MvPolynomial (Fin 3) ℤ} {x : IntPoint 3} (hp : eval x p = 0) :
          eval (rationalPoint x) (map (Int.castRingHom ℚ) p) = 0 := by
        have hh := congrArg (Int.castRingHom ℚ) hp; rwa [map_eval, map_zero] at hh
      refine (card_le_card fun x hx => ?_).trans
        ((count_union_le _ _ B).trans (Nat.add_le_add_right (count_union_le _ _ B) _))
      obtain ⟨hbox, hzero⟩ := mem_integralPoints.mp hx
      have hxf : eval x f = 0 := Int.cast_injective (α := ℚ)
        (by change (Int.castRingHom ℚ) (eval x f) = (Int.castRingHom ℚ) 0; rwa [map_eval, map_zero])
      refine mem_integralPoints.mpr ⟨hbox, ?_⟩
      by_cases hsmooth : ∃ j, eval x (pderiv j f) ≠ 0
      · have hxcov : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I :=
          hsec_cov ▸ ⟨hrat hxf, hrat (F.initial_vanishes x hbox hxf)⟩
        obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hxcov
        obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
        by_cases hsm : (δ I : ℝ) ≤
            2 * f.totalDegree * A * surfaceResidueLogBudget B (surfaceWindowSize W_sc B)
        · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
            ⟨mem_filter.mpr ⟨hIS, hsm⟩, hxI⟩⟩))
        · exact Or.inr (large_curve_point_mem_surfaceResidueResidualLocus f hir hA hB hH hL
            (coefficient_abs_le_integerCoefficientHeight f) hlog_win (by linarith) (by linarith) hXL
            F S I hIS (hS I hIS).toIsSurfaceCurve (hS I hIS).mem_right (lt_of_not_ge hsm)
            x hbox hxf hxI hsmooth)
      · refine Or.inl (Or.inl ⟨hrat hxf, fun j => ?_⟩)
        rw [pderiv_map]; exact hrat (not_not.mp fun hn => hsmooth ⟨j, hn⟩)
    have hbud_sm : ∑ I ∈ small, (δ I : ℝ) ≤
        A₀ * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) := calc
      ∑ I ∈ small, (δ I : ℝ) ≤ ∑ I ∈ S, (δ I : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ ≤ (f.totalDegree : ℝ) * A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := hbudget
      _ ≤ (f.totalDegree : ℝ) * A * (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) * (1 + Real.log B) := by
          gcongr; linarith
      _ = A₀ * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) := by dsimp [A₀]; ring
    have hret : (count (⋃ I ∈ small, idealZeroLocus I) B : ℝ) ≤ K_ret * B :=
      hcurve f htop hd small δ A₀ D B hA₀ hD hB
        (fun I hI => ⟨(hS I (mem_filter.mp hI).1).toIsSurfaceCurve, (hS I (mem_filter.mp hI).1).pos⟩)
        (fun I hI => by
          have hh := (mem_filter.mp hI).2
          rw [hbud_eq] at hh; simpa only [D, A₀, mul_assoc] using hh)
        hbud_sm
    have hresidual := hres f rfl B hB F hir S δ fun I hI => (hS I hI).toIsSurfaceCurve
    have hsing : (count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        9 * (f.totalDegree : ℝ) ^ 2 * B := by
      simpa only [rational_map_totalDegree, Nat.cast_one, Nat.cast_ofNat, pow_one,
        show (3 * (1 + 2) : ℝ) = 9 by norm_num] using
        singular_hypersurface_dimension_growth (n := 1) (map (Int.castRingHom ℚ) f) hir hB
    have hcovR : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        9 * (f.totalDegree : ℝ) ^ 2 * B + K_ret * B + K_res * B := by
      have hcR : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
          (count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B : ℝ) +
            count (⋃ I ∈ small, idealZeroLocus I) B +
            count (surfaceResidueResidualLocus F S (surfaceWindowSize W_sc B)
              (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) hL) B := by
        exact_mod_cast hcov_pts
      exact hcR.trans (add_le_add (add_le_add hsing hret) hresidual)
    calc (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ)
        ≤ (9 * (f.totalDegree : ℝ) ^ 2 + K_ret + K_res) * B := by linarith only [hcovR]
      _ ≤ (12 * (f.totalDegree : ℝ) ^ 2 + K_ret + K_res + 1) * B :=
          mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (f.totalDegree : ℝ)]) hB0.le
  · calc (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ)
        ≤ 3 * (f.totalDegree : ℝ) ^ 2 * B := hlarge
      _ ≤ (12 * (f.totalDegree : ℝ) ^ 2 + K_ret + K_res + 1) * B :=
          mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (f.totalDegree : ℝ), hK_ret, hK_res.le]) hB0.le

end
end CCDN
