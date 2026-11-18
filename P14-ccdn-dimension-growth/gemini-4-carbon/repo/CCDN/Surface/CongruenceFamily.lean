module

public import CCDN.AuxiliaryPolynomial.AffineCongruenceAuxiliary
public import CCDN.Determinant.SmoothAffineResidueClasses
import CCDN.Analysis.SurfaceMonomialWeightNumerics
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PlaneHilbert
import CCDN.Hilbert.PrincipalStandardMonomials
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

def SmoothAffineResidueFamily.restrict {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P Q : Finset ℕ} (r : SmoothAffineResidueFamily f P) (hQP : Q ⊆ P) :
    SmoothAffineResidueFamily f Q := fun q => r ⟨q.val, hQP q.property⟩

def emptySmoothAffineResidueFamily {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    SmoothAffineResidueFamily f ∅ := fun p => False.elim (notMem_empty p.val p.property)

structure SurfaceCongruenceFamily (f : MvPolynomial (Fin 3) ℤ) (B A : ℝ) where
  auxiliary : (P : Finset ℕ) → (∀ p ∈ P, p.Prime) →
    SmoothAffineResidueFamily f P → MvPolynomial (Fin 3) ℤ
  proper : ∀ P hP r, ¬ map (Int.castRingHom ℚ) f ∣
    map (Int.castRingHom ℚ) (auxiliary P hP r)
  degree_le : ∀ P hP r, ((auxiliary P hP r).totalDegree : ℝ) ≤
    A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) + 1) * (1 + Real.log B + ∑ p ∈ P, Real.log p)
  vanishes : ∀ P hP r (x : IntPoint 3), InBox x B → eval x f = 0 →
    (∀ (p : ℕ), p ∈ P → ∀ j, (p : ℤ) ∣ x j - smoothResidueIntegerLift r p j) →
    eval x (auxiliary P hP r) = 0

def SurfaceCongruenceFamily.initial {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) : MvPolynomial (Fin 3) ℤ :=
  F.auxiliary ∅ (by simp) (emptySmoothAffineResidueFamily f)

lemma SurfaceCongruenceFamily.initial_eq {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (r : SmoothAffineResidueFamily f ∅)
    (hP : ∀ p ∈ (∅ : Finset ℕ), p.Prime) :
    F.auxiliary ∅ hP r = F.initial := by
  have he : r = emptySmoothAffineResidueFamily f :=
    funext fun p => False.elim (notMem_empty p.val p.property)
  subst he; rfl

lemma SurfaceCongruenceFamily.initial_vanishes {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0) :
    eval x F.initial = 0 :=
  F.vanishes ∅ (by simp) (emptySmoothAffineResidueFamily f) x hx hxf (by simp)

lemma SurfaceCongruenceFamily.point_vanishes {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    eval x (F.auxiliary P hP (smoothResidueFamilyOfPoint x hxf P hs)) = 0 :=
  F.vanishes P hP _ x hx hxf fun p hp j => by
    let : NeZero p := ⟨(hP p hp).ne_zero⟩
    exact smoothResidueFamilyOfPoint_congruence x hxf P hs p hp j

private theorem surface_standard_monomial_weight
    (f : MvPolynomial (Fin 3) ℚ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {M : ℕ} (hM : f.totalDegree ≤ M) :
    let S := standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex M
    (∑ a ∈ S, ((Finsupp.degree a : ℕ) : ℝ)) ≤
      (2 / 3 : ℝ) * S.card * Real.sqrt (2 * S.card / (f.totalDegree : ℝ)) +
        (2 * f.totalDegree + 2) * S.card := by
  classical
  dsimp only
  let H : ℕ → ℕ := fun k => Module.finrank ℚ (filteredCoordinateSpace (Ideal.span {f}) k)
  have hbounds (k : ℕ) (hk : f.totalDegree ≤ k) :
      (f.totalDegree : ℝ) * ((k : ℝ) - f.totalDegree + 1) ^ 2 / 2 ≤ H k ∧
        (H k : ℝ) ≤ (f.totalDegree : ℝ) * ((k : ℝ) + 2) ^ 2 / 2 := by
    have hr : H k + (2 + 1 + (k - f.totalDegree)).choose (k - f.totalDegree) =
        (2 + 1 + k).choose k := by
      simpa only [H, finrank_restrictTotalDegree, Fintype.card_fin] using
        principal_filtered_finrank f hf hk
    have hb := hypersurface_rank_power_bounds hk hr
    norm_num at hb; exact hb
  have hsum := surface_rank_prefix_sum_lower H hM fun k hk => (hbounds k hk).1
  have hidR : (∑ a ∈ standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex M,
      ((Finsupp.degree a : ℕ) : ℝ)) + (∑ k ∈ range M, (H k : ℝ)) = (M : ℝ) * H M :=
    mod_cast standardMonomialPrefix_weight_identity (Ideal.span {f}) M
  have hdR : (0 : ℝ) < f.totalDegree := mod_cast hd
  have hMR : (f.totalDegree : ℝ) ≤ M := mod_cast hM
  have hbase : 0 ≤ 2 * (H M : ℝ) / (f.totalDegree : ℝ) := by positivity
  let R : ℝ := Real.sqrt (2 * (H M : ℝ) / (f.totalDegree : ℝ))
  have hroot : (f.totalDegree : ℝ) * R ^ 2 = 2 * H M := by
    dsimp [R]; rw [Real.sq_sqrt hbase]; field_simp
  have hlo : (M : ℝ) - f.totalDegree ≤ R := Real.le_sqrt_of_sq_le
    ((le_div_iff₀ hdR).mpr (by have := (hbounds M hM).1; nlinarith))
  have hhi : R ≤ (M : ℝ) + 2 := (Real.sqrt_le_left (by positivity)).mpr
    ((div_le_iff₀ hdR).mpr (by have := (hbounds M hM).2; nlinarith))
  have hw : (∑ a ∈ standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex M,
      ((Finsupp.degree a : ℕ) : ℝ)) + (f.totalDegree : ℝ) *
        ((M : ℝ) - f.totalDegree) ^ 3 / 6 ≤ (M : ℝ) * H M := by linarith
  have hh := surface_weight_root_bound hdR hMR (Nat.cast_nonneg (H M)) R (Real.sqrt_nonneg _)
    hroot hlo hhi hw
  simpa only [standardMonomialPrefix_card, H, R] using hh

private theorem surface_congruence_gap_of_log_rank {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) {K B H Q K_ch K_gap : ℝ}
    (_hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (hK_ch : K_ch = Real.log (2 + 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4 *
      (1 + K / (d : ℝ) ^ 2)) + 2 * mertensError + 1)
    (hK_gap : K_gap = 8 * Real.log d + 2 * K_ch + hypersurfaceDeterminantError 1 + 6 * d + 22)
    (hroot : 1 + Real.log B + Q ≤ Real.sqrt (s : ℝ))
    (hrank : (2 / Real.sqrt (d : ℝ)) * Real.log B +
      2 * Real.log (1 + Real.log B + Q) + K_gap ≤ Real.log s + 2 * Q) :
    Real.log (s.factorial : ℝ) +
      ((2 / 3 : ℝ) * s * Real.sqrt (2 * s / (d : ℝ)) + (2 * d + 2) * s) *
        Real.log B < affineCongruenceDeterminantLower 1 d s H Q := by
  have hsR : (0 : ℝ) < s := mod_cast hs
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hlogB := Real.log_nonneg hB
  have hlogH := Real.log_nonneg hH
  have hcharge : congruenceHeightCharge 4 d H Q ≤
      Real.log (1 + Real.log B + Q) + K_ch := by
    have hc : 0 ≤ hypersurfaceHeightConstant 4 :=
      zero_le_one.trans (hypersurfaceHeightConstant_one_le 4)
    have hT : 1 ≤ 1 + Real.log B + Q := by linarith
    have hht' : Real.log H ≤ K * (1 + Real.log B + Q) := by nlinarith
    let A₀ := 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4
    have hA0 : 0 ≤ A₀ := by dsimp [A₀]; positivity
    have hdiv := div_le_div_of_nonneg_right hht' (sq_nonneg (d : ℝ))
    have hin : 1 + A₀ * (1 + Real.log H / (d : ℝ) ^ 2) + Q ≤
        (2 + A₀ * (1 + K / (d : ℝ) ^ 2)) * (1 + Real.log B + Q) := by
      have hm := mul_le_mul_of_nonneg_left hdiv hA0
      rw [show K * (1 + Real.log B + Q) / (d : ℝ) ^ 2 =
        K / (d : ℝ) ^ 2 * (1 + Real.log B + Q) by ring] at hm
      nlinarith [mul_le_mul_of_nonneg_left hT hA0]
    have hh := Real.log_le_log (by positivity) hin
    rw [Real.log_mul (by positivity) (by linarith)] at hh
    rw [hK_ch]; unfold congruenceHeightCharge
    dsimp only [A₀] at hh; simp only [mul_assoc] at hh ⊢; nlinarith
  have hfac' : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * (2 * Real.sqrt (s : ℝ)) := by
    have hfac : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log s := by
      simpa only [Real.log_pow] using Real.log_le_log (by positivity)
        (mod_cast Nat.factorial_le_pow s : (s.factorial : ℝ) ≤ (s : ℝ) ^ s)
    have hlog : Real.log (s : ℝ) ≤ 2 * Real.sqrt (s : ℝ) := by
      simpa only [Nat.cast_ofNat, ← Real.sqrt_eq_rpow] using
        log_le_dimension_root (r := 2) (by omega) hsR
    exact hfac.trans (mul_le_mul_of_nonneg_left hlog hsR.le)
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  let A : ℝ := Real.sqrt 2 / 3 * s * Real.sqrt s
  have hA : 0 < A := by dsimp [A]; positivity
  have hmain : (2 / 3 : ℝ) * s * Real.sqrt (2 * s / (d : ℝ)) = A * (2 / Real.sqrt (d : ℝ)) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]; dsimp [A]; ring
  have herr : Real.log (s.factorial : ℝ) + (2 * d + 2) * s * Real.log B + 3 * s * Q ≤
      A * (6 * d + 21) := by
    have hb' := mul_le_mul_of_nonneg_left (show Real.log B ≤ Real.sqrt (s : ℝ) by linarith)
      (show 0 ≤ (2 * (d : ℝ) + 2) * s by positivity)
    have hq' := mul_le_mul_of_nonneg_left (show Q ≤ Real.sqrt (s : ℝ) by linarith)
      (show 0 ≤ 3 * (s : ℝ) by positivity)
    have hA' : (s : ℝ) * Real.sqrt s ≤ 3 * A := by
      dsimp [A]; nlinarith [mul_le_mul_of_nonneg_right hsqrt2
        (show 0 ≤ (s : ℝ) * Real.sqrt s by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hA' (show 0 ≤ 2 * (d : ℝ) + 7 by positivity)]
  have hbracket : (2 / Real.sqrt (d : ℝ)) * Real.log B + (6 * d + 22) ≤
      Real.log s + 2 * Q - 8 * Real.log d -
        2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1 := by
    rw [hK_gap] at hrank; linarith
  have hp : (s : ℝ) ^ (1 + 1 / 2 : ℝ) = s * Real.sqrt s := by
    rw [Real.rpow_add' hsR.le (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num at hp
  have hlow_eq : affineCongruenceDeterminantLower 1 d s H Q =
      A * (Real.log s + 2 * Q - 8 * Real.log d -
        2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1) - 3 * s * Q := by
    unfold affineCongruenceDeterminantLower hypersurfaceDeterminantMain
    norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_one, Nat.cast_add, Nat.cast_succ, mul_one]
    rw [hp, ← Real.sqrt_eq_rpow]; dsimp [A]; ring
  rw [hlow_eq, hmain]
  nlinarith [mul_le_mul_of_nonneg_left hbracket hA.le]

theorem exists_surface_congruence_family (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), AbsolutelyIrreducible f → f.totalDegree = d →
      ∀ {H B : ℝ}, 1 ≤ H → 1 ≤ B → CoefficientHeightLE f H →
      Real.log H ≤ K * (Real.log B + 1) →
      Nonempty (SurfaceCongruenceFamily f B A) := by
  classical
  let K_ch := Real.log (2 + 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4 *
    (1 + K / (d : ℝ) ^ 2)) + 2 * mertensError + 1
  let K_gap := 8 * Real.log d + 2 * K_ch + hypersurfaceDeterminantError 1 + 6 * d + 22
  let E := Real.exp (K_gap / 2) + 1
  let A_deg : ℝ := d + 2 * E + 1
  have hE1 : 1 ≤ E := by dsimp [E]; linarith [Real.exp_pos (K_gap / 2)]
  refine ⟨A_deg, by dsimp [A_deg]; positivity,
    fun f hir hfd {H B} hH hB hcoeff hheight => ?_⟩
  subst d
  have hex (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P) :
      ∃ g : MvPolynomial (Fin 3) ℤ,
        ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
        (g.totalDegree : ℝ) ≤ A_deg *
          (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) / Real.exp (∑ p ∈ P, Real.log p) + 1) *
          (1 + Real.log B + ∑ p ∈ P, Real.log p) ∧
        ∀ x : IntPoint 3, InBox x B → eval x f = 0 →
          (∀ (p : ℕ), p ∈ P → ∀ j, (p : ℤ) ∣ x j - smoothResidueIntegerLift r p j) → eval x g = 0 := by
    let Q := ∑ p ∈ P, Real.log p
    have hQ : 0 ≤ Q := Finset.sum_nonneg fun p hp =>
      Real.log_nonneg (mod_cast (hP p hp).one_le)
    let T := 1 + Real.log B + Q
    let ρ := B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) / Real.exp Q
    let S₀ := E * (ρ + 1) * T
    have hB0 : 0 < B := by linarith
    have hdR : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
    have hT : 1 ≤ T := by dsimp [T]; linarith [Real.log_nonneg hB]
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hS0 : 0 < S₀ := by dsimp [S₀]; positivity
    have hST : T ≤ S₀ := by
      have hh := mul_le_mul hE1 (show 1 ≤ ρ + 1 by linarith) (by norm_num) (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (by linarith : 0 ≤ T)
    let M := f.totalDegree + ⌈2 * S₀⌉₊
    have hdM : f.totalDegree ≤ M := Nat.le_add_right _ _
    have hMl : 2 * S₀ ≤ (M : ℝ) - f.totalDegree + 1 := by
      have hh := Nat.le_ceil (2 * S₀); dsimp [M]; push_cast; linarith
    have hMu : (M : ℝ) ≤ A_deg * (ρ + 1) * T := by
      have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * S₀ by positivity)
      have hprod : 1 ≤ (ρ + 1) * T := by nlinarith
      have hsc := mul_le_mul_of_nonneg_left hprod
        (show 0 ≤ (f.totalDegree : ℝ) + 1 by positivity)
      dsimp [M, A_deg, S₀] at hh ⊢; push_cast; nlinarith
    let fQ := map (Int.castRingHom ℚ) f
    have hf : f ≠ 0 := fun h => hir.ne_zero (by rw [h, map_zero])
    have hfQ : fQ ≠ 0 := fun h =>
      hf ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa [fQ] using h))
    have hdegQ : fQ.totalDegree = f.totalDegree := rational_map_totalDegree f
    let S_mon := standardMonomialPrefix (Ideal.span {fQ}) MonomialOrder.degLex M
    let s := S_mon.card
    have hs_lo : (f.totalDegree : ℝ) * ((M : ℝ) - f.totalDegree + 1) ^ 2 / 2 ≤ s := by
      have hr := principal_standard_prefix_rank fQ hfQ (hdegQ ▸ hdM)
      rw [hdegQ] at hr
      have hb := (hypersurface_rank_power_bounds hdM hr).1
      norm_num at hb; exact hb
    have hsq : S₀ ^ 2 ≤ (s : ℝ) := by
      have hpow : (2 * S₀) ^ 2 ≤ ((M : ℝ) - f.totalDegree + 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hMl 2
      nlinarith [mul_le_mul_of_nonneg_right hdR (sq_nonneg ((M : ℝ) - f.totalDegree + 1)),
        sq_nonneg S₀]
    have hsR : (0 : ℝ) < s := lt_of_lt_of_le (sq_pos_of_pos hS0) hsq
    have hsN : 0 < s := mod_cast hsR
    have hlogS : 2 * Real.log S₀ ≤ Real.log (s : ℝ) := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (sq_pos_of_pos hS0) hsq
    have hlogE : K_gap / 2 ≤ Real.log E := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _)
        (show Real.exp (K_gap / 2) ≤ E by dsimp [E]; linarith)
    have hlogρ : (1 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B - Q ≤ Real.log (ρ + 1) := by
      have hh := Real.log_le_log hρ (by linarith : ρ ≤ ρ + 1)
      rwa [show Real.log ρ = (1 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B - Q by
        dsimp [ρ]; rw [Real.log_div (by positivity) (Real.exp_ne_zero _),
          Real.log_rpow hB0, Real.log_exp]] at hh
    have hSeq : Real.log S₀ = Real.log E + Real.log (ρ + 1) + Real.log T := by
      dsimp [S₀]; rw [Real.log_mul (by positivity) (by linarith),
        Real.log_mul (by linarith) (by positivity)]
    have hrank : (2 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B +
        2 * Real.log T + K_gap ≤ Real.log s + 2 * Q := by
      rw [hSeq] at hlogS
      rw [show (2 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B =
        2 * ((1 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B) by ring]
      linarith
    have hgap := surface_congruence_gap_of_log_rank hd hsN hK hB hH hQ hheight rfl rfl
      (hST.trans (Real.le_sqrt_of_sq_le hsq)) hrank
    let e := (Fintype.equivFin S_mon).symm
    let mon : Fin (Fintype.card S_mon) → (Fin 3 →₀ ℕ) := fun j => (e j).val
    have hc : Fintype.card S_mon = s := Fintype.card_coe S_mon
    have hweight : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) ≤
        (2 / 3 : ℝ) * s * Real.sqrt (2 * s / (f.totalDegree : ℝ)) +
          (2 * f.totalDegree + 2) * s := by
      have hw := surface_standard_monomial_weight fQ hfQ (hdegQ ▸ hd) (hdegQ ▸ hdM)
      have hsum : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) =
          ∑ j ∈ S_mon, ((Finsupp.degree j : ℕ) : ℝ) := by
        rw [← Finset.sum_coe_sort S_mon]
        exact e.sum_comp fun j : S_mon => ((Finsupp.degree j.val : ℕ) : ℝ)
      rw [hsum, ← hdegQ]; exact hw
    have hgap' : Real.log ((Fintype.card S_mon).factorial : ℝ) +
        (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
        affineCongruenceDeterminantLower 1 f.totalDegree (Fintype.card S_mon) H Q := by
      refine lt_of_le_of_lt (add_le_add_right
        (mul_le_mul_of_nonneg_right hweight (Real.log_nonneg hB)) _) ?_
      simpa only [hc] using hgap
    let a := smoothResidueIntegerLift r
    let X_pts := (integerBox 3 B).filter fun x =>
      eval x f = 0 ∧ ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j
    let ex := (Fintype.equivFin X_pts).symm
    let x : Fin (Fintype.card X_pts) → IntPoint 3 := fun i => (ex i).val
    have hx (i) : InBox (x i) B ∧ eval (x i) f = 0 ∧ ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x i j - a p j := by
      simpa only [X_pts, mem_filter, mem_integerBox] using (ex i).property
    obtain ⟨g, _, hgnd, hgdeg, hgz⟩ := exists_affine_congruence_auxiliary_of_gap (hc ▸ hsN)
      f hir hd H hH hcoeff mon (Subtype.val_injective.comp e.injective)
      (fun j => ((mem_standardMonomialPrefix _ _ _ _).mp (e j).property).1)
      (fun j => ((mem_standardMonomialPrefix _ _ _ _).mp (e j).property).2)
      ⟨hB, fun i => (hx i).2.1, fun i j => (hx i).1 j⟩ P a
      ⟨hP, fun p hp => by let : NeZero p := ⟨(hP p hp).ne_zero⟩; exact smoothResidueIntegerLift_zero r p hp,
        fun p hp => by let : NeZero p := ⟨(hP p hp).ne_zero⟩; exact smoothResidueIntegerLift_smooth r p hp,
        fun p hp i j => (hx i).2.2 p hp j⟩ hgap'
    refine ⟨g, hgnd, (Nat.cast_le.mpr hgdeg).trans hMu, fun y hyB hyf hyc => ?_⟩
    obtain ⟨i, hi⟩ := ex.surjective ⟨y, mem_filter.mpr ⟨mem_integerBox.mpr hyB, hyf, hyc⟩⟩
    have hh : eval (ex i).val g = 0 := hgz i
    rwa [hi] at hh
  choose g hgproper hgdegree hgzero using hex
  exact ⟨⟨g, hgproper, hgdegree, hgzero⟩⟩

end
end CCDN
