module
public import RoughRegime.Model
public import NearlyMinimax.CoordinatePartialBridge
@[expose] public section
noncomputable section
section
open MeasureTheory Set MvPolynomial
open scoped ENNReal BigOperators ContDiff
namespace RoughRegime.Model
variable {d q k : ℕ}
theorem holderExponent_pos  (ht : 0 < t) : 0 < holderExponent t := by
  have  := Nat.ceil_pos.mpr ht
  have hcast : ((Nat.ceil t - 1 : ℕ) : ℝ) = (Nat.ceil t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold holderExponent holderOrder
  rw [hcast]
  linarith [Nat.ceil_lt_add_one ht.le]
theorem convex_cube (d ) : Convex ℝ (cube d) := by
  intro x hx y hy a b ha hb hab j
  have hxj := hx j
  have hyj := hy j
  constructor
  · exact add_nonneg (mul_nonneg ha hxj.1) (mul_nonneg hb hyj.1)
  · change a * x j + b * y j ≤ 1
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hxj.2 ha)
        (mul_le_mul_of_nonneg_left hyj.2 hb)
      _ = 1 := by nlinarith
theorem uniqueDiffOn_cube (d ) : UniqueDiffOn ℝ (cube d) :=
  have h_cube_nonempty_interior : (interior (cube d)).Nonempty := by
    let c : Covariate d := WithLp.toLp 2 (fun _ => (1 / 2 ))
    refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
    apply Filter.mem_of_superset (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))
    intro x hx j
    have hcoord : |x j - 1 / 2| < 1 / 2 := by
      have hb := PiLp.norm_apply_le (x - c) j
      have hd : ‖x - c‖ < 1 / 2 := by simpa [dist_eq_norm] using hx
      exact hb.trans_lt hd
    exact ⟨by linarith [(abs_lt.mp hcoord).1], by linarith [(abs_lt.mp hcoord).2]⟩
  uniqueDiffOn_convex (convex_cube d) h_cube_nonempty_interior
theorem coordinateDerivative_eq_iteratedFDeriv  (f q) (σ : Fin q → Fin d) (x : Covariate d) (hx : x ∈ cube d)
    (hf : ContDiffAt ℝ q f x) :
    coordinateDerivative f q σ x =
      iteratedFDeriv ℝ q f x (fun j => EuclideanSpace.single (σ j) 1) := by
  unfold coordinateDerivative
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d) hf hx]
theorem holderBall_regular  (f t H)
    (hf : f ∈ holderBall t H) : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) := by
  change holderNorm f t ≤ ENNReal.ofReal H at hf
  unfold holderNorm at hf
  split_ifs at hf with hreg
  · exact hreg
  · exact False.elim (ENNReal.ofReal_ne_top (top_le_iff.mp hf))
theorem holderBall_coordinate_modulus  (f t H)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (σ x y) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |coordinateDerivative f (holderOrder t) σ x - coordinateDerivative f (holderOrder t) σ y| ≤
      H * ‖x - y‖ ^ holderExponent t := by
  by_cases he : x = y
  · subst y
    simpa using mul_nonneg hH (Real.rpow_nonneg (norm_nonneg (x - x)) (holderExponent t))
  · have hreg := holderBall_regular f t H hf
    change holderNorm f t ≤ ENNReal.ofReal H at hf
    have hp : ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
        coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t) ≤
        holderSeminorm f t := le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx
      (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le he le_rfl)))))
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) _)).mp ((ENNReal.ofReal_le_ofReal_iff hH).mp (hp.trans (by unfold holderNorm at hf; rw [ite_eq_left hreg] at hf; exact le_trans le_add_self hf)))
lemma coordinateDerivative_of_order_zero  (f : Covariate d → ℝ)
    (q : ℕ) (hq : q = 0) (σ : Fin q → Fin d) (x : Covariate d) :
    coordinateDerivative f q σ x = f x := by
  subst q
  rfl
theorem holderBall_spatial_modulus  (f t H)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (x y )
    (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |f x - f y| ≤ (↑d + 1) * H * ‖x - y‖ ^ min t 1 := by
  have hreg := holderBall_regular f t H hf
  by_cases ht : t ≤ 1
  · have hk : holderOrder t = 0 := by
      have : Nat.ceil t ≤ 1 := Nat.ceil_le.mpr (by simpa using ht)
      unfold holderOrder
      omega
    have hb := holderBall_coordinate_modulus f t H hH hf
      (fun i => Fin.elim0 (show Fin 0 from hk ▸ i)) x y hx hy
    have hzero : ∀ (σ : Fin (holderOrder t) → Fin d) z,
        coordinateDerivative f (holderOrder t) σ z = f z := by
      intro σ z
      exact coordinateDerivative_of_order_zero f _ hk σ z
    rw [hzero, hzero] at hb
    simp only [holderExponent, hk, min_eq_left ht, sub_zero, Nat.cast_zero] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_right
      (show H ≤ (d + 1) * H by nlinarith [mul_nonneg (Nat.cast_nonneg d) hH])
      (Real.rpow_nonneg (norm_nonneg _) _))
  · have hk : 1 ≤ holderOrder t := by
      have : 1 < Nat.ceil t := Nat.lt_ceil.mpr (by simpa using lt_of_not_ge ht)
      unfold holderOrder
      omega
    have hbound : ∀ z ∈ cube d, ‖fderivWithin ℝ f (cube d) z‖ ≤ d * H := by
      intro z hz
      have h_linear_norm_le_coordinate_bound (L : Covariate d →L[ℝ] ℝ) (hb : ∀ i, |L (EuclideanSpace.single i 1)| ≤ H) : ‖L‖ ≤ d * H := by
        apply L.opNorm_le_bound (by positivity)
        intro x
        have hx : x = ∑ i : Fin d, x i • EuclideanSpace.single i 1 := by
          ext j
          simp [Pi.single_apply]
        conv_lhs => rw [hx, map_sum]
        calc
          _ ≤ ∑ i : Fin d, ‖L (x i • EuclideanSpace.single i 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _i : Fin d, ‖x‖ * H := by
            apply Finset.sum_le_sum
            intro i _
            rw [map_smul, norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)
              (by simpa only [Real.norm_eq_abs] using hb i) (abs_nonneg _) (norm_nonneg _)
          _ = d * H * ‖x‖ := by simp; ring
      apply h_linear_norm_le_coordinate_bound _
      intro i
      have h_holderBall_coordinate_bound : |coordinateDerivative f 1 (fun _ => i) z| ≤ H := by
        have hreg := holderBall_regular f t H hf
        change holderNorm f t ≤ ENNReal.ofReal H at hf
        have hp : ENNReal.ofReal |coordinateDerivative f 1 (fun _ => i) z| ≤ derivativeSup f (holderOrder t) :=
          le_iSup_of_le 1 (le_iSup_of_le hk (le_iSup_of_le (fun _ => i)
            (le_iSup_of_le z (le_iSup_of_le hz le_rfl))))
        exact (ENNReal.ofReal_le_ofReal_iff hH).mp (hp.trans (by unfold holderNorm at hf; rw [ite_eq_left hreg] at hf; exact le_trans le_self_add hf))
      have hb := h_holderBall_coordinate_bound
      simpa only [coordinateDerivative, iteratedFDerivWithin_one_apply ((uniqueDiffOn_cube d) z hz)] using hb
    have hlip := (convex_cube d).norm_image_sub_le_of_norm_fderivWithin_le (hreg.2.differentiableOn (by simpa using (by omega))) hbound hy hx
    rw [Real.norm_eq_abs] at hlip
    rw [min_eq_right (le_of_not_ge ht), Real.rpow_one]
    exact hlip.trans (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))
theorem multilinear_coordinate_expansion 
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (v ) :
    L v = ∑ σ : Fin q → Fin d, (∏ i, v i (σ i)) *
      L (fun i => EuclideanSpace.single (σ i) 1) := by
  have hv : v = fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j 1 := by
    funext i
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  change L.toMultilinearMap (fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j 1) = _
  rw [L.toMultilinearMap.map_sum]
  simp only [L.toMultilinearMap.map_smul_univ, smul_eq_mul]
  rfl
theorem multilinear_norm_le_coordinate_bound 
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (H ) (hH : 0 ≤ H)
    (hb : ∀ σ : Fin q → Fin d, |L (fun i => EuclideanSpace.single (σ i) 1)| ≤ H) :
    ‖L‖ ≤ d ^ q * H := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  rw [multilinear_coordinate_expansion]
  calc
    _ ≤ ∑ σ : Fin q → Fin d,
        ‖(∏ i, v i (σ i)) * L (fun i => EuclideanSpace.single (σ i) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin q → Fin d, (∏ i, ‖v i‖) * H := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, Real.norm_eq_abs, Finset.abs_prod]
      apply mul_le_mul _ (hb σ) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) (σ i))
    _ = d ^ q * H * ∏ i, ‖v i‖ := by simp; ring
theorem holderBall_iteratedFDerivWithin_modulus  (f t H) (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    (x y ) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    ‖iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x -
      iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y‖ ≤
      d ^ holderOrder t * H * ‖x - y‖ ^ holderExponent t := by
  have hbound := multilinear_norm_le_coordinate_bound
    (iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x -
      iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y)
    (H * ‖x - y‖ ^ holderExponent t) (by positivity) (fun σ => by
      simpa only [sub_apply, coordinateDerivative] using
        holderBall_coordinate_modulus f t H hH hf σ x y hx hy)
  simpa only [mul_assoc] using hbound
def multilinearPolynomial 
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ σ : Fin q → Fin d, C (L (fun i => EuclideanSpace.single (σ i) 1)) *
    ∏ i, (X (σ i) - C (x (σ i)))
theorem multilinearPolynomial_eval 
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (x y : Covariate d) :
    MvPolynomial.eval (fun i => y i) (multilinearPolynomial L x) = L (fun _ => y - x) := by
  simp only [multilinearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, map_sub, MvPolynomial.eval_X]
  rw [multilinear_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [PiLp.sub_apply]
  ring
theorem multilinearPolynomial_degree 
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (x : Covariate d) : (multilinearPolynomial L x).totalDegree ≤ q := by
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin q, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])
    _ = q := by simp
def holderTaylorPolynomial  (f : Covariate d → ℝ) (k : ℕ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ q ∈ Finset.range (k + 1), C ((q.factorial : ℝ)⁻¹) *
    multilinearPolynomial (iteratedFDerivWithin ℝ q f (cube d) x) x
theorem holderTaylorPolynomial_degree  (f : Covariate d → ℝ) (k : ℕ)
    (x : Covariate d) : (holderTaylorPolynomial f k x).totalDegree ≤ k := by
  apply totalDegree_finsetSum_le
  intro q hq
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (multilinearPolynomial_degree _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hq))
def linePath  (x y : Covariate d) : ℝ →ᴬ[ℝ] Covariate d :=
  ContinuousAffineMap.lineMap x y
lemma linePath_mem_cube  (x y ) (hx : x ∈ cube d)
    (hy : y ∈ cube d) (z ) (hz : z ∈ Icc (0 : ℝ) 1) : linePath x y z ∈ cube d := (convex_cube d).segment_subset hx hy (lineMap_mem_segment ℝ x y hz)
@[simp] lemma linePath_zero  (x y : Covariate d) : linePath x y 0 = x := by
  simp [linePath, ContinuousAffineMap.coe_lineMap_eq]
@[simp] lemma linePath_one  (x y : Covariate d) : linePath x y 1 = y := by
  simp [linePath, ContinuousAffineMap.coe_lineMap_eq]
theorem linePath_iteratedDerivWithin  (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ k f (cube d)) (hq : q ≤ k)
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d)
    (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin q (f ∘ linePath x y) (Icc ↑0 1) z =
      iteratedFDerivWithin ℝ q f (cube d) (linePath x y z) (fun _ => y - x) := by
  have hseries := ((hf.ftaylorSeriesWithin (uniqueDiffOn_cube d)).comp_continuousAffineMap
    (linePath x y)).mono (fun z hz => linePath_mem_cube x y hx hy z hz)
  have he := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := q)
    (by exact_mod_cast hq) (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hz
  have hh := congrArg (fun L => L (fun _ => 1)) he.symm
  have h_linePath_contLinear_one : (linePath x y).contLinear 1 = y - x := by
    simp [linePath, ContinuousAffineMap.coe_contLinear, AffineMap.lineMap_linear]
  simpa only [iteratedDerivWithin, ftaylorSeriesWithin,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, h_linePath_contLinear_one] using hh
theorem linePath_contDiffOn  (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ k f (cube d))
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    ContDiffOn ℝ k (f ∘ linePath x y) (Icc 0 1) := hf.comp (linePath x y).contDiff.contDiffOn (fun z hz => linePath_mem_cube x y hx hy z hz)
theorem linePath_taylor_eq  (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ k f (cube d))
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    taylorWithinEval (f ∘ linePath x y) k (Icc ↑0 1) 0 1 =
      MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f k x) := by
  have h_holderTaylorPolynomial_eval : MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f k x) =
      ∑ q ∈ Finset.range (k + 1), (q.factorial : ℝ)⁻¹ *
        iteratedFDerivWithin ℝ q f (cube d) x (fun _ => y - x) := by
    simp [holderTaylorPolynomial, multilinearPolynomial_eval]
  rw [taylor_within_apply, h_holderTaylorPolynomial_eval]
  apply Finset.sum_congr rfl
  intro q hq
  rw [linePath_iteratedDerivWithin f hf (Nat.le_of_lt_succ (Finset.mem_range.mp hq))
    x y hx hy 0 (by constructor <;> norm_num), linePath_zero]
  simp
theorem holderTaylorPolynomial_error  (f t H) (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    (x y ) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |f y - MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f (holderOrder t) x)| ≤
      (d ^ holderOrder t * H / (holderOrder t).factorial) * ‖y - x‖ ^ t := by
  have hreg := holderBall_regular f t H hf
  cases hk : holderOrder t with
  | zero =>
    have h_holderTaylorPolynomial_zero_eval : MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f 0 x) = f x := by
      simp [holderTaylorPolynomial, multilinearPolynomial_eval, iteratedFDerivWithin_zero_apply]
    rw [h_holderTaylorPolynomial_zero_eval]
    have hh := holderBall_coordinate_modulus f t H hH hf
      (fun i => Fin.elim0 (show Fin 0 from hk ▸ i)) y x hy hx
    rw [coordinateDerivative_of_order_zero f _ hk, coordinateDerivative_of_order_zero f _ hk] at hh
    simpa [hk, holderExponent] using hh
  | succ n =>
    have hft : ContDiffOn ℝ (n + 1) f (cube d) := by simpa [hk] using hreg.2
    let F : ℝ → ℝ := f ∘ linePath x y
    have hF  := linePath_contDiffOn f hft x y hx hy
    have hd := hF.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n)
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    obtain ⟨z, hz, hrem⟩ := taylor_mean_remainder_lagrange (f := F) (n := n)
      (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (by norm_num)
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hF.of_succ)
      (by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1),
        uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hd.mono Ioo_subset_Icc_self)
    have hz' : z ∈ Icc (0 : ℝ) 1 := by
      have hzo : z ∈ Ioo (0 : ℝ) 1 := by
        simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hz
      exact ⟨hzo.1.le, hzo.2.le⟩
    have hzCube := linePath_mem_cube x y hx hy z hz'
    have hD := holderBall_iteratedFDerivWithin_modulus f t H hH hf (linePath x y z) x hzCube hx
    rw [hk] at hD
    have hD' : ‖iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) -
        iteratedFDerivWithin ℝ (n + 1) f (cube d) x‖ ≤
        d ^ (n + 1) * H * ‖y - x‖ ^ holderExponent t := by
      apply hD.trans
      have h_linePath_sub_base_norm_le : ‖linePath x y z - x‖ ≤ ‖y - x‖ := by
        simp only [linePath, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module',
          add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hz'.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hz'.2
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) h_linePath_sub_base_norm_le
          (holderExponent_pos hreg.1).le) (by positivity)
    have hDD : |iteratedDerivWithin (n + 1) F (Icc 0 1) z -
        iteratedDerivWithin (n + 1) F (Icc 0 1) 0| ≤
        d ^ (n + 1) * H * ‖y - x‖ ^ holderExponent t * ‖y - x‖ ^ (n + 1) := by
      rw [linePath_iteratedDerivWithin f hft le_rfl x y hx hy z hz',
        linePath_iteratedDerivWithin f hft le_rfl x y hx hy 0 (by constructor <;> norm_num),
        linePath_zero, ← Real.norm_eq_abs]
      have hb := (iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) -
        iteratedFDerivWithin ℝ (n + 1) f (cube d) x).le_opNorm (fun _ => y - x)
      have hb' : ‖iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) (fun _ => y - x) -
          iteratedFDerivWithin ℝ (n + 1) f (cube d) x (fun _ => y - x)‖ ≤
          ‖iteratedFDerivWithin ℝ (n + 1) f (cube d) (linePath x y z) -
            iteratedFDerivWithin ℝ (n + 1) f (cube d) x‖ * ‖y - x‖ ^ (n + 1) := by
        simpa only [sub_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb
      exact hb'.trans
        (mul_le_mul_of_nonneg_right hD' (by positivity))
    have herror : f y - MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f (n + 1) x) =
        (iteratedDerivWithin (n + 1) F (Icc 0 1) z -
          iteratedDerivWithin (n + 1) F (Icc 0 1) 0) / (n + 1).factorial := by
      rw [← (linePath_taylor_eq f hft x y hx hy), taylorWithinEval_succ]
      have hr : F 1 - taylorWithinEval F n (Icc 0 1) 0 1 =
          iteratedDerivWithin (n + 1) F (Icc (0 : ℝ) 1) z / (n + 1).factorial := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), sub_zero, one_pow, mul_one] using hrem
      have hf1 : F 1 = f y := by simp [F]
      rw [hf1] at hr
      simp only [sub_zero, one_pow, mul_one, smul_eq_mul]
      rw [Nat.factorial_succ]
      push_cast
      rw [Nat.factorial_succ] at hr
      push_cast at hr
      linear_combination hr
    rw [herror, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ↑(n + 1).factorial)]
    apply (div_le_div_of_nonneg_right hDD (by positivity)).trans_eq
    have he : holderExponent t + (n + 1 : ℕ) = t := by
      simp only [holderExponent, hk]
      ring
    have hepow : ‖y - x‖ ^ holderExponent t * ‖y - x‖ ^ (n + 1) = ‖y - x‖ ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_add_of_nonneg (norm_nonneg _)
        (holderExponent_pos hreg.1).le (by positivity), he]
    calc
      _ = (d ^ (n + 1) * H / (n + 1).factorial) *
          (‖y - x‖ ^ holderExponent t * ‖y - x‖ ^ (n + 1)) := by ring
      _ = _ := by rw [hepow]
end RoughRegime.Model
end
open Set
open scoped BigOperators ContDiff ENNReal
namespace NearlyMinimax
variable {d : ℕ}
def euclideanCoordinates (d ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Covariate d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ => ℝ)
def euclideanPoint  (x : Covariate d) : EuclideanSpace ℝ (Fin d) :=
  (euclideanCoordinates d).symm x
def euclideanExtension  (F : Covariate d → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  F ∘ euclideanCoordinates d
@[simp] theorem euclideanPoint_apply  (x : Covariate d) (i : Fin d) :
    euclideanPoint x i = x i := rfl
@[simp] theorem euclideanCoordinates_point  (x ) :
    euclideanCoordinates d (euclideanPoint x) = x :=
  (euclideanCoordinates d).apply_symm_apply x
theorem euclideanCoordinates_norm  (x ) :
    euclideanNorm (euclideanCoordinates d x) = ‖x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  have h_euclideanCoordinates_apply (i) : euclideanCoordinates d x i = x i := rfl
  simp only [h_euclideanCoordinates_apply, Real.norm_eq_abs, sq_abs]
theorem euclideanPoint_norm  (x : Covariate d) :
    ‖euclideanPoint x‖ = euclideanNorm x := by
  rw [← euclideanCoordinates_norm, euclideanCoordinates_point]
theorem euclideanExtension_coordinateDerivative {d ℓ q : ℕ}
    (U : Set (Covariate d)) (hU : IsOpen U) (F : Covariate d → ℝ)
    (hf : ContDiffOn ℝ ℓ F U) (hcube : unitCube d ⊆ U) (hq : q ≤ ℓ)
    (σ : Fin q → Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ RoughRegime.Model.cube d) :
    RoughRegime.Model.coordinateDerivative (euclideanExtension F) q σ x =
      iteratedFDeriv ℝ q F (euclideanCoordinates d x)
        (fun j => Pi.single (σ j) 1) := by
  have hqf : ContDiffOn ℝ q F U := hf.of_le (by exact_mod_cast hq)
  have hreg := hqf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap
  have hopen : IsOpen ((euclideanCoordinates d) ⁻¹' U) :=
    hU.preimage (euclideanCoordinates d).continuous
  have hxU : euclideanCoordinates d x ∈ U := hcube hx
  have hat : ContDiffAt ℝ q (euclideanExtension F) x :=
    hreg.contDiffAt (hopen.mem_nhds hxU)
  rw [RoughRegime.Model.coordinateDerivative_eq_iteratedFDeriv _ q σ x hx hat]
  have he := (euclideanCoordinates d).iteratedFDerivWithin_comp_right
    F uniqueDiffOn_univ (x := x) (mem_univ _) q
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at he
  rw [show euclideanExtension F = F ∘ euclideanCoordinates d by rfl, he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  congr 1
theorem euclideanExtension_mem_holderBall  (C : ModelConstants d)
    (F : Covariate d → ℝ) (hf : ContDiffOn ℝ C.order F C.domain)
    (hNorm : holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound) :
    euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound) := by
  have h_euclideanExtension_mem_holderBall_of_coordinate_bounds (hb : ∀ q ≤ C.order, ∀ σ : Fin q → Fin d, ∀ x ∈ C.domain,
      |iteratedFDeriv ℝ q F x (fun j => Pi.single (σ j) 1)| ≤ C.holderBound) (hm : ∀ σ : Fin C.order → Fin d, ∀ x ∈ C.domain, ∀ y ∈ C.domain,
      |iteratedFDeriv ℝ C.order F x (fun j => Pi.single (σ j) 1) -
        iteratedFDeriv ℝ C.order F y (fun j => Pi.single (σ j) 1)| ≤
          C.holderBound * euclideanNorm (x - y) ^ C.alpha) : euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound) := by
    have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
    have halpha : RoughRegime.Model.holderExponent C.smoothness = C.alpha := by
      simp only [RoughRegime.Model.holderExponent, horder, ModelConstants.alpha]
    have hsup : RoughRegime.Model.derivativeSup (euclideanExtension F)
        (RoughRegime.Model.holderOrder C.smoothness) ≤ ENNReal.ofReal C.holderBound := by
      unfold RoughRegime.Model.derivativeSup
      rw [horder]
      apply iSup_le; intro q
      apply iSup_le; intro hq
      apply iSup_le; intro σ
      apply iSup_le; intro x
      apply iSup_le; intro hx
      rw [euclideanExtension_coordinateDerivative C.domain C.domain_open F hf
        C.cube_subset hq σ x hx]
      exact ENNReal.ofReal_le_ofReal (hb q hq σ _ (C.cube_subset hx))
    have hsem : RoughRegime.Model.holderSeminorm (euclideanExtension F) C.smoothness ≤
        ENNReal.ofReal C.holderBound := by
      unfold RoughRegime.Model.holderSeminorm
      rw [horder, halpha]
      apply iSup_le; intro σ
      apply iSup_le; intro x
      apply iSup_le; intro hx
      apply iSup_le; intro y
      apply iSup_le; intro hy
      apply iSup_le; intro hxy
      apply ENNReal.ofReal_le_ofReal
      have hmod := hm σ _ (C.cube_subset hx) _ (C.cube_subset hy)
      change |iteratedFDeriv ℝ C.order F (euclideanCoordinates d x)
          (fun j => Pi.single (σ j) 1) -
        iteratedFDeriv ℝ C.order F (euclideanCoordinates d y)
          (fun j => Pi.single (σ j) 1)| ≤
        C.holderBound * euclideanNorm (euclideanCoordinates d x - euclideanCoordinates d y) ^
          C.alpha at hmod
      rw [euclideanExtension_coordinateDerivative C.domain C.domain_open F hf
        C.cube_subset le_rfl σ x hx,
        euclideanExtension_coordinateDerivative C.domain C.domain_open F hf
        C.cube_subset le_rfl σ y hy]
      have hnorm : euclideanNorm (euclideanCoordinates d x - euclideanCoordinates d y) =
          ‖x - y‖ := by rw [← map_sub, euclideanCoordinates_norm]
      rw [hnorm] at hmod
      exact (div_le_iff₀ (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).2 hmod
    change RoughRegime.Model.holderNorm (euclideanExtension F) C.smoothness ≤ _
    unfold RoughRegime.Model.holderNorm
    rw [if_pos ⟨C.smoothness_pos, (by rw [horder]; apply (hf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap).mono; intro x hx; exact C.cube_subset hx)⟩]
    calc
      _ ≤ ENNReal.ofReal C.holderBound + ENNReal.ofReal C.holderBound := add_le_add hsup hsem
      _ = ENNReal.ofReal (2 * C.holderBound) := by
        rw [← ENNReal.ofReal_add C.holderBound_pos.le C.holderBound_pos.le]
        congr 1
        ring
  apply h_euclideanExtension_mem_holderBall_of_coordinate_bounds
  · intro q hq σ x hx
    let γ : Fin d → Fin (C.order + 1) := fun i =>
      ⟨(List.ofFn σ).count i,
        lt_of_le_of_lt (by simpa using (List.count_le_length (l := List.ofFn σ) (a := i)))
          (Nat.lt_succ_of_le hq)⟩
    rw [iteratedFDeriv_coordinates_eq_multiPartial C.domain C.domain_open F C.order q hf hq σ x hx]
    exact holderNorm_derivative_bound C.domain F C.order C.alpha C.holderBound C.holderBound_pos.le hNorm γ
      (by simpa only [γ, coordinate_counts_sum, List.length_ofFn] using hq) x hx
  · intro σ x hx y hy
    let γ : Fin d → Fin (C.order + 1) := fun i =>
      ⟨(List.ofFn σ).count i,
        lt_of_le_of_lt (by simpa using (List.count_le_length (l := List.ofFn σ) (a := i)))
          (Nat.lt_succ_self C.order)⟩
    rw [iteratedFDeriv_coordinates_eq_multiPartial C.domain C.domain_open F C.order C.order hf le_rfl σ x hx,
      iteratedFDeriv_coordinates_eq_multiPartial C.domain C.domain_open F C.order C.order hf le_rfl σ y hy]
    have hγ : (∑ i, (γ i).val) = C.order := by simp only [γ, coordinate_counts_sum, List.length_ofFn]
    have h_holderSeminorm_pointwise_bound (G : Covariate d → ℝ) (hseminorm : holderSeminorm C.domain G C.alpha ≤ ENNReal.ofReal C.holderBound) : |G x - G y| ≤ C.holderBound * euclideanNorm (x - y) ^ C.alpha := by
      by_cases hxy : x = y
      · subst y
        simp only [sub_self, abs_zero]
        exact mul_nonneg C.holderBound_pos.le (Real.rpow_nonneg (Real.sqrt_nonneg _) C.alpha)
      · have hraw : ENNReal.ofReal
            (|G x - G y| / euclideanNorm (x - y) ^ C.alpha) ≤ holderSeminorm C.domain G C.alpha := by
          apply le_iSup_of_le (⟨x, hx⟩ : C.domain)
          apply le_iSup_of_le (⟨y, hy⟩ : C.domain)
          simp only [hxy, if_false]
          rfl
        exact (div_le_iff₀ (Real.rpow_pos_of_pos (euclideanNorm_pos_of_ne_zero (x - y) (sub_ne_zero.mpr hxy)) C.alpha)).mp ((ENNReal.ofReal_le_ofReal_iff C.holderBound_pos.le).mp (hraw.trans hseminorm))
    apply h_holderSeminorm_pointwise_bound _ _
    apply le_trans _ hNorm
    apply le_trans _ (le_add_left le_rfl)
    apply le_iSup_of_le γ
    simp only [if_pos hγ]
    exact le_rfl
def modelTaylorPolynomial  (C : ModelConstants d) (F : Covariate d → ℝ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  RoughRegime.Model.holderTaylorPolynomial (euclideanExtension F) C.order (euclideanPoint x)
theorem modelTaylorPolynomial_degree  (C : ModelConstants d)
    (F x) :
    (modelTaylorPolynomial C F x).totalDegree ≤ C.order :=
  RoughRegime.Model.holderTaylorPolynomial_degree _ _ _
theorem modelTaylorPolynomial_error_of_holderBall  (C : ModelConstants d)
    (F )
    (hf : euclideanExtension F ∈
      RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound))
    (x y ) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) :
    |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      (d ^ C.order * (2 * C.holderBound) / C.order.factorial) *
        euclideanNorm (y - x) ^ C.smoothness := by
  have herr := RoughRegime.Model.holderTaylorPolynomial_error (euclideanExtension F)
    C.smoothness (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) hf
    (euclideanPoint x) (euclideanPoint y) hx hy
  have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
  rw [horder] at herr
  have hdiff : euclideanPoint y - euclideanPoint x = euclideanPoint (y - x) :=
    ((euclideanCoordinates d).symm.map_sub y x).symm
  rw [hdiff, euclideanPoint_norm] at herr
  simpa only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
    euclideanPoint_apply, modelTaylorPolynomial] using herr
def taylorErrorFactor  (C : ModelConstants d) : ℝ :=
  (2 * d ^ C.order / C.order.factorial) *
    (Real.sqrt d) ^ C.smoothness
theorem taylorErrorFactor_pos  (C : ModelConstants d) :
    0 < taylorErrorFactor C := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast C.dimension_pos
  exact mul_pos (div_pos (mul_pos (by norm_num) (pow_pos hd _))
    (by exact_mod_cast Nat.factorial_pos _)) (Real.rpow_pos_of_pos (Real.sqrt_pos.2 hd) _)
theorem modelTaylorPolynomial_cell_error  (C : ModelConstants d)
    (F ) (hf : ContDiffOn ℝ C.order F C.domain)
    (hNorm : holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound)
    (x y ) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (h ) (hh : 0 ≤ h) (hxy : ∀ i, |y i - x i| ≤ h) :
    |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      taylorErrorFactor C * C.holderBound * h ^ C.smoothness :=
  have h_modelTaylorPolynomial_cell_error_of_holderBall (hf : euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness (2 * C.holderBound)) (x) (y) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (h) (hh : 0 ≤ h) (hxy : ∀ i, |y i - x i| ≤ h) : |F y - MvPolynomial.eval y (modelTaylorPolynomial C F x)| ≤
      taylorErrorFactor C * C.holderBound * h ^ C.smoothness := by
    have he := modelTaylorPolynomial_error_of_holderBall C F hf x y hx hy
    have hr := euclideanNorm_le_coordinate_radius (y - x) h hh hxy
    have hp := Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hr C.smoothness_pos.le
    have hcoef : 0 ≤ d ^ C.order * (2 * C.holderBound) / C.order.factorial := by
      exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
        (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
    calc
      _ ≤ (d ^ C.order * (2 * C.holderBound) / C.order.factorial) *
          euclideanNorm (y - x) ^ C.smoothness := he
      _ ≤ (d ^ C.order * (2 * C.holderBound) / C.order.factorial) *
          (Real.sqrt d * h) ^ C.smoothness := mul_le_mul_of_nonneg_left hp hcoef
      _ = _ := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) hh]
        unfold taylorErrorFactor
        ring
  h_modelTaylorPolynomial_cell_error_of_holderBall
    (euclideanExtension_mem_holderBall C F hf hNorm) x y hx hy h hh hxy
end NearlyMinimax
