module
public import DensityStrip.Low
public import LaterPairs.PairPhysicalExcess

/-! Control of the shifted contour by the positive excess of critical-line
zeta above a fixed power threshold. The Gamma weights, including their
real parts, are allowed to vary from one zero to the next. -/
@[expose] public section
noncomputable section
open Real Complex MeasureTheory Filter Finset Set MathCollab.Density MathCollab.Density.Stronger
open GuthMaynard.Improvement Montgomery.RationalMoment.RightDetector TaoTrudgianYang2025
namespace DensityStrip

private abbrev gamma (β v : ℝ) := ‖Complex.Gamma (((1/2-β:ℝ):ℂ)+(v:ℂ)*I)‖
private abbrev band (T : ℝ) := Icc (-(T/2)) (T/2)

private theorem local_excess {s y q e : ℝ} (hs : 1/2<s) (hy : 0<y) (he : e≤1)
    (hg : q+e < y*(s-1/2)) : ∀ᶠ T : ℝ in atTop, ∀ {ρ : ℂ}, s ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ 2*T →
      1/3 ≤ ‖detectorIntegral ρ (T^e) (T^y)‖ →
      T^q ≤ ∫ v in band T, gamma ρ.re v*criticalExcess (T^q) (ρ.im+v) := by
  obtain ⟨G,hG,hmass⟩ := uniform_detector_gamma_mass hs
  have hgap : 0<y*(s-1/2)-q-e := by linarith
  filter_upwards [eventually_ge_atTop (1:ℝ), contour_window hs,
    (tendsto_rpow_atTop hgap).eventually_gt_atTop (6*(G+1))] with T hT hnear hmargin
  intro ρ hβ hβ' hγ hdet
  let X := T^e; let Y := T^y; let V := T^q
  have ht : 0<T := by linarith
  have hx : 0<X := rpow_pos_of_pos ht _
  have hx' : X≤T := (rpow_le_rpow_of_exponent_le hT he).trans_eq (rpow_one _)
  have hy' : 1≤Y := one_le_rpow hT hy.le
  have hYpos : 0<Y := zero_lt_one.trans_le hy'
  have hv : 0<V := rpow_pos_of_pos ht _
  have hn := hnear hx.le (by linarith) hy' hβ hβ' hγ hdet
  let g := gamma ρ.re
  let F := fun t : ℝ => criticalExcess V (ρ.im+t)
  have hc : Continuous g := (continuous_Gamma_detector_strip (by linarith) (by linarith)).norm
  have hf : Continuous F := (criticalExcess_continuous V).comp (continuous_const.add continuous_id)
  have hi := hmass ρ.re hβ hβ'
  have hG' : (∫ t in band T,g t) ≤ G := calc
    _ ≤ ∫ t,g t := setIntegral_le_integral hi.1.norm (Eventually.of_forall fun t => norm_nonneg _)
    _ ≤ ∫ t : ℝ,(1+|t|)*g t := integral_mono hi.1.norm hi.2.1 fun t => le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg t])
    _ ≤ _ := hi.2.2
  have hcap : (∫ t in band T,g t*mollifiedNorm X (ρ.im+t)) ≤ X*(G*V+∫ t in band T,g t*F t) := calc
    _ ≤ ∫ t in band T, X*(g t*V+g t*F t) := by
      apply integral_mono ((hc.mul ((mollifiedNorm_continuous X).comp (continuous_const.add continuous_id))).integrableOn_Icc)
        (((hc.mul_const V).add (hc.mul hf)).const_mul X).integrableOn_Icc
      intro t
      have hm := (norm_zetaMollifier_le_cutoff X (s := (1/2:ℂ)+((ρ.im+t:ℝ):ℂ)*I) (by norm_num)).trans (Nat.floor_le hx.le)
      have hz : ‖riemannZeta ((1/2:ℂ)+((ρ.im+t:ℝ):ℂ)*I)‖ ≤ V + F t := by
        simpa [zetaMomentCriticalNorm,F] using critical_norm_le_threshold_add_excess V (ρ.im+t)
      have hpos : 0 ≤ V+F t := add_nonneg hv.le (criticalExcess_nonneg ..)
      have hbound := mul_le_mul hz hm (norm_nonneg _) hpos
      change g t*mollifiedNorm X (ρ.im+t) ≤ X*(g t*V+g t*F t)
      rw [mollifiedNorm,norm_mul]
      apply (mul_le_mul_of_nonneg_left hbound (norm_nonneg _ : 0≤g t)).trans_eq
      change g t*((V+F t)*X) = X*(g t*V+g t*F t)
      ring
    _ ≤ _ := by
      have h₁ : IntegrableOn (fun t => g t*V) (band T) := (hc.mul_const V).integrableOn_Icc
      have h₂ : IntegrableOn (fun t => g t*F t) (band T) := (hc.mul hf).integrableOn_Icc
      rw [integral_const_mul,integral_add h₁ h₂,integral_mul_const]; gcongr
  by_contra! hbad
  have hsink := lt_of_le_of_lt hcap (mul_lt_mul_of_pos_left (add_lt_add_right hbad _) hx)
  have hbig := hn.trans_lt (mul_lt_mul_of_pos_left hsink (rpow_pos_of_pos hYpos _))
  have hY := rpow_le_rpow_of_exponent_le hy' (show 1/2-ρ.re ≤ 1/2-s by linarith)
  have hstop : Y^(1/2-ρ.re)*(X*(G*V+V)) < 1/6 := calc
    _ ≤ Y^(1/2-s)*(X*(G*V+V)) := by gcongr
    _ = (G+1)/T^(y*(s-1/2)-q-e) := by
      dsimp only [Y,X,V]; rw [← rpow_mul ht.le,div_eq_mul_inv (G+1),← rpow_neg ht.le,
        show -(y*(s-1/2)-q-e) = y*(1/2-s)+e+q by ring]; simp only [rpow_add ht]; ring
    _ < _ := (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith only [hmargin])
  exact (lt_asymm hbig hstop)

/-- Pack the local excess windows before estimating the physical tail. -/
theorem count_of_excess {s y q e P : ℝ} (hs : 1/2<s) (hy : 0<y) (he : e≤1) (hg : q+e < y*(s-1/2))
    (hE : ∃ C : ℝ, 0<C ∧ ∀ᶠ T : ℝ in atTop, (∫ t in Icc 0 (3*T),criticalExcess (T^q) t) ≤ C*(T^q*T^P)) : IntegralCount s y e P := by
  obtain ⟨C,hC,hE⟩ := hE
  obtain ⟨B,hB,hpack⟩ := short_typeII_window_packing hs
  refine ⟨B*C,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),local_excess hs hy he hg,hE] with T ht hlocal hexc
  intro W z hsep hloc hz hd
  let V := T^q
  have h (u : ℝ) (hu : u∈W) := hlocal (hz u hu).2.1 (hz u hu).2.2 (by rw [(hz u hu).1,abs_of_nonneg (ht.trans_le (hloc u hu).1).le]; exact (hloc u hu).2) (hd u hu)
  have hsum := Finset.sum_le_sum h
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hs' : (W.card:ℝ)*V ≤ _ := hsum.trans ((Finset.sum_congr rfl (fun t ht => by rw [(hz t ht).1])).le)
  have hp := hpack T _ (criticalExcess_continuous V) (criticalExcess_nonneg V) ht.le W z hsep hloc (fun t h => (hz t h).2)
  have hi : (∫ t in Icc (T/2) (3*T),criticalExcess V t) ≤ ∫ t in Icc 0 (3*T),criticalExcess V t :=
    setIntegral_mono_set (criticalExcess_continuous V).integrableOn_Icc (Eventually.of_forall (criticalExcess_nonneg _))
      (Eventually.of_forall (Icc_subset_Icc_left (by linarith)))
  apply (mul_le_mul_iff_left₀ (rpow_pos_of_pos ht q)).mp
  exact (hs'.trans (hp.trans (mul_le_mul_of_nonneg_left (hi.trans hexc) hB.le))).trans_eq (by ring)

end DensityStrip
