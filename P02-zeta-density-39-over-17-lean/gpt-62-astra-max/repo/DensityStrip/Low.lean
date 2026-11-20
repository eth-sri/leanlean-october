module
public import MathCollab.Density.Stronger.BlockFamily
public import MathCollab.Density.Stronger.LongScalarBudget
public import MathCollab.Density.LocalZeroCount
public import MathCollab.Density.DensityDyadicSummation
public import GuthMaynard.Improvement.RealIntegerSource
public import GuthMaynard.Improvement.ShortTypeIICount
public import GuthMaynard.Improvement.WeakShortMoment

/-! Below three quarters one can smooth at `Y = √T`. Every surviving
block can then be powered into the counting window; the other alternative
costs only the ordinary critical-line fourth moment. -/
@[expose] public section
noncomputable section
open Real Filter Finset MathCollab.Density MathCollab.Density.Stronger GuthMaynard.Improvement
namespace DensityStrip

private theorem detection {u s a e y : ℝ} (hu : 1/2≤u) (hs : u < s) (hy : 0 < y) (hy' : y < 3*a/4) (ha' : a < 4/3)
    (he : 0 < e) (he' : e ≤ 1) : ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ zetaZeroFinset s T (2*T),
    let X := T^e; let Y := T^y
    1/3 ≤ ‖detectorIntegralOn u ρ X Y‖ ∨ ∃ q ∈ BlockFamily.list Y T a e,
      (BlockFamily.length q:ℝ)^s*T^(-2*e) ≤
        ‖detectingPolynomial (BlockFamily.length q) (BlockFamily.coeff e T X Y q) ρ.im‖ := by
  have hlim := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 72
  simp only [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop (1:ℝ), (tendsto_rpow_atTop hy).eventually_ge_atTop 8,
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/24)), large_block_of_tail,
    BlockFamily.covers (by linarith : 0<a) ha' he he,
    log_pow_eventually_le_rpow 2 (by linarith : 0<3*a/4-y)] with T hT h8 hres hblock hcov hlog
  intro ρ hρ
  obtain ⟨⟨hz,_,hβ'⟩,hβ,hlo,hhi⟩ := mem_zetaZeroFinset.mp hρ
  have ht : 0<T := by linarith
  let X := T^e; let Y := T^y
  have hX := one_le_rpow hT he.le
  have hXT : X ≤ T := (rpow_le_rpow_of_exponent_le hT he').trans_eq (rpow_one _)
  have hYT : Y ≤ T := (rpow_le_rpow_of_exponent_le hT (by linarith : y ≤ 1)).trans_eq (rpow_one _)
  have hY : 1 ≤ Y := by change 1 ≤ T^y; linarith
  have hYp : 0<Y := zero_lt_one.trans_le hY
  have hβ0 := (by linarith : 0 ≤ ρ.re)
  have hres' := norm_residue_le (X:=X) (Y:=Y) hT (zero_le_one.trans hX) hXT hY hYT (by linarith) hβ'.le
    (by rwa [abs_of_nonneg (ht.trans_le hlo).le]) (by rwa [abs_of_nonneg (ht.trans_le hlo).le])
  change 1/3 ≤ ‖detectorIntegralOn u ρ X Y‖ ∨ _
  apply or_iff_not_imp_left.mpr; intro hsmall
  have hd := detectorTail_decomposition (ρ:=ρ) hX hYp hβ0
  rw [smoothedDetector_contour_identity hY (hs.trans_le hβ) hβ' hz hu] at hd
  have heq : ((exp (-1/Y):ℝ):ℂ) = detectorResidue ρ X Y + detectorIntegralOn u ρ X Y - detectorTail ρ X Y := by
    change _ = detectorResidue ρ X Y + detectorIntegralOn u ρ X Y at hd
    linear_combination hd
  have hb := norm_sub_le (detectorResidue ρ X Y + detectorIntegralOn u ρ X Y) (detectorTail ρ X Y)
  rw [← heq, Complex.norm_real, Real.norm_eq_abs,abs_of_pos (exp_pos _)] at hb
  have hinv := (div_le_iff₀ hYp).mpr (by change 1 ≤ 1/8*Y; linarith only [show 8≤Y from h8] : 1 ≤ 1/8*Y)
  have htail : 1/2 ≤ ‖detectorTail ρ X Y‖ := by
    change 72*(T^3*exp (-T)) < 1/24 at hres
    have hr := hres'.trans_lt (show 72 * T^3 * exp (-T) < 1/24 by rwa [mul_assoc])
    have hfirst : 7/8 ≤ exp (-1/Y) := by
      have h := Real.add_one_le_exp (-1/Y)
      rw [neg_div] at h ⊢
      linarith only [hinv,h]
    linarith only [hr,lt_of_not_ge hsmall,hfirst,hb,norm_add_le (detectorResidue ρ X Y) (detectorIntegralOn u ρ X Y)]
  obtain ⟨j,hj,hlo,hb⟩ := hblock (zero_le_one.trans hX) hXT hY hYT hβ0 htail
  apply hcov (by linarith : 0≤ s) hβ hβ'.le hYp hj hlo _ hb
  apply (mem_smoothScaleIndices.mp hj).2.trans
  calc
    _ ≤ Y*T^(3*a/4-y) := by gcongr
    _ = _ := by dsimp [Y]; rw [← rpow_add ht]; congr 1; ring

/-- Large-value input at the powered length. The loss coefficient `k`
keeps track of the normalization and dyadic enlargement. -/
abbrev WindowCount (s a p k e : ℝ) := ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
  ∀ (Q : ℕ), let N : ℝ := Q
    ∀ (b : ℕ → ℂ) (W : Finset ℝ), 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+e) →
    (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → (∀ t ∈ W, T ≤ t ∧ t ≤ T+T) → oneSeparated W →
    (∀ t ∈ W, N^s*T^(-2*e) ≤ ‖boundedPolynomial N b t‖) → (W.card:ℝ) ≤ C*T^(p+k*e)

/-- A finite family is counted at one fixed member at a time. -/
theorem card_covered {α β : Type*} [DecidableEq α] {S A : Finset α} {J : Finset β} {f : β → Finset α}
    {C : ℝ} (hc : ∀ q ∈ J, ((f q).card:ℝ) ≤ C) (h : S ⊆ A ∪ J.biUnion f) :
    (S.card:ℝ) ≤ (A.card:ℝ)+(J.card:ℝ)*C := calc
  _ ≤ (A.card:ℝ) + ∑ q ∈ J, ((f q).card:ℝ) := by
    exact_mod_cast (card_le_card h).trans <| (card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _)
  _ ≤ _ := by simpa using add_le_add_left (sum_le_sum hc) (A.card:ℝ)

/-- Estimate for separated ordinates on which the shifted contour, instead
of a powered Dirichlet block, supplies the detection. -/
abbrev IntegralCount (s y e P : ℝ) (u : ℝ := 1/2) := ∃ D : ℝ, 0<D ∧ ∀ᶠ T : ℝ in atTop,
  ∀ (W : Finset ℝ) (z : ℝ → ℂ), oneSeparated W → (∀ t ∈ W, t ∈ Set.Icc T (2*T)) →
    (∀ t ∈ W, (z t).im = t ∧ s ≤ (z t).re ∧ (z t).re ≤ 1) →
    (∀ t ∈ W, 1/3 ≤ ‖detectorIntegralOn u (z t) (T^e) (T^y)‖) → (W.card:ℝ) ≤ D*T^P

/-- Choose the smoothing power strictly below the top of the short-block
range. No intermediate long polynomial is needed: the two contributors
are the short family and the actual shifted-contour integral. -/
theorem window_density {u s a p k y e ε : ℝ} (hs : u < s) (hp : 0 ≤ p)
    (hy : 0<y) (hy' : y<3*a/4) (ha' : a<4/3) (he : 0<e) (he' : e≤1)
    (hW : WindowCount s a p k e) (hI : IntegralCount s y e (p+k*e) u) (hε : 0<ε) (heε : (k+4)*e ≤ ε) (hu : 1/2≤u := by norm_num) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → (zetaDensityCount s T:ℝ) ≤ C*T^(p+ε) := by
  classical
  obtain ⟨C,hC,hwin⟩ := hW
  obtain ⟨D,hD,hmass⟩ := hI
  obtain ⟨L,hL,hl⟩ := zeta_local_multiplicity_bound
  apply zetaDensity_bound_of_eventual_slabs (by linarith only [hp,hε]) (show 0 < D+C by positivity)
  have hsmall := (tendsto_rpow_atTop he).eventually_ge_atTop
  filter_upwards [eventually_ge_atTop (2:ℝ),hwin,hmass,detection hu hs hy hy' ha' he (by linarith),
    BlockFamily.valid (δ:=e) he ha',BlockFamily.size a e,log_pow_eventually_le_rpow 2 he,
    log_pow_eventually_le_rpow 1 he, hsmall (4*L),hsmall (144*(BlockFamily.bound a e:ℝ)^2),
    hsmall ((2:ℝ)^BlockFamily.bound a e), (tendsto_rpow_atTop (by linarith : 0<a)).eventually_ge_atTop 2]
    with T hT hw hmass hd hv hsize hlog2 hlog h4 h144 hK h2
  have ht : 0<T := by linarith
  have ht1 : 1≤T := by linarith
  have hab : 0 ≤ log (2*T) := log_nonneg (by linarith)
  obtain ⟨R,hR,hcard,hsep,hrestore⟩ := zetaSlab_separated_representatives s T (2*T) (mul_nonneg hL.le hab) (hl s T (hu.trans hs.le) hT)
  let W := R.image Complex.im
  have hrepr (t : ℝ) : ∃ z : ℂ, t ∈ W → z ∈ R ∧ z.im=t := by
    by_cases h : t∈W
    · obtain ⟨z,hz,hz'⟩ := mem_image.mp h; exact ⟨z,fun _ => ⟨hz,hz'⟩⟩
    · exact ⟨0,fun hh => (h hh).elim⟩
  choose z hz using hrepr
  have hloc t (ht : t∈W) := mem_zetaZeroFinset.mp (hR (hz t ht).1)
  let X := T^e; let Y := T^y; let J := BlockFamily.list Y T a e
  have hx : 0≤X := (rpow_pos_of_pos ht _).le
  have hxT : X ≤ T := (rpow_le_rpow_of_exponent_le ht1 (by linarith : e≤1)).trans_eq (rpow_one _)
  have hy : 1≤Y := one_le_rpow ht1 hy.le
  have hyT : Y ≤ T := (rpow_le_rpow_of_exponent_le ht1 (by linarith : y ≤ 1)).trans_eq (rpow_one _)
  let A := W.filter (fun t => 1/3 ≤ ‖detectorIntegralOn u (z t) X Y‖)
  let b := BlockFamily.coeff e T X Y
  let Q := BlockFamily.length
  let Wq := fun q => W.filter (fun t => (Q q:ℝ)^s*T^(-2*e) ≤ ‖detectingPolynomial (Q q) (b q) t‖)
  have hinc : W ⊆ A ∪ J.biUnion Wq := by
    intro t h
    rcases hd (z t) (hR (hz t h).1) with hI | ⟨q,hq,hh⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨h,hI⟩)
    · rw [(hz t h).2] at hh
      exact mem_union_right _ (mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨h,hh⟩⟩)
  have hpoly q (hq : q∈J) : ((Wq q).card:ℝ) ≤ C*T^(p+k*e) := by
    obtain ⟨hlo,hhi,hunit⟩ := hv (X:=X) (zero_lt_one.trans_le hy) hq
    refine hw _ _ _ (h2.trans hlo) hlo ?_ (fun n _ => hunit n) ?_ (oneSeparated_subset hsep (filter_subset ..)) ?_
    · apply hhi.trans
      rw [rpow_add ht,mul_comm]; gcongr
    · intro t ht; have h := (mem_filter.mp ht).1
      have H := (hloc t h).2.2
      rw [(hz t h).2] at H
      exact ⟨H.1,by linarith only [H.2]⟩
    · intro t ht; exact (mem_filter.mp ht).2.trans_eq (congrArg norm (detectingPolynomial_eq_boundedPolynomial ..))
  have hA : (A.card:ℝ) ≤ D*T^(p+k*e) := by
    exact hmass A z (oneSeparated_subset hsep (filter_subset ..)) (by
      intro t ht; have h := (mem_filter.mp ht).1; simpa only [(hz t h).2,Set.mem_Icc] using (hloc t h).2.2) (by
      intro t ht; have h := (mem_filter.mp ht).1; exact ⟨(hz t h).2,(hloc t h).2.1,(hloc t h).1.2.2.le⟩)
      (fun t ht => (mem_filter.mp ht).2)
  have hJ : (J.card:ℝ) ≤ T^(2*e) := (hsize hy hyT).trans <| (mul_le_mul h144 hlog2 (sq_nonneg _) hx).trans_eq <|
    by rw [← rpow_add ht]; congr 1; ring
  have hge := one_le_rpow ht1 (show 0 ≤ 2*e by linarith)
  have hWcard := card_covered hpoly hinc
  have hsum : (W.card:ℝ) ≤ (D+C)*T^(p+(k+2)*e) := calc
    _ ≤ D*T^(p+k*e) + T^(2*e)*(C*T^(p+k*e)) := hWcard.trans (by gcongr)
    _ ≤ T^(2*e)*(D*T^(p+k*e)) + T^(2*e)*(C*T^(p+k*e)) := add_le_add (le_mul_of_one_le_left (by positivity : 0 ≤ D*T^(p+k*e)) hge) le_rfl
    _ = _ := by rw [show p+(k+2)*e=2*e+(p+k*e) by ring]; simp only [rpow_add ht]; ring
  have hlT : 2*(L*log (2*T)) ≤ T^(2*e) := calc
    _ ≤ 4*L*log T := by rw [log_mul (by norm_num) ht.ne']; nlinarith only [mul_le_mul_of_nonneg_left (log_le_log (by norm_num : (0:ℝ)<2) hT) hL.le]
    _ ≤ T^e*T^e := mul_le_mul h4 (by simpa using hlog) (log_nonneg ht1) hx
    _ = _ := by rw [← rpow_add ht]; congr 1; ring
  rw [← hcard] at hrestore
  apply hrestore.trans
  calc
    _ ≤ T^(2*e)*((D+C)*T^(p+(k+2)*e)) := mul_le_mul hlT hsum (by positivity) (by positivity)
    _ = (D+C)*T^(2*e+(p+(k+2)*e)) := by simp only [rpow_add ht]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le ht1 (by linarith only [heε])) (by positivity)

theorem low_density {s a p k ε : ℝ} (hs : 1/2 < s) (hs' : s ≤ 1) (ha : 2/3 < a) (ha' : a < 4/3)
    (hp : 2-2*s ≤ p) (hk : 5 ≤ k) (hW : ∀ e, 0 < e → e ≤ 1/100 → WindowCount s a p k e) (hε : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → (zetaDensityCount s T:ℝ) ≤ C*T^(p+ε) := by
  let e := min (1/100:ℝ) (ε/(k+4))
  have he : 0<e := lt_min (by norm_num) (div_pos hε (by linarith))
  have he₀ : e ≤ 1/100 := min_le_left ..
  have heε := (le_div_iff₀ (by linarith : 0<k+4)).mp (min_le_right (1/100:ℝ) (ε/(k+4)))
  apply window_density hs (by linarith) (by norm_num : (0:ℝ)<1/2) (by linarith) ha' he (by linarith) (hW e he he₀) _ hε (by linarith only [heε])
  obtain ⟨D,hD,hmass⟩ := short_typeII_count_by_moment hs
  obtain ⟨F,hF,hm⟩ := weak_short_moment he
  refine ⟨D*F,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),hmass,hm] with T ht1 hmass hm
  intro W z hsep hloc hz hlarge
  have ht : 0<T := by linarith
  let X := T^e
  have hx : 0≤X := (rpow_pos_of_pos ht _).le
  have hxT : X≤T := (rpow_le_rpow_of_exponent_le ht1 (by linarith : e≤1)).trans_eq (rpow_one _)
  apply (hmass X hx (by linarith) W z hsep hloc hz hlarge).trans
  calc
    _ ≤ D*T^(1-2*s)*(F*X^4*T^(1+e)) := by gcongr; apply hm X hx
    _ = D*F*T^(2-2*s+5*e) := by
      dsimp [X]; rw [← rpow_mul_natCast ht.le]; simp only [Nat.cast_ofNat]
      rw [show 2-2*s+5*e=(1-2*s)+(e*4)+(1+e) by ring]; simp only [rpow_add ht]; ring
    _ ≤ _ := by gcongr <;> nlinarith only [hp,mul_le_mul_of_nonneg_right hk he.le]

end DensityStrip
