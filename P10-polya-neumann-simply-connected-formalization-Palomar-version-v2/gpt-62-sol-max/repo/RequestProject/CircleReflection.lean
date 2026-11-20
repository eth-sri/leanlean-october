module

public import RequestProject.RiemannMappingInterior
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Metric Complex Filter MeasureTheory
open scoped Interval ComplexConjugate Topology

/-- A continuous function holomorphic above and below the real axis is
holomorphic on the whole disk, by splitting the rectangles in Morera's theorem. -/
private theorem differentiableOn_of_off_real {f : ℂ → ℂ} {r : ℝ}
    (hc : ContinuousOn f (ball 0 r))
    (hd : ∀ z ∈ ball 0 r, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f (ball 0 r) := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_ball).mp ⟨?_, hc⟩
  intro z w hsub
  rw [← add_eq_zero_iff_eq_neg]
  wlog hwz : z.im ≤ w.im generalizing z w
  grind [add_comm, Rectangle, uIcc_comm]
  have hzero (a b : ℂ) (hab : a.im ≤ b.im) (h : Rectangle a b ⊆ ball 0 r)
      (hside : 0 ≤ a.im ∨ b.im ≤ 0) : wedgeIntegral a b f + wedgeIntegral b a f = 0 := by
    rw [wedgeIntegral_add_wedgeIntegral_eq]
    apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f a b (hc.mono h)
    intro q hq
    rw [mem_reProdIm, min_eq_left hab, max_eq_right hab] at hq
    exact (hd q (h (by
      rw [Rectangle, mem_reProdIm, uIcc_of_le hab]
      exact ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩)) (by grind)).differentiableWithinAt
  by_cases hside : 0 ≤ z.im ∨ w.im ≤ 0
  simp_all
  have hz : z.im ≤ 0 := by grind
  have hw : 0 ≤ w.im := by grind
  let a : ℂ := ⟨z.re, 0⟩
  let b : ℂ := ⟨w.re, 0⟩
  have hl : Rectangle z b ⊆ ball 0 r := hsub.trans' (fun q hq => by
    simp only [Rectangle, b, mem_reProdIm, uIcc_of_le hz, uIcc_of_le hwz] at hq ⊢
    grind)
  have hu : Rectangle a w ⊆ ball 0 r := hsub.trans' (fun q hq => by
    simp  [Rectangle, a, mem_reProdIm, uIcc_of_le hw, uIcc_of_le hwz] at hq ⊢
    grind)
  have h₁ := hzero z b hz hl (Or.inr le_rfl)
  have h₂ := hzero a w hw hu (Or.inl le_rfl)
  have hjoin (x : ℝ) (hx : x ∈ [[z.re, w.re]]) :
      (∫ y in z.im..w.im, f (x + y * I)) =
        (∫ y in z.im..0, f (x + y * I)) + ∫ y in 0..w.im, f (x + y * I) := by
    have hv : ContinuousOn (fun y : ℝ => f (x + y * I)) [[z.im, w.im]] :=
      hc.comp (by fun_prop) (fun y hy => hsub (by simp [Rectangle, mem_reProdIm, hx, hy]))
    have hI₁ : [[z.im, 0]] ⊆ [[z.im, w.im]] := by
      simp  [uIcc_of_le hz, uIcc_of_le hwz]; gcongr
    have hI₂ : [[0, w.im]] ⊆ [[z.im, w.im]] := by
      simp  [uIcc_of_le hw, uIcc_of_le hwz]; gcongr
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hv.mono hI₁).intervalIntegrable (hv.mono hI₂).intervalIntegrable).symm
  calc
    _ = (wedgeIntegral z b f + wedgeIntegral b z f) +
        (wedgeIntegral a w f + wedgeIntegral w a f) := by
      simp only [wedgeIntegral_add_wedgeIntegral_eq, b]
      rw [hjoin z.re left_mem_uIcc, hjoin w.re right_mem_uIcc, smul_add, smul_add]
      abel
    _ = 0 := by simp_all

private theorem exists_continuous_primitive {S : Set ℂ} (ho : IsOpen S) (hb : Bornology.IsBounded S)
    (hv : Convex ℝ S) (hne : S.Nonempty) {u : ℂ → ℂ} (hd : DifferentiableOn ℂ u S)
    {K : NNReal} (hK : ∀ z ∈ S, ‖u z‖₊ ≤ K) :
    ∃ A : ℂ → ℂ, Continuous A ∧ ∀ z ∈ S, HasDerivAt A (u z) z := by
  letI := hv.contractibleSpace hne
  obtain ⟨F, hF, hi, him⟩ := exists_interior_conformal_map S ho hb (SimplyConnectedSpace.ofContractible S)
  obtain ⟨G, hG, hm, _, hright⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball hF hi
  rw [him] at hG hm hright
  have hmF := him ▸ mapsTo_image F _
  obtain ⟨B, hB⟩ := ((hd.comp hF hmF).mul (hF.deriv isOpen_ball)).isExactOn_ball
  have hBA (z) (hz : z ∈ S) : HasDerivAt (B ∘ G) (u z) z := by
    have hfg := (hF.differentiableAt (isOpen_ball.mem_nhds (hm hz))).hasDerivAt.comp z
      (hG.differentiableAt (ho.mem_nhds hz)).hasDerivAt
    have heq := eventually_of_mem (ho.mem_nhds hz) fun _ hw => hright _ hw
    have hprod := hfg.unique ((hasDerivAt_id z).congr_of_eventuallyEq heq)
    have h := (hB (G z) (hm hz)).comp z (hG.differentiableAt (ho.mem_nhds hz)).hasDerivAt
    simpa only [Pi.mul_apply, Function.comp_apply, hright z hz, mul_assoc, hprod, mul_one] using h
  have hl := hv.lipschitzOnWith_of_nnnorm_deriv_le (fun z hz => (hBA z hz).differentiableAt)
    (fun z hz => (hBA z hz).deriv.symm ▸ hK z hz)
  obtain ⟨A, hA, he⟩ := hl.extend_finite_dimension
  exact ⟨A, hA.continuous, fun z hz =>
    (hBA z hz).congr_of_eventuallyEq (he.symm.eventuallyEq_of_mem (ho.mem_nhds hz))⟩

private lemma conj_inv_difference_le {a : ℂ} (ha : 1 / 2 ≤ ‖a‖) (hb : ‖a‖ < 1) :
    ‖a - conj (a⁻¹)‖ ≤ 4 * (1 - ‖a‖) := by
  have hpos : 0 < ‖a‖ := by linarith
  have he : ‖a - conj (a⁻¹)‖ * ‖a‖ = 1 - ‖a‖ ^ 2 := by
    calc
      _ = ‖(a - conj (a⁻¹)) * conj a‖ := by simp 
      _ = _ := by
        rw [sub_mul, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).mpr (norm_pos_iff.mp hpos)),
          mul_conj, normSq_eq_norm_sq, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (by nlinarith))]
        ring
  apply le_of_mul_le_mul_right _ hpos
  nlinarith

private theorem primitives_agree_on_diameter {u P Q : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    {n : ℂ → ℝ} (hn : ContinuousOn n (ball 0 r))
    (hre : ∀ z ∈ ball 0 r, z.im = 0 → n z = 1)
    (hup : ∀ z ∈ ball 0 r, 0 < z.im → n z = ‖u z‖)
    (hlo : ∀ z ∈ ball 0 r, 0 < z.im → 1 / 2 ≤ ‖u z‖)
    (hhi : ∀ z ∈ ball 0 r, 0 < z.im → ‖u z‖ < 1)
    (hP : Continuous P) (hQ : Continuous Q)
    (hPd : ∀ z ∈ ball 0 r, 0 < z.im → HasDerivAt P (u z) z)
    (hQd : ∀ z ∈ ball 0 r, 0 < z.im → HasDerivAt Q ((u z)⁻¹) z)
    {z : ℂ} (hz : z ∈ ball 0 r) (hz₀ : z.im = 0) :
    P z - P 0 = conj (Q z - Q 0) := by
  have hreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz₀]
  let T (t x : ℝ) := (x : ℂ) + t * I
  let A (t x : ℝ) := P (T t x) - conj (Q (T t x))
  have hK : MapsTo (fun x : ℝ => (x : ℂ)) [[0, z.re]] (ball 0 r) := by
    have hz' : |z.re| < r := by
      rw [← Real.norm_eq_abs, ← norm_real, ← congrArg norm hreal]
      exact mem_ball_zero_iff.mp hz
    intro x hx
    rw [mem_ball_zero_iff, norm_real]
    rcases mem_uIcc.mp hx with h | h <;> exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hz').1], by linarith [(abs_lt.mp hz').2]⟩
  have hbound (ε : ℝ) (he : 0 < ε) : ‖A 0 z.re - A 0 0‖ ≤ ε * |z.re| := by
    have ho := hn.isOpen_inter_preimage isOpen_ball (isOpen_Ioi (a := 1 - ε / 4))
    obtain ⟨δ, hδ, hs⟩ := (isCompact_uIcc.image continuous_ofReal).exists_thickening_subset_open ho
      (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hK hx, by rw [mem_preimage, mem_Ioi, hre _ (hK hx) (by simp)]; linarith⟩)
    have hshift (t : ℝ) (ht : t ∈ Ioo 0 δ) (x : ℝ) (hx : x ∈ [[0, z.re]]) :
        T t x ∈ ball 0 r ∧ 1 - ε / 4 < n (T t x) := by
      apply hs
      exact mem_thickening_iff.mpr ⟨(x : ℂ), mem_image_of_mem _ hx, by
        simpa [T, dist_eq_norm, abs_of_pos ht.1] using ht.2⟩
    have hder (t : ℝ) (ht : t ∈ Ioo 0 δ) (x : ℝ) (hx : x ∈ [[0, z.re]]) :
        HasDerivAt (A t) (u (T t x) - conj ((u (T t x))⁻¹)) x := by
      have hi : 0 < (T t x).im := by simpa [T] using ht.1
      have hb := (hshift t ht x hx).1
      have hlin := (hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * I)
      have hp := ((hPd _ hb hi).comp (x : ℂ) hlin).comp_ofReal
      have hq := ((hQd _ hb hi).comp (x : ℂ) hlin).comp_ofReal
      simpa only [A, T, Function.comp_apply, id_eq, Pi.sub_def, mul_one, Complex.star_def] using hp.sub hq.star
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖A t z.re - A t 0‖ ≤ ε * |z.re| := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      simpa [Real.norm_eq_abs] using
        (convex_uIcc (0 : ℝ) z.re).norm_image_sub_le_of_norm_deriv_le
          (fun x hx => (hder t ht x hx).differentiableAt) (C := ε)
          (fun x hx => by
            rw [(hder t ht x hx).deriv]
            have hb := hshift t ht x hx
            have hi : 0 < (T t x).im := by simpa [T] using ht.1
            exact (conj_inv_difference_le (hlo _ hb.1 hi) (hhi _ hb.1 hi)).trans (by grind)) left_mem_uIcc right_mem_uIcc
    have hcont : Continuous (fun t : ℝ => ‖A t z.re - A t 0‖) := by fun_prop
    exact le_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
  have heq : A 0 z.re = A 0 0 := by
    by_contra hne
    have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h := hbound (‖A 0 z.re - A 0 0‖ / (2 * (|z.re| + 1))) (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
    nlinarith [mul_nonneg hp.le (abs_nonneg z.re)]
  simp  [A, T, ofReal_zero, zero_mul, add_zero] at heq
  rw [← hreal] at heq
  rw [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp heq

/-- Reflection into the unit circle needs only continuity of the modulus.
The primitives of the two reflected holomorphic functions have equal traces:
the jump of their horizontal derivatives tends to zero. -/
theorem exists_circle_reflection_of_continuous_norm {u : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    {n : ℂ → ℝ} (hn : ContinuousOn n (ball 0 r))
    (hre : ∀ z ∈ ball 0 r, z.im = 0 → n z = 1)
    (hup : ∀ z ∈ ball 0 r, 0 < z.im → n z = ‖u z‖)
    (hlo : ∀ z ∈ ball 0 r, 0 < z.im → 1 / 2 ≤ ‖u z‖)
    (hhi : ∀ z ∈ ball 0 r, 0 < z.im → ‖u z‖ < 1)
    (hd : DifferentiableOn ℂ u (ball 0 r ∩ {z | 0 < z.im}))
    (hi : InjOn u (ball 0 r ∩ {z | 0 < z.im})) :
    ∃ v : ℂ → ℂ, DifferentiableOn ℂ v (ball 0 r) ∧ InjOn v (ball 0 r) ∧
      EqOn v u (ball 0 r ∩ {z | 0 < z.im}) ∧ ‖v 0‖ = 1 ∧
      ∀ z ∈ ball 0 r, ‖v z‖ < 1 ↔ 0 < z.im := by
  let S := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hs : IsOpen S := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hb : Bornology.IsBounded S := isBounded_ball.subset inter_subset_left
  have hv : Convex ℝ S := (convex_ball _ _).inter (convex_halfSpace_gt imCLM.isLinear 0)
  have hmid : (r / 2 : ℝ) * I ∈ S := by
    refine ⟨mem_ball_zero_iff.mpr ?_, by simp_all⟩
    simpa [abs_of_pos hr, abs_of_pos (half_pos hr)] using half_lt_self hr
  have hne : S.Nonempty := ⟨_, hmid⟩
  have hnonzero (z) (hz : z ∈ S) : u z ≠ 0 := norm_pos_iff.mp (by grind)
  obtain ⟨P, hP, hPd⟩ := exists_continuous_primitive hs hb hv hne hd (K := 1)
    (fun z hz => by exact_mod_cast (hhi z hz.1 hz.2).le)
  obtain ⟨Q, hQ, hQd⟩ := exists_continuous_primitive hs hb hv hne
    (hd.inv hnonzero) (K := 2) (fun z hz => by
      change ‖(u z)⁻¹‖ ≤ (2 : ℝ)
      rw [norm_inv, inv_le_comm₀ (norm_pos_iff.mpr (hnonzero _ hz)) (by norm_num)]
      grind)
  let A (z : ℂ) := if 0 ≤ z.im then P z - P 0 else conj (Q (conj z) - Q 0)
  have hAc : ContinuousOn A (ball 0 r) := by
    apply ContinuousOn.if
    · intro z hz
      have hz₀ : z.im = 0 := by simpa [frontier_setOfPred_le_im] using hz.2
      have hconj : conj z = z := by apply Complex.ext <;> simp [hz₀]
      rw [hconj]
      exact primitives_agree_on_diameter hr hn hre hup hlo hhi hP hQ
        (fun z hz hi => hPd z ⟨hz, hi⟩) (fun z hz hi => hQd z ⟨hz, hi⟩) hz.1 hz₀
    fun_prop
    · exact (continuous_conj.comp ((hQ.comp continuous_conj).sub continuous_const)).continuousOn
  have hdu {z : ℂ} (hz : z ∈ ball 0 r) (hp : 0 < z.im) : HasDerivAt A (u z) z := by
    apply (hPd z ⟨hz, hp⟩).sub_const _ |>.congr_of_eventuallyEq
    filter_upwards [continuous_im.continuousAt.eventually (lt_mem_nhds hp)] with w hw
    exact if_pos hw.le
  have hdm {z : ℂ} (hz : z ∈ ball 0 r) (hp : z.im < 0) :
      HasDerivAt A (conj ((u (conj z))⁻¹)) z := by
    have h : HasDerivAt (fun w => conj (Q (conj w) - Q 0)) (conj ((u (conj z))⁻¹)) z := by
      simpa only [conj_conj, Function.comp_def, Pi.inv_apply] using
        ((hQd (conj z) ⟨by simpa using hz, by simpa using hp⟩).sub_const (Q 0)).conj_conj
    apply h.congr_of_eventuallyEq
    filter_upwards [continuous_im.continuousAt.eventually (gt_mem_nhds hp)] with w hw
    simp [A, hw.not_ge]
  have had := differentiableOn_of_off_real hAc (fun z hz he => (lt_or_gt_of_ne he).elim
    (fun h => (hdm hz h).differentiableAt) (fun h => (hdu hz h).differentiableAt))
  let v := deriv A
  have hvc : ContinuousOn v (ball 0 r) := (had.deriv isOpen_ball).continuousOn
  have hve : EqOn v u S := fun z hz => (hdu hz.1 hz.2).deriv
  have hnorm (z : ℂ) (hz : z ∈ ball 0 r) (hz₀ : z.im = 0) : ‖v z‖ = 1 := by
    let b (t : ℝ) := z + (t : ℂ) * I
    have ht : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      have h : Continuous b := by fun_prop
      simpa [b] using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), b t ∈ S := by
      filter_upwards [ht.eventually (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with t ht₁ ht₂
      exact ⟨ht₁, by simpa [b, hz₀, Complex.add_im, Complex.mul_im] using ht₂⟩
    have htb := tendsto_nhdsWithin_iff.mpr ⟨ht, he.mono fun _ h => h.1⟩
    exact tendsto_nhds_unique ((hvc.norm z hz).tendsto.comp htb)
      (((hn z hz).tendsto.comp htb).congr' (he.mono fun t h => by grind) |>.trans (hre z hz hz₀ ▸ le_rfl))
  have hneg (z : ℂ) (hz : z ∈ ball 0 r) (h : z.im < 0) : 1 < ‖v z‖ := by
    change 1 < ‖deriv A z‖
    rw [(hdm hz h).deriv (f := A), norm_conj, norm_inv, one_lt_inv₀ (norm_pos_iff.mpr
      (hnonzero _ ⟨by simpa using hz, by simpa using h⟩))]
    exact hhi _ (by simpa using hz) (by simpa using h)
  have hchar (z : ℂ) (hz : z ∈ ball 0 r) : ‖v z‖ < 1 ↔ 0 < z.im := by
    refine ⟨fun h => ?_, fun h => hve ⟨hz, h⟩ ▸ hhi z hz h⟩
    rcases lt_trichotomy z.im 0 with hl | he | hg
    · linarith [hneg z hz hl]
    · linarith [hnorm z hz he]
    · exact hg
  have hvd : DifferentiableOn ℂ v (ball 0 r) := had.deriv isOpen_ball
  have hzero := hnorm 0 (mem_ball_self hr) (by simp)
  refine ⟨v, hvd, ?_, hve, hzero, hchar⟩
  have ho := ((hvd.analyticOnNhd isOpen_ball).is_constant_or_isOpen (convex_ball _ _).isPreconnected).resolve_left
    (by rintro ⟨c, hc⟩; have he := (hc 0 (mem_ball_self hr)).trans (hc _ hmid.1).symm
        grind)
  intro a ha b hb hab
  by_cases hpa : 0 < a.im
  · have hpb := (hchar b hb).mp (hab ▸ (hchar a ha).mpr hpa)
    exact hi ⟨ha, hpa⟩ ⟨hb, hpb⟩ ((hve ⟨ha, hpa⟩).symm.trans (hab.trans (hve ⟨hb, hpb⟩)))
  by_cases hma : a.im < 0
  · have hmb : b.im < 0 := by
      rcases lt_trichotomy b.im 0 with h | h | h
      · exact h
      grind
      grind
    have h := (hdm ha hma).deriv.symm.trans (hab.trans (hdm hb hmb).deriv)
    apply (starRingEnd ℂ).injective
    exact hi (x₁ := conj a) (x₂ := conj b) ⟨by simpa using ha, by simpa using hma⟩
      ⟨by simpa using hb, by simpa using hmb⟩ ((starRingEnd ℂ).injective (by simpa using h))
  have haz : a.im = 0 := by linarith
  by_contra hneq
  let s := dist a b / 2
  have hs₀ : 0 < s := half_pos (dist_pos.mpr hneq)
  have hdisj : Disjoint (ball a s) (ball b s) := ball_disjoint_ball (by dsimp [s]; linarith)
  let U := ball (0 : ℂ) r ∩ ball a s
  let V := ball (0 : ℂ) r ∩ ball b s
  have hU := ho U inter_subset_left (isOpen_ball.inter isOpen_ball)
  have hV := ho V inter_subset_left (isOpen_ball.inter isOpen_ball)
  have hm : v a ∈ v '' U ∩ v '' V :=
    ⟨mem_image_of_mem _ ⟨ha, mem_ball_self hs₀⟩, ⟨b, ⟨hb, mem_ball_self hs₀⟩, hab.symm⟩⟩
  have hcl : v a ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero, mem_closedBall_zero_iff, hnorm a ha haz]
  obtain ⟨q, hq, hh⟩ := mem_closure_iff_nhds.mp hcl _ ((hU.inter hV).mem_nhds hm)
  obtain ⟨x, hx, hxe⟩ := hq.1
  obtain ⟨y, hy, hye⟩ := hq.2
  have hx' : x ∈ S := ⟨hx.1, (hchar _ hx.1).mp (mem_ball_zero_iff.mp (hxe.symm ▸ hh))⟩
  have hy' : y ∈ S := ⟨hy.1, (hchar _ hy.1).mp (mem_ball_zero_iff.mp (hye.symm ▸ hh))⟩
  have hxy := hi hx' hy' ((hve hx').symm.trans (hxe.trans (hye.symm.trans (hve hy'))))
  exact Set.disjoint_left.mp hdisj hx.2 (hxy ▸ hy.2)

end PolyaNeumann

end
