module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNormalized
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxis
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFields
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarHessianScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarEquations
public import Mathlib.Analysis.Calculus.MeanValue
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarProfile
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNativeEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarClassical
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeak
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter Asymptotics Set MeasureTheory
open scoped Topology ContDiff



/-- A differentiated power remainder gives a finite normalized first-derivative limit. -/
theorem scalar_deriv_tail_ratio (f : ℝ → ℝ) (alpha c : ℝ) (hf : ContDiff ℝ 2 f)
    (hr : IsBigO atTop (deriv (fun s => f s - c * Real.rpow s alpha))
      (fun s => Real.rpow s (alpha - 4))) :
    Tendsto (fun s => deriv f s / Real.rpow s (alpha - 1)) atTop (𝓝 (c * alpha)) := by
  have hzero : Tendsto (fun s =>
      deriv (fun t => f t - c * Real.rpow t alpha) s / Real.rpow s (alpha - 1))
      atTop (𝓝 0) := by
    apply scalar_tail_ratio _ (alpha - 1) 0
    simpa [show alpha - 1 - 3 = alpha - 4 by ring] using hr
  have ht := hzero.add_const (c * alpha)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [scalar_power_remainder_deriv f alpha c s hs (hf.differentiable (by norm_num) s)]
  have hp : Real.rpow s (alpha - 1) ≠ 0 := by
    simpa using (Real.rpow_pos_of_pos hs (alpha - 1)).ne'
  field_simp
  ring

/-- A twice differentiated remainder gives a finite normalized second-derivative limit. -/
theorem scalar_deriv2_tail_ratio (f : ℝ → ℝ) (alpha c : ℝ) (hf : ContDiff ℝ 2 f)
    (hr : IsBigO atTop (deriv (deriv (fun s => f s - c * Real.rpow s alpha)))
      (fun s => Real.rpow s (alpha - 5))) :
    Tendsto (fun s => deriv (deriv f) s / Real.rpow s (alpha - 2))
      atTop (𝓝 (c * alpha * (alpha - 1)))  := by
  have scalar_power_remainder_deriv2 (s : ℝ) (hs : 0 < s) :
      deriv (deriv (fun t => f t - c * Real.rpow t alpha)) s =
      deriv (deriv f) s - c * alpha * (alpha - 1) * Real.rpow s (alpha - 2) := by
    have he : deriv (fun t => f t - c * Real.rpow t alpha) =ᶠ[𝓝 s]
        fun t => deriv f t - c * alpha * Real.rpow t (alpha - 1) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact scalar_power_remainder_deriv f alpha c t ht (hf.differentiable (by norm_num) t)
    rw [he.deriv_eq]
    have hp := (Real.hasDerivAt_rpow_const (p := alpha - 1) (Or.inl hs.ne')).const_mul
      (c * alpha)
    simpa only [Real.rpow_eq_pow, Pi.sub_def, Pi.mul_def,
      show alpha - 1 - 1 = alpha - 2 by ring, mul_assoc] using ((hf.differentiable_deriv_two s).hasDerivAt.sub hp).deriv
  have hzero : Tendsto (fun s =>
      deriv (deriv (fun t => f t - c * Real.rpow t alpha)) s /
        Real.rpow s (alpha - 2)) atTop (𝓝 0) := by
    apply scalar_tail_ratio _ (alpha - 2) 0
    simpa [show alpha - 2 - 3 = alpha - 5 by ring] using hr
  have ht := hzero.add_const (c * alpha * (alpha - 1))
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [scalar_power_remainder_deriv2 s hs]
  have hp : Real.rpow s (alpha - 2) ≠ 0 := by
    simpa using (Real.rpow_pos_of_pos hs (alpha - 2)).ne'
  field_simp
  ring



/-- A finite power-normalized limit gives the corresponding actual Big-O estimate. -/
theorem scalar_isBigO_of_power_ratio (f : ℝ → ℝ) (beta c : ℝ)
    (ht : Tendsto (fun s => f s / Real.rpow s beta) atTop (𝓝 c)) :
    IsBigO atTop f (fun s => Real.rpow s beta) := by
  refine isBigO_of_div_tendsto_nhds ?_ c ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hp : Real.rpow s beta ≠ 0 := by
      simpa using (Real.rpow_pos_of_pos hs beta).ne'
    exact fun hz => False.elim (hp hz)
  · simpa only [Pi.div_def] using ht





/-- Exact power cancellation for every real jet degree, including negative degrees. -/
theorem scalar_similarity_power_cancel_general (beta x v : ℝ) (hx : 0 < x) :
    Real.rpow x (beta / 3) * Real.rpow |scalarSimilarity x v| beta = Real.rpow |v| beta := by
  simp only [scalarSimilarity, Real.rpow_eq_pow, abs_div, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos hx (1 / 3 : ℝ))]
  rw [Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hx.le _),
    ← Real.rpow_mul hx.le, show (1 / 3 : ℝ) * beta = beta / 3 by ring]
  field_simp

/-- The signed similarity coordinate tends to the appropriate infinite ray in a joint axis limit. -/
theorem scalarSimilarity_tendsto_axis {ι : Type*} (l : Filter ι) (X V : ι → ℝ)
    (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    Tendsto (fun i => scalarSimilarity (X i) (V i)) l
      (if v < 0 then atTop else atBot) := by
  have hK : Tendsto (fun i => Real.rpow (X i) (1 / 3)) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 3 : ℝ))).tendsto 0
      simpa only [Real.rpow_eq_pow, Function.comp_def,
        Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using h.comp hX
    · filter_upwards [hXp] with i hi
      exact Real.rpow_pos_of_pos hi _
  have hInv := hK.inv_tendsto_nhdsGT_zero
  rcases lt_or_gt_of_ne hv with hv | hv
  · rw [ite_eq_left hv]
    simpa only [scalarSimilarity, div_eq_mul_inv, Pi.inv_apply] using
      hV.neg.pos_mul_atTop (neg_pos.mpr hv) hInv
  · rw [ite_eq_right (not_lt.mpr hv.le)]
    simpa only [scalarSimilarity, div_eq_mul_inv, Pi.inv_apply] using
      hV.neg.neg_mul_atTop (neg_neg_of_pos hv) hInv

/-- Two actual similarity-tail bounds give local boundedness after kinetic rescaling at an axis. -/
theorem scalar_scaled_tail_bounded {ι : Type*} (l : Filter ι) (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (X V : ι → ℝ) (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    IsBigO l (fun i => Real.rpow (X i) (beta / 3) * f (scalarSimilarity (X i) (V i)))
      (fun _ => (1 : ℝ)) := by
  have hS := scalarSimilarity_tendsto_axis l X V v hv hX hXp hV
  have hf : IsBigO l (fun i => f (scalarSimilarity (X i) (V i)))
      (fun i => Real.rpow |scalarSimilarity (X i) (V i)| beta) := by
    by_cases hvn : v < 0
    · rw [ite_eq_left hvn] at hS
      exact ht.comp_tendsto hS
    · rw [ite_eq_right hvn] at hS
      exact hb.comp_tendsto hS
  have he : (fun i => Real.rpow (X i) (beta / 3) *
      Real.rpow |scalarSimilarity (X i) (V i)| beta) =ᶠ[l] fun i => Real.rpow |V i| beta := by
    filter_upwards [hXp] with i hi
    exact scalar_similarity_power_cancel_general beta (X i) (V i) hi
  have hP : Tendsto (fun i => Real.rpow |V i| beta) l (𝓝 (Real.rpow |v| beta)) := by
    simpa only [Real.rpow_eq_pow, Function.comp_def] using
      (Real.continuousAt_rpow_const |v| beta (Or.inl (abs_ne_zero.mpr hv))).tendsto.comp hV.abs
  exact (((isBigO_refl (fun i => Real.rpow (X i) (beta / 3)) l).mul hf).congr' EventuallyEq.rfl he).trans (isBigO_const_of_tendsto hP one_ne_zero)









/-- The reflected scalar rescaling, with zero values on the position axis. -/
def scalarRescaled (f : ℝ → ℝ) (beta : ℝ) (q : XV 1) : ℝ :=
  if 0 < q.1 0 then Real.rpow (q.1 0) (beta / 3) * f (scalarSimilarity (q.1 0) (q.2 0))
  else if q.1 0 < 0 then Real.rpow (-q.1 0) (beta / 3) *
    f (scalarSimilarity (-q.1 0) (-q.2 0)) else 0







/-- The source's cancelled position similarity factor. -/
def scalarPositionFactor (gamma : ScalarGamma) (Lam s : ℝ) : ℝ :=
  gamma.1 * F gamma Lam s - s / 3 * deriv (F gamma Lam) s





/-- Native supremum norm in dimension one is exactly the sole scalar absolute value. -/
theorem scalar_vec_norm (v : PDE.Vec 1) : ‖v‖ = |v 0| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (v 0))).mpr
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact le_rfl
  · simpa using norm_le_pi_norm v 0

/-- Both actual derivative rays can be used in the absolute-value rescaling bound. -/
theorem scalar_positive_power_to_abs (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow s beta)) :
    IsBigO atTop f (fun s => Real.rpow |s| beta) := by
  apply ht.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [abs_of_pos hs]

/-- All scalar representative jets are uniformly bounded on compact sets away from zero. -/
theorem scalarJets_compact_bound (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (K : Set (XV 1)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K, ‖scalarGx gamma Lam q‖ ≤ M ∧ ‖scalarGv gamma Lam q‖ ≤ M ∧
      ∀ i k, |scalarHess gamma Lam q i k| ≤ M        := by
  have scalarRescaled_compact_bound (f : ℝ → ℝ) (beta : ℝ) (hf : Continuous f) (ht : IsBigO atTop f (fun s => Real.rpow |s| beta)) (hb : IsBigO atBot f (fun s => Real.rpow |s| beta)) :
      ∃ M : ℝ, ∀ q ∈ K, |scalarRescaled f beta q| ≤ M := by
    have scalarRescaled_locally_bounded (q : XV 1) (hq : q ≠ 0) :
        ∃ M : ℝ, ∀ᶠ z in 𝓝 q, |scalarRescaled f beta z| ≤ M := by
      have scalarRescaled_isBigO_axis (hx : q.1 0 = 0) (hv : q.2 0 ≠ 0) :
          IsBigO (𝓝 q) (scalarRescaled f beta) (fun _ => (1 : ℝ)) := by
        have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
        have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
        let Sp : Set (XV 1) := {z | 0 < z.1 0}
        let Sn : Set (XV 1) := {z | z.1 0 < 0}
        let Sz : Set (XV 1) := {z | z.1 0 = 0}
        have hUnion : Sp ∪ Sn ∪ Sz = univ := by
          ext z
          simp only [Sp, Sn, Sz, mem_union, mem_ofPred_eq, mem_univ, iff_true]
          rcases lt_trichotomy (z.1 0) 0 with h | h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
          · exact Or.inl (Or.inl h)
        rw [← nhdsWithin_univ q, ← hUnion, nhdsWithin_union, nhdsWithin_union, isBigO_sup,
          isBigO_sup]
        constructor
        · constructor
          · have hh := scalar_scaled_tail_bounded (𝓝[Sp] q) f beta ht hb
              (fun z => z.1 0) (fun z => z.2 0) (q.2 0) hv
              (by simpa only [hx] using
                ((hX.tendsto q).mono_left (nhdsWithin_le_nhds (s := Sp))))
              self_mem_nhdsWithin ((hV.tendsto q).mono_left nhdsWithin_le_nhds)
            apply hh.congr' _ EventuallyEq.rfl
            filter_upwards [self_mem_nhdsWithin] with z hz
            simp [scalarRescaled, show 0 < z.1 0 from hz]
          · have hh := scalar_scaled_tail_bounded (𝓝[Sn] q) f beta ht hb
              (fun z => -z.1 0) (fun z => -z.2 0) (-q.2 0) (neg_ne_zero.mpr hv)
              (by simpa [hx] using
                ((hX.tendsto q).neg.mono_left (nhdsWithin_le_nhds (s := Sn))))
              (by filter_upwards [self_mem_nhdsWithin] with z hz; exact neg_pos.mpr hz)
              ((hV.tendsto q).neg.mono_left nhdsWithin_le_nhds)
            apply hh.congr' _ EventuallyEq.rfl
            filter_upwards [self_mem_nhdsWithin] with z hz
            simp [scalarRescaled, not_lt.mpr (show z.1 0 < 0 from hz).le, show z.1 0 < 0 from hz]
        · apply (isBigO_zero (fun _ : XV 1 => 1) (𝓝[Sz] q)).congr' _ EventuallyEq.rfl
          filter_upwards [self_mem_nhdsWithin] with z hz
          simp [scalarRescaled, show z.1 0 = 0 from hz, lt_self_iff_false]
      have scalarRescaled_continuousAt_off_axis (hx : q.1 0 ≠ 0) :
          ContinuousAt (scalarRescaled f beta) q := by
        have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
        have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
        rcases lt_or_gt_of_ne hx with hx | hx
        · have hxp : 0 < -q.1 0 := neg_pos.mpr hx
          have hXn : ContinuousAt (fun z : XV 1 => -z.1 0) q := by fun_prop
          have hP : ContinuousAt (fun z : XV 1 => Real.rpow (-z.1 0) (beta / 3)) q := by
            simpa only [Real.rpow_eq_pow] using
              (Real.continuousAt_rpow_const (-q.1 0) (beta / 3) (Or.inl hxp.ne')).comp'
                (f := fun z : XV 1 => -z.1 0) hXn
          have hK : ContinuousAt (fun z : XV 1 => Real.rpow (-z.1 0) (1 / 3)) q := by
            simpa only [Real.rpow_eq_pow] using
              (Real.continuousAt_rpow_const (-q.1 0) (1 / 3) (Or.inl hxp.ne')).comp'
                (f := fun z : XV 1 => -z.1 0) hXn
          have hk : Real.rpow (-q.1 0) (1 / 3) ≠ 0 := by
            simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hxp (1 / 3 : ℝ)).ne'
          have hS : ContinuousAt (fun z : XV 1 => scalarSimilarity (-z.1 0) (-z.2 0)) q := by
            simpa [scalarSimilarity, Pi.div_def] using (hV.continuousAt (x := q)).div hK hk
          have hh := hP.mul (hf.continuousAt.comp' hS)
          apply hh.congr_of_eventuallyEq
          filter_upwards [hX.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx)] with z hz
          simp [scalarRescaled, scalarSimilarity, not_lt.mpr (show z.1 0 < 0 from hz).le, show z.1 0 < 0 from hz, Pi.mul_def]
        · have hP : ContinuousAt (fun z : XV 1 => Real.rpow (z.1 0) (beta / 3)) q := by
            simpa only [Real.rpow_eq_pow] using
              (Real.continuousAt_rpow_const (q.1 0) (beta / 3) (Or.inl hx.ne')).comp'
                (f := fun z : XV 1 => z.1 0)
                (hX.continuousAt (x := q))
          have hK : ContinuousAt (fun z : XV 1 => Real.rpow (z.1 0) (1 / 3)) q := by
            simpa only [Real.rpow_eq_pow] using
              (Real.continuousAt_rpow_const (q.1 0) (1 / 3) (Or.inl hx.ne')).comp'
                (f := fun z : XV 1 => z.1 0)
                (hX.continuousAt (x := q))
          have hk : Real.rpow (q.1 0) (1 / 3) ≠ 0 := by
            simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hx (1 / 3 : ℝ)).ne'
          have hS : ContinuousAt (fun z : XV 1 => scalarSimilarity (z.1 0) (z.2 0)) q := by
            simpa only [scalarSimilarity, Pi.neg_def, Pi.div_def] using
              (hV.continuousAt (x := q)).neg.div hK hk
          have hh := hP.mul (hf.continuousAt.comp' hS)
          apply hh.congr_of_eventuallyEq
          filter_upwards [hX.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with z hz
          simp [scalarRescaled, scalarSimilarity, show 0 < z.1 0 from hz, Pi.mul_def]
      have hh : IsBigO (𝓝 q) (scalarRescaled f beta) (fun _ => (1 : ℝ)) := by
        by_cases hx : q.1 0 = 0
        · have hv : q.2 0 ≠ 0 := by
            intro hv
            apply hq
            apply Prod.ext <;> funext i
            all_goals have hi : i = 0 := Subsingleton.elim _ _
            all_goals subst i
            · exact hx
            · exact hv
          exact scalarRescaled_isBigO_axis hx hv
        · exact isBigO_const_of_tendsto
            (scalarRescaled_continuousAt_off_axis hx).tendsto one_ne_zero
      obtain ⟨M, hM⟩ := hh.bound
      refine ⟨M, ?_⟩
      simpa [norm_one] using hM
    classical
    have hKnz (q : K) : (q : XV 1) ≠ 0 := by
      intro hq
      exact hz (hq ▸ q.2)
    choose M hM using fun q : K => scalarRescaled_locally_bounded q (hKnz q)
    let U : ∀ q ∈ K, Set (XV 1) := fun q hq => {z | |scalarRescaled f beta z| ≤ M ⟨q, hq⟩}
    obtain ⟨J, hJ⟩ := hK.elim_nhds_subcover' U (fun q hq => hM ⟨q, hq⟩)
    refine ⟨∑ j ∈ J, |M j|, ?_⟩
    intro q hq
    obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.mp (hJ hq)
    have hh := hqp
    exact hh.trans ((le_abs_self (M p)).trans (Finset.single_le_sum
      (fun j _ => abs_nonneg (M j)) hp))
  have F_derivatives_isBigO_atBot :
      IsBigO atBot (deriv (F gamma Lam)) (fun s => Real.rpow |s| (3 * gamma.1 - 1)) ∧
    IsBigO atBot (deriv (deriv (F gamma Lam)))
      (fun s => Real.rpow |s| (3 * gamma.1 - 2)) := by
    have F_negative_remainder_derivatives :
        IsBigO atTop (deriv (fun s => F gamma Lam (-s) -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
        (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
      IsBigO atTop (deriv (deriv (fun s => F gamma Lam (-s) -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
        (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
      have hn := Fminus_negative_ray_tail_derivatives_of_M_jets
        Kummer.M_negative_expansion_jet gamma Lam hLam
      rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hn
      have he (s : ℝ) (hs : 0 < s) : (fun t => Fminus gamma Lam (-t) -
          Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s]
          fun t => F gamma Lam (-t) -
            Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        simp [F, neg_neg_of_pos (show 0 < t from ht), not_lt.mpr (neg_neg_of_pos (show 0 < t from ht)).le]
      constructor
      · apply hn.1.congr' _ EventuallyEq.rfl
        filter_upwards [eventually_gt_atTop 0] with s hs
        exact (he s hs).deriv_eq
      · apply hn.2.congr' _ EventuallyEq.rfl
        filter_upwards [eventually_gt_atTop 0] with s hs
        exact (he s hs).deriv.deriv_eq
    let f : ℝ → ℝ := fun s => F gamma Lam (-s)
    have hj := F_negative_remainder_derivatives
    have hf := (F_contDiff_two gamma Lam hLam).comp contDiff_id.neg
    constructor
    · have hb := ((scalar_isBigO_of_power_ratio _ _ _ (scalar_deriv_tail_ratio f _ _ hf hj.1)).comp_tendsto tendsto_neg_atBot_atTop).neg_left
      apply hb.congr' _ _
      · exact Eventually.of_forall fun s => by
          simp [f, Function.comp_def, deriv_comp_neg]
      · filter_upwards [eventually_lt_atBot 0] with s hs
        simp only [Function.comp_def, abs_of_neg hs]
    · have hb := (scalar_isBigO_of_power_ratio _ _ _ (scalar_deriv2_tail_ratio f _ _ hf hj.2)).comp_tendsto tendsto_neg_atBot_atTop
      apply hb.congr' _ _
      · exact Eventually.of_forall fun s => by
          simp [f, Function.comp_def, scalar_deriv2_comp_neg]
      · filter_upwards [eventually_lt_atBot 0] with s hs
        simp only [Function.comp_def, abs_of_neg hs]
  have F_derivatives_isBigO_atTop :
      IsBigO atTop (deriv (F gamma Lam)) (fun s => Real.rpow s (3 * gamma.1 - 1)) ∧
    IsBigO atTop (deriv (deriv (F gamma Lam))) (fun s => Real.rpow s (3 * gamma.1 - 2)) := by
    have F_positive_remainder_derivatives :
        IsBigO atTop (deriv (fun s => F gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
        (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
      IsBigO atTop (deriv (deriv (fun s => F gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
        (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
      have hp := Fplus_tail_derivatives gamma Lam hLam
      have he (s : ℝ) (hs : 0 < s) : (fun t => Fplus gamma Lam t -
          Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s]
          fun t => F gamma Lam t -
            Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        simp [F, show 0 < t from ht]
      constructor
      · apply hp.1.congr' _ EventuallyEq.rfl
        filter_upwards [eventually_gt_atTop 0] with s hs
        exact (he s hs).deriv_eq
      · apply hp.2.congr' _ EventuallyEq.rfl
        filter_upwards [eventually_gt_atTop 0] with s hs
        exact (he s hs).deriv.deriv_eq
    have hj := F_positive_remainder_derivatives
    have hf := F_contDiff_two gamma Lam hLam
    constructor
    · exact scalar_isBigO_of_power_ratio _ _ _
        (scalar_deriv_tail_ratio _ _ _ hf hj.1)
    · exact scalar_isBigO_of_power_ratio _ _ _
        (scalar_deriv2_tail_ratio _ _ _ hf hj.2)
  have scalarHess_abs_rescaled (q : XV 1) :
      |scalarHess gamma Lam q 0 0| =
      |scalarRescaled (deriv (deriv (F gamma Lam))) (3 * gamma.1 - 2) q| := by
    have scalarAnsatz_deriv2_v_power (x : ℝ) (v : ℝ) (hx : 0 < x) :
        deriv (deriv (scalarAnsatz gamma Lam x)) v = Real.rpow x (gamma.1 - 2 / 3) *
        deriv (deriv (F gamma Lam)) (scalarSimilarity x v) := by
      rw [scalarAnsatz_deriv2_v gamma Lam x v (F_contDiff_two gamma Lam hLam).contDiffAt]
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_sub hx, ← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 2,
        ← Real.rpow_mul hx.le]
      norm_num
    rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
    · simp only [scalarHess, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
      rw [scalarProfile_dvv_negative gamma Lam hLam q hx,
        scalarAnsatz_deriv2_v_power _ _ (neg_pos.mpr hx)]
      simp only [show (3 * gamma.1 - 2) / 3 = gamma.1 - 2 / 3 by ring]
    · simp only [scalarHess, hx, ↓reduceIte, Matrix.zero_apply, scalarRescaled,
        lt_self_iff_false]
    · simp only [scalarHess, hx.ne', ↓reduceIte, scalarRescaled, hx]
      rw [scalarProfile_dvv_positive gamma Lam hLam q hx,
        scalarAnsatz_deriv2_v_power _ _ hx]
      simp only [show (3 * gamma.1 - 2) / 3 = gamma.1 - 2 / 3 by ring]
  have scalarGv_abs_rescaled (q : XV 1) :
      |scalarGv gamma Lam q 0| =
      |scalarRescaled (deriv (F gamma Lam)) (3 * gamma.1 - 1) q| := by
    have scalarProfile_dv_negative (hx : q.1 0 < 0) :
        dv (scalarProfile gamma Lam) q 0 =
        -deriv (scalarAnsatz gamma Lam (-q.1 0)) (-q.2 0) := by
      rw [dv_eq_scalar_slice _ q
        ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne).differentiableAt
          (by norm_num))]
      have he : (fun v => scalarProfile gamma Lam (scalarVelocitySlice q v)) =
          fun v => scalarAnsatz gamma Lam (-q.1 0) (-v) := by
        funext v
        simp only [scalarVelocitySlice, scalarProfile, hx, not_lt.mpr hx.le, ↓reduceIte]
      rw [he]
      exact deriv_comp_neg _ _
    have scalarProfile_dv_positive (hx : 0 < q.1 0) :
        dv (scalarProfile gamma Lam) q 0 = deriv (scalarAnsatz gamma Lam (q.1 0)) (q.2 0) := by
      rw [dv_eq_scalar_slice _ q
        ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne').differentiableAt
          (by norm_num))]
      congr 1
      funext v
      simp only [scalarVelocitySlice, scalarProfile, hx, ↓reduceIte]
    have scalarAnsatz_deriv_v_power (x : ℝ) (v : ℝ) (hx : 0 < x) :
        deriv (scalarAnsatz gamma Lam x) v = -Real.rpow x (gamma.1 - 1 / 3) *
        deriv (F gamma Lam) (scalarSimilarity x v) := by
      rw [(scalarAnsatz_hasDerivAt_v gamma Lam x v
        ((F_contDiff_two gamma Lam hLam).differentiable (by norm_num) _)).deriv]
      simp only [Real.rpow_eq_pow, Real.rpow_sub hx]
    rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
    · simp only [scalarGv, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
      rw [scalarProfile_dv_negative hx,
        scalarAnsatz_deriv_v_power _ _ (neg_pos.mpr hx)]
      simp only [neg_mul, neg_neg, show (3 * gamma.1 - 1) / 3 = gamma.1 - 1 / 3 by ring]
    · simp only [scalarGv, hx, ↓reduceIte, Pi.zero_apply, scalarRescaled, lt_self_iff_false]
    · simp only [scalarGv, hx.ne', ↓reduceIte, scalarRescaled, hx]
      rw [scalarProfile_dv_positive hx,
        scalarAnsatz_deriv_v_power _ _ hx]
      simp only [neg_mul, abs_neg, show (3 * gamma.1 - 1) / 3 = gamma.1 - 1 / 3 by ring]
  have scalarGx_abs_rescaled (q : XV 1) :
      |scalarGx gamma Lam q 0| =
      |scalarRescaled (scalarPositionFactor gamma Lam) (3 * gamma.1 - 3) q| := by
    have scalarAnsatz_deriv_x_cancel (x : ℝ) (v : ℝ) (hx : 0 < x) :
        deriv (fun y => scalarAnsatz gamma Lam y v) x =
        Real.rpow x (gamma.1 - 1) * (gamma.1 * F gamma Lam (scalarSimilarity x v) -
          scalarSimilarity x v / 3 * deriv (F gamma Lam) (scalarSimilarity x v)) := by
      rw [(scalarAnsatz_hasDerivAt_x gamma Lam x v hx
        ((F_contDiff_two gamma Lam hLam).differentiable (by norm_num) _)).deriv]
      have hxp : Real.rpow x (gamma.1 - 1) = Real.rpow x gamma.1 / x := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_sub hx, Real.rpow_one]
      have hxn : Real.rpow x (-(4 / 3)) = (x * Real.rpow x (1 / 3))⁻¹ := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_neg hx.le, show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
          Real.rpow_add hx, Real.rpow_one]
      rw [hxp, hxn]
      unfold scalarSimilarity
      ring
    rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
    · simp only [scalarGx, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
      rw [scalarProfile_dx_negative gamma Lam hLam q hx,
        scalarAnsatz_deriv_x_cancel _ _ (neg_pos.mpr hx), abs_neg]
      simp only [scalarPositionFactor, show (3 * gamma.1 - 3) / 3 = gamma.1 - 1 by ring]
    · simp only [scalarGx, hx, ↓reduceIte, Pi.zero_apply, scalarRescaled, lt_self_iff_false]
    · simp only [scalarGx, hx.ne', ↓reduceIte, scalarRescaled, hx]
      rw [scalarProfile_dx_positive gamma Lam hLam q hx,
        scalarAnsatz_deriv_x_cancel _ _ hx]
      simp only [scalarPositionFactor, show (3 * gamma.1 - 3) / 3 = gamma.1 - 1 by ring]
  have scalarPositionFactor_continuous :
      Continuous (scalarPositionFactor gamma Lam) := by
    have hf := F_contDiff_two gamma Lam hLam
    exact continuous_const.mul hf.continuous |>.sub
      ((continuous_id.div_const 3).mul (hf.continuous_deriv (by norm_num)))
  have hd : ContDiff ℝ 1 (deriv (F gamma Lam)) := (F_contDiff_two gamma Lam hLam).deriv'
  have hp := F_derivatives_isBigO_atTop
  have hn := F_derivatives_isBigO_atBot
  obtain ⟨Mx, hx⟩ := scalarRescaled_compact_bound (scalarPositionFactor gamma Lam)
    (3 * gamma.1 - 3) (scalarPositionFactor_continuous)
    (scalar_positive_power_to_abs _ _ (F_position_cancellation_atTop gamma Lam hLam))
    (F_position_cancellation_atBot gamma Lam hLam hmatch)
  obtain ⟨Mv, hv⟩ := scalarRescaled_compact_bound (deriv (F gamma Lam)) (3 * gamma.1 - 1)
    hd.continuous (scalar_positive_power_to_abs _ _ hp.1) hn.1
  obtain ⟨Mh, hh⟩ := scalarRescaled_compact_bound (deriv (deriv (F gamma Lam)))
    (3 * gamma.1 - 2) hd.continuous_deriv_one
    (scalar_positive_power_to_abs _ _ hp.2) hn.2
  refine ⟨max Mx (max Mv Mh), ?_⟩
  intro q hq
  constructor
  · rw [scalar_vec_norm, scalarGx_abs_rescaled]
    exact (hx q hq).trans (le_max_left _ _)
  constructor
  · rw [scalar_vec_norm, scalarGv_abs_rescaled]
    exact (hv q hq).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i k
    have hi : i = 0 := Subsingleton.elim _ _
    have hk : k = 0 := Subsingleton.elim _ _
    subst i k
    rw [scalarHess_abs_rescaled]
    exact (hh q hq).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Euclidean normalization in dimension one agrees with the scalar absolute value. -/
theorem scalar_vec_euclidean_norm (v : PDE.Vec 1) : PDE.vecEuclideanNorm v = |v 0| := by
  simp only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_one,
    ← sq, Real.sqrt_sq_eq_abs]

/-- The selected velocity representative has the required global kinetic gradient bound. -/
theorem scalarGv_gauge_bound (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV 1, q ≠ 0 → PDE.vecEuclideanNorm (scalarGv gamma Lam q) ≤
      C * Real.rpow (rho q) (3 * gamma.1 - 1) := by
  obtain ⟨C, hC, hbound⟩ := homogeneous_component_bound (fun q => scalarGv gamma Lam q 0)
    (3 * gamma.1 - 1)
    (fun r hr q => congrArg (fun w => w 0) (scalarGv_homogeneous gamma Lam r hLam hr q))
    (by
      intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      exact ⟨M, fun q hq => by simpa only [scalar_vec_norm] using (hM q hq).2.1⟩)
  refine ⟨C, hC, ?_⟩
  intro q hq
  rw [scalar_vec_euclidean_norm]
  exact hbound q hq



/-- Every selected scalar jet is locally integrable with respect to native spatial volume. -/
theorem scalarJets_locallyIntegrable (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    (∀ i, LocallyIntegrable (fun q => scalarGx gamma Lam q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => scalarGv gamma Lam q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => scalarHess gamma Lam q i k) volume) := by
  have hx (i : Fin 1) : LocallyIntegrable (fun q => scalarGx gamma Lam q i) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega)
      (fun q => scalarGx gamma Lam q i)
      ((measurable_pi_apply i).comp (measurable_scalarGx gamma Lam)) (3 * gamma.1 - 3)
      (by linarith only [gamma.2.1]) (by linarith only [gamma.2.2])
    · intro r hr q
      exact congrArg (fun w => w i) (scalarGx_homogeneous gamma Lam r hLam hr q)
    · intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      refine ⟨M, fun q hq => ?_⟩
      have hh : |scalarGx gamma Lam q i| ≤ ‖scalarGx gamma Lam q‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (scalarGx gamma Lam q) i
      exact hh.trans (hM q hq).1
  have hv (i : Fin 1) : LocallyIntegrable (fun q => scalarGv gamma Lam q i) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega)
      (fun q => scalarGv gamma Lam q i)
      ((measurable_pi_apply i).comp (measurable_scalarGv gamma Lam)) (3 * gamma.1 - 1)
      (by linarith only [gamma.2.1]) (by linarith only [gamma.2.2])
    · intro r hr q
      exact congrArg (fun w => w i) (scalarGv_homogeneous gamma Lam r hLam hr q)
    · intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      refine ⟨M, fun q hq => ?_⟩
      have hh : |scalarGv gamma Lam q i| ≤ ‖scalarGv gamma Lam q‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (scalarGv gamma Lam q) i
      exact hh.trans (hM q hq).2.1
  have hh (i k : Fin 1) : LocallyIntegrable (fun q => scalarHess gamma Lam q i k) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega)
      (fun q => scalarHess gamma Lam q i k) (measurable_scalarHess gamma Lam i k)
      (3 * gamma.1 - 2) (by linarith only [gamma.2.1]) (by linarith only [gamma.2.2])
    · intro r hr q
      exact congrArg (fun w => w i k) (scalarHess_homogeneous gamma Lam r hLam hr q)
    · intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      exact ⟨M, fun q hq => (hM q hq).2.2 i k⟩
  exact ⟨hx, hv, hh⟩


/-- The ordinary scalar Wronskian, with the source solution first. -/
def scalarWronskian (f g : ℝ → ℝ) (s : ℝ) : ℝ := f s * deriv g s - deriv f s * g s


/-- The scalar Wronskian has exactly the exponential source normalization. -/
theorem scalarWronskian_identity (f g : ℝ → ℝ) (gamma : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfo : ∀ s, deriv (deriv f) s - s ^ 2 / 3 * deriv f s + gamma * s * f s = 0)
    (hgo : ∀ s, deriv (deriv g) s - s ^ 2 / 3 * deriv g s + gamma * s * g s = 0)
    (s : ℝ) : scalarWronskian f g s * Real.exp (-(s ^ 3 / 9)) =
      scalarWronskian f g 0  := by
  have scalarWronskian_hasDerivAt (s : ℝ) (hfo : deriv (deriv f) s - s ^ 2 / 3 * deriv f s + gamma * s * f s = 0) (hgo : deriv (deriv g) s - s ^ 2 / 3 * deriv g s + gamma * s * g s = 0) :
      HasDerivAt (scalarWronskian f g) (s ^ 2 / 3 * scalarWronskian f g s) s := by
    have hdf' := (hf.differentiable_deriv_two s).hasDerivAt
    have hdg' := (hg.differentiable_deriv_two s).hasDerivAt
    have hd := (((hf.differentiable (by norm_num) s).hasDerivAt).mul hdg').sub (hdf'.mul ((hg.differentiable (by norm_num) s).hasDerivAt))
    simp only [Pi.sub_def, Pi.mul_def] at hd
    unfold scalarWronskian
    convert hd using 1
    linear_combination g s * hfo - f s * hgo
  let w : ℝ → ℝ := fun t => scalarWronskian f g t * Real.exp (-(t ^ 3 / 9))
  have hd (t : ℝ) : HasDerivAt w 0 t := by
    have hpoly : HasDerivAt (fun t : ℝ => -(t ^ 3 / 9)) (-(t ^ 2 / 3)) t := by
      have hp := (((hasDerivAt_id t).pow 3).div_const 9).neg
      simp only [Pi.neg_def, id_eq] at hp
      convert hp using 1
      norm_num
      ring
    have hw := (scalarWronskian_hasDerivAt t (hfo t) (hgo t)).mul hpoly.exp
    simp only [Pi.mul_def] at hw
    change HasDerivAt (fun t => scalarWronskian f g t * Real.exp (-(t ^ 3 / 9))) 0 t
    convert hw using 1
    ring
  simpa only [w, zero_pow (by decide : 3 ≠ 0), zero_div, neg_zero, Real.exp_zero,
    mul_one] using (is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0)










/-- A power remainder of three lower degrees is negligible relative to the leading power. -/
theorem scalar_tail_eventually_pos (f : ℝ → ℝ) (alpha c : ℝ) (hc : 0 < c)
    (hr : IsBigO atTop (fun s => f s - c * Real.rpow s alpha)
      (fun s => Real.rpow s (alpha - 3))) : ∀ᶠ s in atTop, 0 < f s := by
  have hpow : Tendsto (fun s : ℝ => Real.rpow s (-3)) atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)
  have hzero := (Kummer.rpow_mul_isBigO_of_add_eq (fun s => f s - c * Real.rpow s alpha) (-alpha) (alpha - 3) (-3) (by simpa only [Real.rpow_eq_pow] using hr) (by ring)).trans_tendsto hpow
  have ht : Tendsto (fun s => f s / Real.rpow s alpha) atTop (𝓝 c) := by
    have h : Tendsto (fun s => c + s ^ (-alpha) *
        (f s - c * Real.rpow s alpha)) atTop (𝓝 (c + 0)) := tendsto_const_nhds.add hzero
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hs.le]
    field_simp
    ring
  filter_upwards [ht.eventually (Ioi_mem_nhds hc), eventually_gt_atTop 0] with s hs hs0
  exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hs0 alpha)).mp hs








/-- Continuous real functions with finite normalized limits have a global power bound. -/
theorem scalar_power_growth (f : ℝ → ℝ) (alpha c : ℝ) (hf : Continuous f)
    (ht : Tendsto (fun s => f s / Real.rpow |s| alpha) atTop (𝓝 c))
    (hb : Tendsto (fun s => f s / Real.rpow |s| alpha) atBot (𝓝 c)) :
    ∃ K : ℝ, 0 < K ∧ c ≤ K ∧ ∀ s, |f s| ≤ K * (1 + Real.rpow |s| alpha) := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp (ht.abs.eventually (Iio_mem_nhds (lt_add_one |c|)))
  obtain ⟨b, hb⟩ := eventually_atBot.mp (hb.abs.eventually (Iio_mem_nhds (lt_add_one |c|)))
  let R : ℝ := max (max a (-b)) 1
  have hR : 1 ≤ R := le_max_right _ _
  have hRa : a ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRb : -b ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hf.abs).bddAbove
  let K : ℝ := max (max M (|c| + 1)) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKM : M ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKc : |c| + 1 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨K, hK, (le_abs_self c).trans ((le_add_of_nonneg_right zero_le_one).trans hKc), ?_⟩
  intro s
  have hpow : 0 ≤ Real.rpow |s| alpha := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hs : s ∈ Icc (-R) R
  · have hm : |f s| ≤ M := hM (mem_image_of_mem _ hs)
    exact hm.trans (hKM.trans (le_mul_of_one_le_right hK.le (by linarith)))
  · have hs0 : s ≠ 0 := by
      intro hz
      apply hs
      subst s
      constructor <;> linarith
    have hp : 0 < Real.rpow |s| alpha := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_pos_of_pos (abs_pos.mpr hs0) alpha
    have hratio : |f s / Real.rpow |s| alpha| < |c| + 1 := by
      rcases lt_or_ge s (-R) with hleft | hleft
      · exact hb s (by linarith)
      · exact ha s (by
          have hr : R < s := by
            by_contra hn
            exact hs ⟨hleft, le_of_not_gt hn⟩
          linarith)
    rw [abs_div, abs_of_pos hp] at hratio
    exact ((div_lt_iff₀ hp).mp hratio).le.trans ((mul_le_mul_of_nonneg_right hKc hpow).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK.le))








/-- The literal scalar profile is continuous on the entire native carrier. -/
theorem scalarProfile_continuous (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) : Continuous (scalarProfile gamma Lam)   := by
  have scalarProfile_continuousAt_zero :
      ContinuousAt (scalarProfile gamma Lam) 0 := by
    have scalarProfile_growth :
        ∃ K : ℝ, 0 < K ∧ ∀ q : XV 1, |scalarProfile gamma Lam q| ≤
        K * (Real.rpow |q.1 0| gamma.1 + Real.rpow |q.2 0| (3 * gamma.1)) := by
      obtain ⟨K, hK, hKC, hF⟩ := (scalar_power_growth _ _ _ (F_contDiff_two gamma Lam hLam).continuous (F_ratio_atTop gamma Lam hLam) (F_ratio_atBot gamma Lam hLam hmatch))
      have hA (x v : ℝ) (hx : 0 < x) : |scalarAnsatz gamma Lam x v| ≤
          K * (Real.rpow x gamma.1 + Real.rpow |v| (3 * gamma.1)) := by
        have hp : 0 < Real.rpow x gamma.1 := by
          simpa only [Real.rpow_eq_pow] using Real.rpow_pos_of_pos hx gamma.1
        have h := mul_le_mul_of_nonneg_left (hF (scalarSimilarity x v)) hp.le
        have he := scalar_similarity_power_cancel gamma x v hx
        change |Real.rpow x gamma.1 * F gamma Lam (scalarSimilarity x v)| ≤ _
        rw [abs_mul, abs_of_pos hp]
        calc
          _ ≤ Real.rpow x gamma.1 * (K * (1 +
              Real.rpow |scalarSimilarity x v| (3 * gamma.1))) := h
          _ = K * (Real.rpow x gamma.1 + Real.rpow |v| (3 * gamma.1)) := by
            rw [← he]
            ring
      refine ⟨K, hK, ?_⟩
      intro q
      rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
      · simpa only [scalarProfile, not_lt.mpr hx.le, hx, ↓reduceIte,
          abs_of_neg hx, abs_neg] using hA (-q.1 0) (-q.2 0) (neg_pos.mpr hx)
      · simp only [scalarProfile, hx, lt_self_iff_false, ↓reduceIte, abs_zero,
          scalarTrace, abs_mul]
        simp only [Real.rpow_eq_pow, Real.zero_rpow gamma.2.1.ne', zero_add]
        rw [abs_of_pos (by
          simpa only [Real.rpow_eq_pow] using
            Real.rpow_pos_of_pos (mul_pos (by norm_num) hLam) (-gamma.1)),
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (abs_nonneg _) _)
      · simpa only [scalarProfile, hx, ↓reduceIte, abs_of_pos hx] using hA _ _ hx
    obtain ⟨K, hK, hb⟩ := scalarProfile_growth
    have hX : Continuous (fun q : XV 1 => Real.rpow |q.1 0| gamma.1) :=
      (Real.continuous_rpow_const gamma.2.1.le).comp (by fun_prop)
    have hV : Continuous (fun q : XV 1 => Real.rpow |q.2 0| (3 * gamma.1)) :=
      (Real.continuous_rpow_const (mul_pos (by norm_num) gamma.2.1).le).comp (by fun_prop)
    have hc : Continuous (fun q : XV 1 => K *
        (Real.rpow |q.1 0| gamma.1 + Real.rpow |q.2 0| (3 * gamma.1))) :=
      continuous_const.mul (hX.add hV)
    have ht := hc.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, abs_zero, Real.rpow_eq_pow,
      Real.zero_rpow gamma.2.1.ne',
      Real.zero_rpow (mul_pos (by norm_num : (0 : ℝ) < 3) gamma.2.1).ne',
      zero_add, mul_zero] at ht
    have hn : Tendsto (fun q => |scalarProfile gamma Lam q|) (𝓝 0) (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hb ht
    have hh : Tendsto (scalarProfile gamma Lam) (𝓝 0) (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hn)
    simpa only [ContinuousAt, scalarProfile_zero] using hh
  have scalarProfile_continuousAt_axis (q : XV 1) (hx : q.1 0 = 0) (hv : q.2 0 ≠ 0) :
      ContinuousAt (scalarProfile gamma Lam) q := by
    have scalarTrace_continuous :
        Continuous (scalarTrace gamma Lam) := by
      unfold scalarTrace
      have hp : 0 ≤ 3 * gamma.1 := (mul_pos (by norm_num) gamma.2.1).le
      exact continuous_const.mul ((Real.continuous_rpow_const hp).comp continuous_abs)
    have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
    have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
    let Sp : Set (XV 1) := {z | 0 < z.1 0}
    let Sn : Set (XV 1) := {z | z.1 0 < 0}
    let Sz : Set (XV 1) := {z | z.1 0 = 0}
    have ht : Sp ∪ Sn ∪ Sz = univ := by
      ext z
      simp only [Sp, Sn, Sz, mem_union, mem_ofPred_eq, mem_univ, iff_true]
      rcases lt_trichotomy (z.1 0) 0 with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
      · exact Or.inl (Or.inl h)
    have hq : scalarProfile gamma Lam q = scalarTrace gamma Lam (q.2 0) := by
      simp only [scalarProfile, hx, lt_self_iff_false, ↓reduceIte]
    change Tendsto _ (𝓝 q) _
    rw [hq, ← nhdsWithin_univ q, ← ht, nhdsWithin_union, nhdsWithin_union, tendsto_sup,
      tendsto_sup]
    constructor
    · constructor
      · have he := scalarAnsatz_tendsto_axis (𝓝[Sp] q) gamma Lam hLam hmatch
          (fun z => z.1 0) (fun z => z.2 0) (q.2 0) hv
          (by simpa only [hx] using
            ((hX.tendsto q).mono_left (nhdsWithin_le_nhds (s := Sp))))
          self_mem_nhdsWithin ((hV.tendsto q).mono_left nhdsWithin_le_nhds)
        apply he.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [scalarProfile, show 0 < z.1 0 from hz, ↓reduceIte]
      · have he := scalarAnsatz_tendsto_axis (𝓝[Sn] q) gamma Lam hLam hmatch
          (fun z => -z.1 0) (fun z => -z.2 0) (-q.2 0) (neg_ne_zero.mpr hv)
          (by simpa only [hx, neg_zero] using
            (hX.tendsto q).neg.mono_left (nhdsWithin_le_nhds (s := Sn)))
          (by filter_upwards [self_mem_nhdsWithin] with z hz; exact neg_pos.mpr hz)
          ((hV.tendsto q).neg.mono_left nhdsWithin_le_nhds)
        rw [scalarTrace_neg] at he
        apply he.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [scalarProfile, not_lt.mpr (show z.1 0 < 0 from hz).le,
          show z.1 0 < 0 from hz, ↓reduceIte]
    · have he := ((scalarTrace_continuous).comp hV).tendsto q
        |>.mono_left (nhdsWithin_le_nhds (s := Sz))
      apply he.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarProfile, show z.1 0 = 0 from hz, lt_self_iff_false, ↓reduceIte,
        Function.comp_def]
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hx : q.1 0 = 0
  · by_cases hv : q.2 0 = 0
    · have hq : q = 0 := by
        apply Prod.ext <;> funext i
        all_goals have hi : i = 0 := Subsingleton.elim _ _
        all_goals subst i
        · exact hx
        · exact hv
      subst q
      exact scalarProfile_continuousAt_zero
    · exact scalarProfile_continuousAt_axis q hx hv
  · exact (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx).continuousAt



/-- The actual reflected source profile is comparable with the literal native kinetic gauge. -/
theorem scalarProfile_comparison (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV 1,
      c * Real.rpow (rho q) (3 * gamma.1) ≤ scalarProfile gamma Lam q ∧
      scalarProfile gamma Lam q ≤ C * Real.rpow (rho q) (3 * gamma.1)  := by
  have scalarProfile_pos (q : XV 1) (hq : q ≠ 0) :
      0 < scalarProfile gamma Lam q := by
    let scalarSecondM (gamma : ScalarGamma) (s : ℝ) :=
      s * Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s)
    have F_pos (s : ℝ) :
        0 < F gamma Lam s := by
      have Fminus_pos (hs : s ≤ 0) :
          0 < Fminus gamma Lam s := by
        have Fminus_nonneg (s : ℝ) (hs : s ≤ 0) :
            0 ≤ Fminus gamma Lam s := by
          have Fminus_eventually_pos :
              ∀ᶠ s in atBot, 0 < Fminus gamma Lam s := by
            have hb := Fminus_negative_ray_asymptotic_of_M_expansion
              Kummer.M_negative_expansion gamma Lam hLam
            rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hb
            have hp := scalar_tail_eventually_pos (fun s => Fminus gamma Lam (-s)) (3 * gamma.1)
              (Real.rpow (9 * Lam) (-gamma.1))
              (by simpa only [Real.rpow_eq_pow] using
                Real.rpow_pos_of_pos (mul_pos (by norm_num) hLam) (-gamma.1)) hb
            simpa only [neg_neg] using tendsto_neg_atBot_atTop.eventually hp
          have Fminus_no_negative_local_min (s : ℝ) (hs : s < 0) (hmin : IsLocalMin (Fminus gamma Lam) s) :
              0 ≤ Fminus gamma Lam s := by
            have scalar_local_min_curvature (f : ℝ → ℝ) (hc : ContinuousAt f s) (hmin : IsLocalMin f s) :
                0 ≤ deriv (deriv f) s := by
              by_contra hn
              have hneg : deriv (deriv f) s < 0 := lt_of_not_ge hn
              have he : f =ᶠ[𝓝 s] fun _ => f s := by
                filter_upwards [hmin, (isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc)] with t ht ht'
                exact le_antisymm ht' ht
              have hz := he.deriv.deriv_eq
              simp only [deriv_const', deriv_const] at hz
              rw [hz] at hneg
              exact lt_irrefl _ hneg
            by_contra hn
            have hneg : Fminus gamma Lam s < 0 := lt_of_not_ge hn
            have ho := Fminus_ode gamma Lam s
            rw [hmin.deriv_eq_zero, mul_zero, sub_zero] at ho
            have hp : 0 < gamma.1 * s * Fminus gamma Lam s :=
              mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg gamma.2.1 hs) hneg
            linarith only [ho, (scalar_local_min_curvature (Fminus gamma Lam) (contDiff_Fminus gamma Lam).continuous.continuousAt hmin), hp]
          by_contra hn
          have hneg : Fminus gamma Lam s < 0 := lt_of_not_ge hn
          have hf0 : 0 < Fminus gamma Lam 0 := by
            rw [Fminus_zero]
            exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1
          have hs0 : s < 0 := lt_of_le_of_ne hs (by intro he; rw [he] at hneg; linarith only [hf0, hneg])
          obtain ⟨a, ha, has⟩ := ((Fminus_eventually_pos).and
            (eventually_lt_atBot s)).exists
          obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn
            (nonempty_Icc.mpr (has.trans hs0).le) (contDiff_Fminus gamma Lam).continuous.continuousOn
          have hms : Fminus gamma Lam m ≤ Fminus gamma Lam s := hmin ⟨has.le, hs⟩
          have hmn := lt_of_le_of_lt hms hneg
          have ham : a < m := lt_of_le_of_ne hm.1 (by
            intro he
            rw [← he] at hmn
            linarith only [ha, hmn])
          have hm0 : m < 0 := lt_of_le_of_ne hm.2 (by
            intro he
            rw [he] at hmn
            linarith only [hf0, hmn])
          have hc := Fminus_no_negative_local_min m hm0 (hmin.isLocalMin (Icc_mem_nhds ham hm0))
          exact not_lt_of_ge hc hmn
        have Fminus_no_zero_jet :
            ¬ (Fminus gamma Lam s = 0 ∧ deriv (Fminus gamma Lam) s = 0) := by
          intro hz
          have scalarSecondM_zero_jets :
              scalarSecondM gamma 0 = 0 ∧ deriv (scalarSecondM gamma) 0 = 1 := by
            have hc : scalarCubic 1 0 = 0 := by simp [scalarCubic]
            have hm := (Kummer.hasDerivAt_M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 0)).comp
              0 (hasDerivAt_scalarCubic 1 0)
            have hd := (hasDerivAt_id 0).mul hm
            simp only [Pi.mul_def, Function.comp_def, id_eq, hc, Kummer.M_zero,
              one_mul, zero_mul, add_zero] at hd
            unfold scalarSecondM
            exact ⟨by simp, hd.deriv⟩
          have scalarSecondM_ode (s : ℝ) :
              deriv (deriv (scalarSecondM gamma)) s - s ^ 2 / 3 * deriv (scalarSecondM gamma) s +
              gamma.1 * s * scalarSecondM gamma s = 0 := by
            have h := scalarCubic_second_ode (Kummer.M (1 / 3 - gamma.1) Kummer.b43) gamma.1 1 s
              one_ne_zero (Kummer.analyticOnNhd_M _ _).contDiff
              (by simpa only [Kummer.b43] using
                Kummer.M_ode (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s))
            unfold scalarSecondM
            simpa only [one_mul] using h
          have contDiff_scalarSecondM : ContDiff ℝ 2 (scalarSecondM gamma) :=
            contDiff_id.mul ((Kummer.analyticOnNhd_M _ _).contDiff.comp
                ((contDiff_scalarCubic 1).of_le (by norm_num)))
          have hw := scalarWronskian_identity (Fminus gamma Lam) (scalarSecondM gamma) gamma.1
            ((contDiff_Fminus gamma Lam).of_le (by norm_num)) (contDiff_scalarSecondM)
            (Fminus_ode gamma Lam) (scalarSecondM_ode) s
          simp only [scalarWronskian, hz.1, hz.2, zero_mul, sub_self, Fminus_zero,
            (scalarSecondM_zero_jets).1, (scalarSecondM_zero_jets).2,
            mul_zero, mul_one, sub_zero] at hw
          exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1.ne' hw.symm
        refine lt_of_le_of_ne (Fminus_nonneg s hs) ?_
        intro hz
        have hz' : Fminus gamma Lam s = 0 := hz.symm
        have hs0 : s < 0 := lt_of_le_of_ne hs (by
          intro he
          rw [he, Fminus_zero] at hz'
          exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1.ne' hz')
        have hmin : IsLocalMin (Fminus gamma Lam) s := by
          filter_upwards [Iio_mem_nhds hs0] with t ht
          rw [hz']
          exact Fminus_nonneg t ht.le
        exact Fminus_no_zero_jet ⟨hz', hmin.deriv_eq_zero⟩
      unfold F
      split_ifs with hs hs0
      · exact Fplus_pos gamma Lam s hLam hs
      · exact Fminus_pos hs0.le
      · exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1
    unfold scalarProfile scalarAnsatz
    split_ifs with hx hx'
    · exact mul_pos (Real.rpow_pos_of_pos hx _) (F_pos _)
    · exact mul_pos (Real.rpow_pos_of_pos (neg_pos.mpr hx') _) (F_pos _)
    · have hx0 : q.1 0 = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hx')
      have hv0 : q.2 0 ≠ 0 := by
        intro hv
        apply hq
        apply Prod.ext
        · funext i
          fin_cases i
          exact hx0
        · funext i
          fin_cases i
          exact hv
      exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hLam) _)
        (Real.rpow_pos_of_pos (abs_pos.mpr hv0) _)
  let K : Set (XV 1) := {q | rho q = 1}
  have hK : IsCompact K := (isCompact_rho_sublevel 1 1).of_isClosed_subset
    (isClosed_eq (continuous_rho 1) continuous_const) (fun _ h => le_of_eq h)
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hz
    have hh : rho q = 1 := hq
    simp only [hz, rho_zero] at hh
    norm_num at hh
  obtain ⟨c, C, hc, hcC, hbound⟩ := exists_positive_bounds_on_compact K hK
    (scalarProfile gamma Lam) (scalarProfile_continuous gamma Lam hLam hmatch).continuousOn
    (fun q hq => scalarProfile_pos q (hKnz q hq))
  refine ⟨c, C, hc, hcC, ?_⟩
  intro q
  by_cases hq : q = 0
  · subst q
    simp only [rho_zero, scalarProfile_zero, Real.rpow_eq_pow,
      Real.zero_rpow (mul_pos (by norm_num : (0 : ℝ) < 3) gamma.2.1).ne',
      mul_zero, le_refl, and_self]
  · have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
    let p := dilate (rho q)⁻¹ q
    have hp : p ∈ K := by
      change rho (dilate (rho q)⁻¹ q) = 1
      rw [rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have hpR : Real.rpow (rho q) (3 * gamma.1) *
        Real.rpow (rho q)⁻¹ (3 * gamma.1) = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.inv_rpow hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne']
    have hH : scalarProfile gamma Lam q =
        Real.rpow (rho q) (3 * gamma.1) * scalarProfile gamma Lam p := by
      dsimp only [p]
      rw [(scalarProfile_homogeneous gamma Lam (rho q)⁻¹ (inv_pos.mpr hr) q), ← mul_assoc, hpR, one_mul]
    obtain ⟨hlo, hhi⟩ := hbound p hp
    rw [hH]
    have hnonneg := (Real.rpow_pos_of_pos hr (3 * gamma.1)).le
    constructor
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hlo hnonneg
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hhi hnonneg



/-- Literal native point with scalar position and velocity coordinates. -/
def scalarPoint (x v : ℝ) : XV 1 := (fun _ => x, fun _ => v)

/-- Coordinate evaluation is a measurable equivalence, with no Euclidean carrier replacement. -/
def scalarNativeCoordinates : XV 1 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- The inverse coordinate map is exactly the literal native point constructor. -/
theorem scalarNativeCoordinates_symm_apply (p : ℝ × ℝ) :
    scalarNativeCoordinates.symm p = scalarPoint p.1 p.2 := rfl

/-- Coordinate evaluation preserves precisely the native product volume normalization. -/
theorem scalarNativeCoordinates_measurePreserving :
    MeasurePreserving scalarNativeCoordinates volume volume := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  convert (volume_preserving_funUnique (Fin 1) ℝ).prod (volume_preserving_funUnique (Fin 1) ℝ) using 1
  · funext q
    rfl
  · rfl


/-- The position-line tangent is the native position basis vector. -/
theorem scalarPoint_hasDerivAt_x (x v : ℝ) :
    HasDerivAt (fun t => scalarPoint t v) (Pi.single 0 1, 0) x :=
  scalarPositionSlice_hasDerivAt (scalarPoint 0 v) x



/-- Integration by parts for a continuous join whose classical derivative exists off zero. -/
theorem scalar_integral_mul_deriv_off_zero (u up v vp : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (hdu : ∀ x, x ≠ 0 → HasDerivAt u (up x) x)
    (hdv : ∀ x, HasDerivAt v (vp x) x)
    (hupv : Integrable (fun x => up x * v x))
    (huvp : Integrable (fun x => u x * vp x))
    (ht : Tendsto (fun x => u x * v x) atTop (𝓝 0))
    (hb : Tendsto (fun x => u x * v x) atBot (𝓝 0)) :
    (∫ x, u x * vp x) = -(∫ x, up x * v x) := by
  have hzero : Tendsto (u * v) (𝓝 0) (𝓝 (u 0 * v 0)) :=
    (hu.mul hv).tendsto 0
  have hvp := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic huvp
  have hup := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hupv
  simp only [compl_Iic] at hvp hup
  linear_combination (integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (fun x hx => hdu x hx.ne') (fun x _ => hdv x) (by simpa only [Pi.mul_def] using huvp.integrableOn) (by simpa only [Pi.mul_def] using hupv.integrableOn) (hzero.mono_left nhdsWithin_le_nhds) (by simpa only [Pi.mul_def] using ht)) + (integral_Iic_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (fun x hx => hdu x hx.ne) (fun x _ => hdv x) (by simpa only [Pi.mul_def] using huvp.integrableOn) (by simpa only [Pi.mul_def] using hupv.integrableOn) (hzero.mono_left nhdsWithin_le_nhds) (by simpa only [Pi.mul_def] using hb)) - hvp - hup



/-- Position integration by parts for a continuous native function with an actual off-axis jet. -/
theorem scalar_position_ibp (f g : XV 1 → ℝ) (hf : Continuous f)
    (hgi : LocallyIntegrable g volume)
    (hfd : ∀ q : XV 1, q.1 0 ≠ 0 → DifferentiableAt ℝ f q)
    (hfg : ∀ q : XV 1, q.1 0 ≠ 0 → fderiv ℝ f q (Pi.single 0 1, 0) = g q)
    (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ q, f q * dx test q 0) = -(∫ q, g q * test q)  := by
  have scalarNativeCoordinates_symm_measurePreserving :=
    MeasurePreserving.symm scalarNativeCoordinates scalarNativeCoordinates_measurePreserving
  let L : XV 1 → ℝ := fun q => f q * dx test q 0
  let R : XV 1 → ℝ := fun q => g q * test q
  have hL : Integrable L volume := by
    simpa only [L, dx, smul_eq_mul, mul_comm] using
      hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        ((ht.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
        (hs.fderiv_apply ℝ (Pi.single 0 1, 0))
  have hR : Integrable R volume := by
    simpa only [R, smul_eq_mul, mul_comm] using
      hgi.integrable_smul_left_of_hasCompactSupport ht.continuous hs
  have hLI := scalarNativeCoordinates_symm_measurePreserving.integrable_comp_of_integrable hL
  have hRI := scalarNativeCoordinates_symm_measurePreserving.integrable_comp_of_integrable hR
  rw [Measure.volume_eq_prod] at hLI hRI
  change (∫ q, L q) = -(∫ q, R q)
  rw [← (scalarNativeCoordinates_symm_measurePreserving.integral_comp' L), ← (scalarNativeCoordinates_symm_measurePreserving.integral_comp' R)]
  simp only [Function.comp_def] at hLI hRI
  rw [Measure.volume_eq_prod, integral_prod_symm _ hLI, integral_prod_symm _ hRI,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hLI.prod_left_ae, hRI.prod_left_ae] with v hLv hRv
  simp only [scalarNativeCoordinates_symm_apply, L, R] at hLv hRv ⊢
  have hP : Continuous (fun x => scalarPoint x v) := by unfold scalarPoint; fun_prop
  have hdu (x : ℝ) (hx : x ≠ 0) : HasDerivAt (fun t => f (scalarPoint t v))
      (g (scalarPoint x v)) x := by
    have hd := (hfd (scalarPoint x v) hx).hasFDerivAt.comp_hasDerivAt x
      (scalarPoint_hasDerivAt_x x v)
    simpa only [Function.comp_def, hfg (scalarPoint x v) hx] using hd
  have hdt (x : ℝ) : HasDerivAt (fun t => test (scalarPoint t v))
      (dx test (scalarPoint x v) 0) x := by
    simpa only [Function.comp_def, dx] using (ht.differentiable (by norm_num) (scalarPoint x v)).hasFDerivAt.comp_hasDerivAt x (scalarPoint_hasDerivAt_x x v)
  have hX : Continuous (fun q : XV 1 => q.1 0) := by fun_prop
  obtain ⟨B, hB⟩ := hs.isCompact.exists_bound_of_continuousOn hX.continuousOn
  have hzTop : ∀ᶠ x in atTop, test (scalarPoint x v) = 0 := by
    filter_upwards [eventually_gt_atTop B] with x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hq
    have hb := hB (scalarPoint x v) hq
    have hl : x ≤ |x| := le_abs_self x
    simp only [scalarPoint, Real.norm_eq_abs] at hb
    linarith
  have hzBot : ∀ᶠ x in atBot, test (scalarPoint x v) = 0 := by
    filter_upwards [eventually_lt_atBot (-B)] with x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hq
    have hb := hB (scalarPoint x v) hq
    have hl : -x ≤ |x| := neg_le_abs x
    simp only [scalarPoint, Real.norm_eq_abs] at hb
    linarith
  apply scalar_integral_mul_deriv_off_zero
    (fun x => f (scalarPoint x v)) (fun x => g (scalarPoint x v))
    (fun x => test (scalarPoint x v)) (fun x => dx test (scalarPoint x v) 0)
    (hf.comp hP) (ht.continuous.comp hP) hdu hdt hRv hLv
  · apply tendsto_const_nhds.congr'
    filter_upwards [hzTop] with x hx
    simp only [hx, mul_zero]
  · apply tendsto_const_nhds.congr'
    filter_upwards [hzBot] with x hx
    simp only [hx, mul_zero]

/-- The actual scalar profile has its native position weak identity. -/
theorem scalarProfile_position_weak (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test)
    (hs : HasCompactSupport test) :
    (∫ q, scalarProfile gamma Lam q * dx test q 0) =
      -(∫ q, scalarGx gamma Lam q 0 * test q) := by
  apply scalar_position_ibp _ _ (scalarProfile_continuous gamma Lam hLam hmatch)
    ((scalarJets_locallyIntegrable gamma Lam hLam hmatch).1 0)
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hq).differentiableAt
      (by norm_num)
  · intro q hq
    simp only [scalarGx, hq, ↓reduceIte, dx]
  · exact ht
  · exact hs




/-- Velocity integration by parts for a locally integrable jet smooth off the position axis. -/
theorem scalar_velocity_ibp (f g : XV 1 → ℝ)
    (hfi : LocallyIntegrable f volume) (hgi : LocallyIntegrable g volume)
    (hfd : ∀ q : XV 1, q.1 0 ≠ 0 → DifferentiableAt ℝ f q)
    (hfg : ∀ q : XV 1, q.1 0 ≠ 0 → fderiv ℝ f q (0, Pi.single 0 1) = g q)
    (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ q, f q * dv test q 0) = -(∫ q, g q * test q)  := by
  have scalar_position_cutoff_support (n : ℕ) (q : XV 1) (hq : q ∈ tsupport (fun z => test z * originCutoff n z.1)) :
      q.1 0 ≠ 0 := by
    intro hx
    have hz : q.1 = 0 := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hx
    have ht : Tendsto (Prod.fst : XV 1 → PDE.Vec 1) (𝓝 q) (𝓝 0) := by
      simpa only [hz] using continuous_fst.tendsto q
    have he := (originCutoff_eventually_zero 1 n).comp_tendsto ht
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hq
    filter_upwards [he] with z hz
    change originCutoff n z.1 = 0 at hz
    simp only [hz, mul_zero]
    rfl
  let : Measure.IsAddHaarMeasure (volume : Measure (PDE.Vec 1)) :=
    isAddHaarMeasure_volume_pi (Fin 1)
  let : Measure.IsAddHaarMeasure (volume : Measure (XV 1)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hderiv : ∀ᵐ q ∂volume, fderiv ℝ f q (0, Pi.single 0 1) = g q := by
    filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
    apply hfg q
    intro hz
    apply hq.1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hz
  let cut : ℕ → XV 1 → ℝ := fun n q => originCutoff n q.1
  have he (n : ℕ) : (∫ q, (f q * dv test q 0) * cut n q) =
      -(∫ q, (g q * test q) * cut n q) := by
    let t : XV 1 → ℝ := fun q => test q * cut n q
    have ht1 : ContDiff ℝ 1 t := ht.mul
      (((contDiff_originCutoff 1 n).of_le (by norm_num)).comp contDiff_fst)
    have htc : HasCompactSupport t := hs.mul_right
    have hgT : Integrable (fun q => g q * t q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hgi.integrable_smul_left_of_hasCompactSupport ht1.continuous htc
    have hfT : Integrable (fun q => f q * t q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hfi.integrable_smul_left_of_hasCompactSupport ht1.continuous htc
    have hfDT : Integrable (fun q => f q * fderiv ℝ t q (0, Pi.single 0 1)) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hfi.integrable_smul_left_of_hasCompactSupport
          ((ht1.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
          (htc.fderiv_apply ℝ (0, Pi.single 0 1))
    have hfGT : Integrable (fun q => fderiv ℝ f q (0, Pi.single 0 1) * t q) volume := by
      apply hgT.congr
      filter_upwards [hderiv] with q hq
      rw [hq]
    have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfGT hfDT hfT
      (fun q hq => hfd q (scalar_position_cutoff_support n q hq))
      (fun q _ => ht1.differentiable (by norm_num) q)
    have hR : (∫ q, fderiv ℝ f q (0, Pi.single 0 1) * t q) = ∫ q, g q * t q := by
      apply integral_congr_ae
      filter_upwards [hderiv] with q hq
      rw [hq]
    rw [hR] at hIBP
    change (∫ q, f q * dv t q 0) = -(∫ q, g q * t q) at hIBP
    simpa only [t, cut, dv_mul_position_cutoff test n _
      (ht.differentiable (by norm_num) _) 0, mul_assoc] using hIBP
  have hL : Integrable (fun q => f q * dv test q 0) volume := by
    simpa only [smul_eq_mul, mul_comm, dv] using
      hfi.integrable_smul_left_of_hasCompactSupport
        ((ht.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
        (hs.fderiv_apply ℝ (0, Pi.single 0 1))
  have hR : Integrable (fun q => g q * test q) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      hgi.integrable_smul_left_of_hasCompactSupport ht.continuous hs
  have hc (n : ℕ) : Measurable (cut n) :=
    ((contDiff_originCutoff 1 n).continuous.comp continuous_fst).measurable
  have hb (n : ℕ) (q : XV 1) : |cut n q| ≤ 1 := abs_originCutoff_le_one n q.1
  have hl : ∀ᵐ q ∂volume, Tendsto (fun n => cut n q) atTop (𝓝 1) := by
    filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
    exact originCutoff_tendsto q.1 hq.1
  exact tendsto_nhds_unique (integral_mul_cutoff_tendsto _ hL cut hc hb hl) (((integral_mul_cutoff_tendsto _ hR cut hc hb hl).neg).congr (fun n => (he n).symm))

/-- The actual scalar profile has its first native velocity weak identity. -/
theorem scalarProfile_velocity_weak (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test)
    (hs : HasCompactSupport test) :
    (∫ q, scalarProfile gamma Lam q * dv test q 0) =
      -(∫ q, scalarGv gamma Lam q 0 * test q) := by
  apply scalar_velocity_ibp _ _
    (scalarProfile_continuous gamma Lam hLam hmatch).locallyIntegrable
    ((scalarJets_locallyIntegrable gamma Lam hLam hmatch).2.1 0)
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hq).differentiableAt
      (by norm_num)
  · intro q hq
    simp only [scalarGv, hq, ↓reduceIte, dv]
  · exact ht
  · exact hs

/-- The actual scalar profile has its second native velocity weak identity. -/
theorem scalarProfile_hessian_weak (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (test : XV 1 → ℝ) (ht : ContDiff ℝ 2 test)
    (hs : HasCompactSupport test) :
    (∫ q, scalarProfile gamma Lam q * dvv test q 0 0) =
      (∫ q, scalarHess gamma Lam q 0 0 * test q) := by
  have hjet := scalarJets_locallyIntegrable gamma Lam hLam hmatch
  have hfirst := scalarProfile_velocity_weak gamma Lam hLam hmatch
    (fun q => dv test q 0) (contDiff_dv_test test ht 0)
    (hs.fderiv_apply ℝ (0, Pi.single 0 1))
  have hsecond : (∫ q, scalarGv gamma Lam q 0 * dv test q 0) =
      -(∫ q, scalarHess gamma Lam q 0 0 * test q) := by
    apply scalar_velocity_ibp _ _ (hjet.2.1 0) (hjet.2.2 0 0)
    · intro q hq
      exact scalarGv_differentiableAt gamma Lam hLam q hq 0
    · intro q hq
      exact (scalarHess_eq_velocity_derivative gamma Lam q hq 0 0).symm
    · exact ht.of_le (by norm_num)
    · exact hs
  change (∫ q, scalarProfile gamma Lam q * dvv test q 0 0) =
    -(∫ q, scalarGv gamma Lam q 0 * dv test q 0) at hfirst
  simpa only [hsecond, neg_neg] using hfirst



/-- The actual Appendix C scalar profile satisfies the complete branch interface. -/
theorem counterProfileOne_exists (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    CounterProfileOneStatement alpha := by
  let gamma : ScalarGamma := ⟨alpha / 3, by constructor <;> linarith⟩
  have hga : 3 * gamma.1 = alpha := by dsimp only [gamma]; ring
  obtain ⟨Lam, hLam, hmatch⟩ := exists_matching_ratio gamma.1 gamma.2.1 gamma.2.2
  have hp : 0 < Lam := lt_trans zero_lt_one hLam
  obtain ⟨c, C0, hc, hcC, hcomp⟩ := scalarProfile_comparison gamma Lam hp hmatch
  obtain ⟨Cg, hCg, hgrad⟩ := scalarGv_gauge_bound gamma Lam hp hmatch
  let C : ℝ := max C0 Cg
  have hC0 : C0 ≤ C := le_max_left _ _
  have hCgC : Cg ≤ C := le_max_right _ _
  refine ⟨Lam, c, C, scalarProfile gamma Lam, scalarGx gamma Lam, scalarGv gamma Lam,
    scalarHess gamma Lam, hLam, hc, hCg.trans_le hCgC,
    scalarProfile_continuous gamma Lam hp hmatch, scalarProfile_zero gamma Lam, ?_, ?_,
    measurable_scalarGx gamma Lam, measurable_scalarGv gamma Lam,
    measurable_scalarHess gamma Lam, scalarJets_eq_ae gamma Lam,
    scalarJets_equation_ae gamma Lam hp, ?_, scalarJets_compact_bound gamma Lam hp hmatch,
    ?_, ?_, ?_⟩
  · intro r hr q
    simpa only [hga] using scalarProfile_homogeneous gamma Lam r hr q
  · intro q
    have hh := hcomp q
    rw [hga] at hh
    exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_right hC0
      (Real.rpow_nonneg (rho_nonneg q) alpha))⟩
  · intro q hq
    have hh := hgrad q hq
    rw [hga] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hCgC
      (Real.rpow_nonneg (rho_nonneg q) (alpha - 1)))
  · intro r hr q
    simpa only [hga] using And.intro (scalarGx_homogeneous gamma Lam r hp hr q)
      (And.intro (scalarGv_homogeneous gamma Lam r hp hr q)
        (scalarHess_homogeneous gamma Lam r hp hr q))
  · intro test ht hs _hz
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact scalarProfile_position_weak gamma Lam hp hmatch test
        (ht.of_le (by norm_num)) hs
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact scalarProfile_velocity_weak gamma Lam hp hmatch test
        (ht.of_le (by norm_num)) hs
    · intro i k
      have hi : i = 0 := Subsingleton.elim _ _
      have hk : k = 0 := Subsingleton.elim _ _
      subst i
      subst k
      exact scalarProfile_hessian_weak gamma Lam hp hmatch test ht hs
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hp q hq).contDiffWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

