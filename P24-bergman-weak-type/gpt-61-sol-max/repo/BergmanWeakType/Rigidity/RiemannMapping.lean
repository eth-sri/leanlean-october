/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/RiemannMapping.lean
-/
module

import all Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import BergmanWeakType.Rigidity.UnitDiscShift
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Tactic
public import BergmanWeakType.Derivative

variable {U : Set ℂ} {f : ℂ → ℂ} {z f' x : ℂ}

/-!
# Riemann mapping theorem (draft)
-/

open Set Metric Function Filter
open scoped Topology ComplexConjugate

public section

namespace Complex

section Hurwitz

variable {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U)
include hUo hUc hFd hf

theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn
    (hF : ∀ᶠ i in l, InjOn (F i) U) :
    (∃ C, ∀ x ∈ U, f x = C) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hfU x hx y hy hxy
  by_contra! hne
  let g := fun z ↦ f z - f y
  let G := fun i z ↦ F i z - F i y
  let V := U \ {y}
  have hxV : x ∈ V := ⟨hx, hne⟩
  have hgd := (hf.differentiableOn hFd hUo).sub_const (f y)
  have hg : TendstoLocallyUniformlyOn G g l U :=
    hf.fun_sub (hf.tendsto_at hy).tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn
  rcases (hgd.analyticAt (hUo.mem_nhds hx)).eventually_eq_zero_or_eventually_ne_zero
    with hzero | hzero
  · exact (hfU ⟨f y, fun z hz ↦ sub_eq_zero.mp
      ((hgd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hx hzero hz)⟩).elim
  · obtain ⟨R, hR₀, hRV, hfR⟩ : ∃ R > 0, closedBall x R ⊆ V ∧ ∀ w ∈ sphere x R, g w ≠ 0 := by
      rw [eventually_nhdsWithin_iff] at hzero
      rcases Metric.nhds_basis_closedBall.eventually_iff.mp
        (hzero.and ((hUo.sdiff isClosed_singleton).eventually_mem hxV)) with ⟨R, hR₀, hR⟩
      refine ⟨R, hR₀, fun w hw ↦ (hR hw).2,
        fun w hw ↦ (hR (sphere_subset_closedBall hw)).1 ?_⟩
      continuity
    have hRU := hRV.trans sdiff_subset
    have hRU' := sphere_subset_closedBall.trans hRU
    have hratio :=
      (hg.tendsto_at hx).tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn.fun_div₀
        (hg.mono hRU') continuousOn_const (hgd.continuousOn.mono hRU') hfR
    simp [g, hxy] at hratio
    rw [tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere x R)] at hratio
    obtain ⟨i, hi, hid, hb⟩ :=
      (hF.and (hFd.and (Metric.tendstoUniformlyOn_iff.mp hratio _ one_half_pos))).exists
    have hGi (z) (hz : z ∈ V) : G i z ≠ 0 := sub_ne_zero.mpr ((hi.ne_iff hz.1 hy).mpr hz.2)
    have hle := norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (((differentiableOn_const _).div ((hid.sub_const _).mono sdiff_subset) hGi).diffContOnCl_ball hRV)
      (fun z hz ↦ le_of_lt (by simpa using hb z (frontier_ball_subset_sphere hz)))
      (subset_closure (mem_ball_self hR₀))
    norm_num [G, hGi x hxV] at hle

end Hurwitz

namespace UnitDisc

@[fun_prop]
theorem continuous_shift (z : 𝔻) : Continuous z.shift := by
  simp [isEmbedding_coe.continuous_iff, Function.comp_def, coe_shift]
  exact .div (by fun_prop) (by fun_prop) fun _ ↦ shift_den_ne_zero _ _

end UnitDisc

theorem UnitDisc.hasDerivAt_shift_comp {f : ℂ → UnitDisc}
    (w : UnitDisc) (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z := by
  have := UnitDisc.shift_den_ne_zero w (f z)
  simp only [coe_shift, ← mul_conj']
  differentiate

section Mapping

variable (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : Bornology.IsBounded U)
include hUo hUc hU

variable (hx : x ∈ U)
include hx

open scoped UniformConvergence in
theorem exists_bijOn_unitBall_map_eq_zero :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x = 0 := by
  set 𝔖 := {K | K ⊆ U ∧ IsCompact K}
  set F := @UniformOnFun.toFun ℂ ℂ 𝔖
  have hF {f} {s} : TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := by
    have : Tendsto id (𝓝[s] f) _ := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [F, tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using this
  set s :=
    {f : ℂ →ᵤ[𝔖] ℂ |
      MapsTo (F f) U (ball 0 1) ∧
      InjOn (F f) U ∧
      DifferentiableOn ℂ (F f) U ∧
      deriv (F f) x ≠ 0 ∧
      F f x = 0}
  have hsd (f) (hf : f ∈ s) := hf.2.2.1
  have hs_ne : s.Nonempty := by
    obtain ⟨R, hRU⟩ := (isBounded_iff_subset_ball x).mp hU
    have hR := by simpa using hRU hx
    have hRc := Complex.ofReal_ne_zero.mpr hR.ne'
    have hd (z) := ((hasDerivAt_id z).sub_const x).div_const (R : ℂ)
    refine ⟨UniformOnFun.ofFun 𝔖 (fun z ↦ (z - x) / (R : ℂ)), ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      simpa [F, mem_ball, dist_eq_norm, norm_div, Complex.norm_real,
        abs_of_pos hR, div_lt_one hR] using hRU hz
    · simp [F, InjOn, div_left_inj' hRc]
    · exact fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt
    · exact (hd x).deriv.trans_ne (one_div_ne_zero hRc)
    · simp [F]
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ hK ↦ hK.2)  (s := s) 
    .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    suffices h : EquicontinuousAt (fun i : s ↦ F i) z from h.equicontinuousWithinAt _
    have hnorm (i : s) (w) (hw : w ∈ U) :=
      le_of_lt (by simpa using i.2.1 hw)
    obtain ⟨r, hr, hrU⟩ := nhds_basis_ball.mem_iff.mp (hUo.mem_nhds <| hKU hz)
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun y ↦ 2 / r * dist y z) (by
        simpa using ((continuous_id.dist (continuous_const (y := z))).const_mul (2 / r)).tendsto z) _
    filter_upwards [ball_mem_nhds z hr] with y hy i
    rw [dist_comm]
    exact dist_le_div_mul_dist_of_mapsTo_ball ((hsd _ i.2).mono hrU) (by
      intro w hw
      exact (dist_le_norm_add_norm _ _).trans
        (by linarith [hnorm i w (hrU hw), hnorm i z (hrU (mem_ball_self hr))])) hy
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1 (hK.1 hx)⟩
  have hcl {f} (hf : f ∈ closure s) := by
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    have htendsto := hF (f := f) (s := s)
    have hdf  := htendsto.differentiableOn
      (eventually_mem_nhdsWithin.mono hsd) hUo
    have hf_le (z) (hz : z ∈ U) := le_of_tendsto (htendsto.tendsto_at hz).norm
      (eventually_mem_nhdsWithin.mono fun g hg ↦ le_of_lt (by simpa using hg.1 hz))
    have hfx := tendsto_nhds_unique (htendsto.tendsto_at hx)
      (tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.2.2.2.symm))
    have hball : MapsTo (F f) U (ball 0 1) := by
      by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have : IsMaxOn (‖F f ·‖) U z := by
        intro y hy
        simpa using (hf_le y hy).trans hz
      have : F f x = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUc.isPathConnected.isConnected.isPreconnected hUo hdf hzU this hx
      norm_num [← this, hfx] at hz
    exact And.intro hball (And.intro (eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo
        hUc.isPathConnected.isConnected.isPreconnected
        (eventually_mem_nhdsWithin.mono hsd) htendsto
        (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.1)) (And.intro hdf hfx))
  rcases hcmpct.exists_isMaxOn hs_ne.closure (by
    intro f hf
    exact ((hF.deriv (eventually_mem_nhdsWithin.mono fun g hg ↦ (hcl hg).2.2.1) hUo).tendsto_at hx).norm
  ) with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x : 0 < ‖deriv (F f₀) x‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    refine lt_of_lt_of_le ?_ (hf₀_max <| subset_closure hf')
    continuity
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x⟩
  clear hcl
  replace hf₀_inj : InjOn (F f₀) U := by
    refine hf₀_inj.resolve_left ?_
    rintro ⟨C, hC⟩
    rw [EqOn.eventuallyEq_of_mem hC (hUo.mem_nhds hx) |>.deriv_eq] at hdf₀_x
    simp at hdf₀_x
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, ?_⟩, hf₀_x⟩
  by_contra! hsurj
  rw [isMaxOn_iff] at hf₀_max
  classical
  let f : ℂ → UnitDisc := fun z ↦ if hz : z ∈ U then
    .mk (F f₀ z) (by simpa using hf₀_mapsTo hz) else 0
  have heq : EqOn (UnitDisc.coe ∘ f) (F f₀) U := by
    intro z hz
    simp [f, hz]
  have hderiv := (heq.eventuallyEq_of_mem (hUo.mem_nhds hx)).deriv_eq
  replace hsurj : ¬SurjOn f U univ := by
    rw [← heq.surjOn_iff] at hsurj
    simpa [SurjOn, eq_univ_iff_forall, subset_def, UnitDisc.exists, ← UnitDisc.coe_inj] using hsurj
  have hdf := (differentiableOn_congr heq).mpr hf₀_diff
  have hf₀ : f x = 0 := by simp [f, hx, hf₀_x]
  have hf_inj := (heq.injOn_iff.mpr hf₀_inj).of_comp
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by simpa [SurjOn, eq_univ_iff_forall] using hsurj
  rcases UnitDisc.exists_continuousOn_pow_eq hUc hUo ((-c).continuous_shift.comp_continuousOn (UnitDisc.isEmbedding_coe.continuousOn_iff.mpr hdf.continuousOn))
    (by simpa) 2 with ⟨g, hgc, hgf⟩
  have hdg z (hz : z ∈ U) :=
    (hasDerivAt_pow 2 (g z : ℂ)).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp (-c) <| (hdf.hasDerivAt <| hUo.mem_nhds hz))
      (by simpa [← UnitDisc.pow_eq_zero (z := g z) (n := 2), hgf] using hc z hz)
      (.of_forall fun x ↦ congr(UnitDisc.coe $(hgf x)))
  let G := (-g x).shift ∘ g
  have hgt : ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ G) x‖ := by
    suffices h : ‖deriv (UnitDisc.coe ∘ f) x‖ <
        ‖deriv (f · : ℂ → ℂ) x‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 by
      convert h using 1
      have hgx : ‖(g x : ℂ)‖ = √‖(c : ℂ)‖ := by
        simpa [hf₀, UnitDisc.coe_pow, norm_pow] using
          congrArg (fun z : UnitDisc ↦ √‖(z : ℂ)‖) (hgf x)
      have hpos₁ := sub_pos.2 c.norm_lt_one
      simp [G, Function.comp_def, (UnitDisc.hasDerivAt_shift_comp _ (hdg x hx)).deriv,
        conj_mul', hgx, hf₀, ← sub_eq_add_neg, field]
      norm_cast
      simp [field, abs_of_pos, hpos₁, (sub_pos.2 c.sq_norm_lt_one)]
      ring
    rw [mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · rw [hderiv]
      exact hdf₀_x
    · have hc₀ : 0 < ‖(c : ℂ)‖ := by continuity
      suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
      have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg
  rw [hderiv] at hgt
  refine hf₀_max (UniformOnFun.ofFun _ (G · : ℂ → ℂ)) (subset_closure ?_) |>.not_gt hgt
  refine ⟨fun z _ ↦ (G z).2, by simpa [F, InjOn] using (by
    refine (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  ), (fun z hz ↦ (UnitDisc.hasDerivAt_shift_comp (-g x) (hdg z hz)).differentiableAt.differentiableWithinAt), ?_, by simp [G, F]⟩
  rw [← norm_pos_iff]
  exact (norm_nonneg _).trans_lt hgt

end Mapping

end Complex
