/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/RiemannMapping.lean
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import BergmanWeakType.Rigidity.DiskShift
public import Mathlib.Analysis.Complex.Schwarz
import all Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Riemann mapping for bounded simply connected domains
-/

open Set Metric Function Filter
open scoped Topology

public section

namespace BergmanWeakType

open Complex

/-- A locally uniform limit of nonvanishing holomorphic maps is either zero near
any given zero, or nonvanishing there. Apply the maximum principle to the relative error. -/
private theorem eventually_eq_zero_of_tendstoLocallyUniformlyOn {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hn : ∀ᶠ i in l, ∀ z ∈ U, F i z ≠ 0) (hf : TendstoLocallyUniformlyOn F f l U)
    {x : ℂ} (hx : x ∈ U) (hzero : f x = 0) : ∀ᶠ z in 𝓝 x, f z = 0 := by
  by_contra h
  have hfd := hf.differentiableOn hd hU
  have hz := ((hfd.analyticAt (hU.mem_nhds hx)).eventually_eq_zero_or_eventually_ne_zero).resolve_left h
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
    ((hU.eventually_mem hx).and (eventually_nhdsWithin_iff.mp hz))
  have hsub : closedBall x r ⊆ U := fun z hz ↦ (hball hz).1
  have hs := sphere_subset_closedBall.trans hsub
  have hne z (hz : z ∈ sphere x r) : f z ≠ 0 :=
    (hball (sphere_subset_closedBall hz)).2 (ne_of_mem_sphere hz hr.ne')
  have hc := hfd.continuousOn.mono hs
  have hconst : TendstoUniformlyOn (fun _ : ι ↦ f) f l (sphere x r) := by
    simp_all [Metric.tendstoUniformlyOn_iff]
  have hlim := ((hf.mono hs).fun_sub hconst.tendstoLocallyUniformlyOn).fun_div₀ (hf.mono hs) (hc.sub hc) hc hne
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere x r)).mp hlim)
    (1 / 2) (by norm_num)
  obtain ⟨i, hi, hni, hc⟩ := (hd.and (hn.and hclose)).exists
  have hmax := norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    ((((hi.sub hfd).div hi hni).mono hsub).diffContOnCl_ball Subset.rfl) (C := 1 / 2)
    (fun z hz ↦ by simpa using (hc z (frontier_ball x hr.ne' ▸ hz)).le)
    (subset_closure (mem_ball_self hr))
  norm_num [hzero, hni x hx] at hmax


private theorem equicontinuousAt_of_mapsTo {ι : Type*} {F : ι → ℂ → ℂ}
    {U : Set ℂ} {x : ℂ} (hU : U ∈ 𝓝 x) (hd : ∀ i, DifferentiableOn ℂ (F i) U)
    (hF : ∀ i, MapsTo (F i) U (ball 0 1)) : EquicontinuousAt F x := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp hU
  have hcont : ContinuousAt (fun y : ℂ ↦ (2 / r) * dist y x) x := by fun_prop
  apply Metric.equicontinuousAt_of_continuity_modulus _ (by simpa using hcont.tendsto) F
  filter_upwards [ball_mem_nhds x hr] with y hy i
  rw [dist_comm (F i x)]
  refine dist_le_div_mul_dist_of_mapsTo_ball ((hd i).mono hrU) (fun z hz ↦ ?_) hy
  have h₁ := mem_ball_zero_iff.mp (hF i (hrU hz))
  have h₂ := mem_ball_zero_iff.mp (hF i (hrU (mem_ball_self hr)))
  exact (dist_le_norm_add_norm _ _).trans (by linarith)

open scoped UniformConvergence in
/-- Every bounded simply connected open domain is biholomorphic to the unit disk. -/
theorem exists_biholomorphic_unitBall {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hbdd : Bornology.IsBounded U) :
    ∃ φ ψ : ℂ → ℂ, DifferentiableOn ℂ φ disk ∧ DifferentiableOn ℂ ψ U ∧
      BijOn φ disk U ∧ InvOn ψ φ disk U ∧ ∀ z ∈ disk, deriv φ z ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hUc.nonempty
  obtain ⟨x₁, hx₁, hne⟩ := (infinite_of_mem_nhds x₀ (hUo.mem_nhds hx₀)).nontrivial.exists_ne x₀
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  set F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
  have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s}, TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := by
    intro f s
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using
        (tendsto_id'.mpr nhdsWithin_le_nhds : Tendsto id (𝓝[s] f) (𝓝 f))
  let A (f : ℂ → ℂ) := MapsTo f U disk ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0
  let s : Set (ℂ →ᵤ[𝔖] ℂ) := {f | A (F f) ∧ F f x₀ = 0}
  have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) U := fun f hf z hz ↦
    (differentiableAt_of_deriv_ne_zero (hf.1.2.2 z hz)).differentiableWithinAt
  have shift {g : ℂ → ℂ} (hg : A g) {a : ℂ} (ha : a ∈ disk) : A (diskShift a ∘ g) := by
    refine ⟨(diskShift_mapsTo ha).comp hg.1, (diskShift_bijOn ha).injOn.comp hg.2.1 hg.1, fun z hz ↦ ?_⟩
    rw [((hasDerivAt_diskShift ha (hg.1 hz)).comp z
      (differentiableAt_of_deriv_ne_zero (hg.2.2 z hz)).hasDerivAt).deriv]
    simp [diskShift_tau_ne_zero ha, diskShift_den_ne_zero ha (hg.1 hz), hg.2.2 z hz]
  obtain ⟨g, hg⟩ : s.Nonempty := by
    obtain ⟨f, hf, hi, hd⟩ := exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc
      (fun h ↦ NormedSpace.unbounded_univ ℂ ℂ (h ▸ hbdd))
    exact ⟨UniformOnFun.ofFun 𝔖 (diskShift (-f x₀) ∘ f),
      shift ⟨hf, hi, hd⟩ (by simpa using hf hx₀), diskShift_neg_self _⟩
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ ↦ And.right) (α := ℂ) (s := s) (F := F)
    .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    exact (equicontinuousAt_of_mapsTo (hUo.mem_nhds (hKU hz))
      (fun i ↦ hsd _ i.2) (fun i ↦ i.2.1.1)).equicontinuousWithinAt _
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1.1 (hK.1 hx)⟩
  obtain ⟨f₀, hf₀, hmax⟩ := hcmpct.exists_isMaxOn ⟨g, subset_closure hg⟩
    (f := fun f ↦ ‖F f x₁‖) (fun _ _ ↦ (hF.tendsto_at hx₁).norm)
  let := mem_closure_iff_nhdsWithin_neBot.mp hf₀
  let f := F f₀
  have hlim : TendstoLocallyUniformlyOn F f (𝓝[s] f₀) U := hF
  have he := eventually_mem_nhdsWithin (a := f₀) (s := s)
  have hpos : 0 < ‖f x₁‖ := (norm_pos_iff.mpr (fun h ↦ hne (hg.1.2.1 hx₁ hx₀ (h.trans hg.2.symm)))).trans_le
    (hmax (subset_closure hg))
  have hzero : f x₀ = 0 := tendsto_nhds_unique (hlim.tendsto_at hx₀)
    (tendsto_const_nhds.congr' (he.mono fun g hg ↦ hg.2.symm))
  have hpre := hUc.isPathConnected.isConnected.isPreconnected
  have hdiff := hlim.differentiableOn (he.mono hsd) hUo
  have ha := hdiff.analyticOnNhd hUo
  have hdn : ∀ z ∈ U, deriv f z ≠ 0 := by
    intro z hz hz0
    have hg := eventually_eq_zero_of_tendstoLocallyUniformlyOn hUo
      (he.mono fun g hg ↦ ((hsd g hg).analyticOnNhd hUo).deriv.differentiableOn)
      (he.mono fun g hg ↦ hg.1.2.2) (hlim.deriv (he.mono hsd) hUo) hz hz0
    exact (norm_pos_iff.mp hpos) ((hUo.is_const_of_deriv_eq_zero hpre hdiff
      (ha.deriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz hg) hx₁ hx₀).trans hzero)
  have strict z (hz : z ∈ U) : HasStrictDerivAt f (deriv f z) z := (ha z hz).hasStrictDerivAt
  have hm : MapsTo f U disk := by
    intro z hz
    change f z ∈ ball 0 1
    rw [← interior_closedBall' 0 1, mem_interior_iff_mem_nhds, ← (strict z hz).map_nhds_eq (hdn z hz)]
    exact (hUo.eventually_mem hz).mono fun w hw ↦ isClosed_closedBall.mem_of_tendsto (hlim.tendsto_at hw)
      (he.mono fun g hg ↦ ball_subset_closedBall (hg.1.1 hw))
  have hi : InjOn f U := by
    intro x hx y hy hxy
    by_contra hne
    have hU' := hUo.sdiff (isClosed_singleton (x := y))
    have hG := hlim.fun_sub ((hlim.tendsto_at hy).tendstoUniformlyOn_const _).tendstoLocallyUniformlyOn
    have hh := eventually_eq_zero_of_tendstoLocallyUniformlyOn hU'
      (he.mono fun g hg ↦ ((hsd g hg).sub_const _).mono sdiff_subset)
      (he.mono fun g hg z hz ↦ sub_ne_zero.mpr (fun h ↦ hz.2 (hg.1.2.1 hz.1 hy h)))
      (hG.mono sdiff_subset) ⟨hx, hne⟩ (sub_eq_zero.mpr hxy)
    exact hdn x hx (by simpa using Filter.EventuallyEq.deriv_eq (f := fun _ ↦ f y) (hh.mono fun _ hz ↦ sub_eq_zero.mp hz))
  have hsurj : SurjOn f U disk := by
    by_contra hsurj
    -- A missing point gives a holomorphic square-root map with a larger value at the second point.
    obtain ⟨c, hc, hmiss⟩ : ∃ c ∈ disk, c ∉ f '' U := by simpa only [SurjOn, not_subset] using hsurj
    have hnc : -c ∈ disk := by simpa using hc
    let b := diskShift (-c) ∘ f
    have hb : A b := shift ⟨hm, hi, hdn⟩ hnc
    have hbne (z : ℂ) (hz : z ∈ U) : b z ≠ 0 := fun h ↦
      hmiss ⟨z, hz, (diskShift_bijOn hnc).injOn (hm hz) hc (by simpa [b] using h)⟩
    obtain ⟨g, hgc, hg⟩ := exists_continuousOn_pow_eq hUc hUo
      (show ContinuousOn b U from fun z hz ↦ (differentiableAt_of_deriv_ne_zero (hb.2.2 z hz)).continuousAt.continuousWithinAt)
      (show 0 ∉ b '' U by aesop) two_ne_zero
    have hgm : MapsTo g U disk := fun z hz ↦ by
      simpa [← pow_lt_one_iff_of_nonneg (norm_nonneg (g z)) two_ne_zero, ← norm_pow, hg] using hb.1 hz
    have hg0 (z : ℂ) (hz : z ∈ U) : g z ≠ 0 := by grind
    have hgd (z : ℂ) (hz : z ∈ U) : deriv g z ≠ 0 := by
      have hd := (hasDerivAt_pow 2 (g z)).of_comp_left (hgc.continuousAt (hUo.mem_nhds hz))
        (differentiableAt_of_deriv_ne_zero (hb.2.2 z hz)).hasDerivAt (by simpa using hg0 z hz) (.of_forall hg)
      simp [hd.deriv, hb.2.2 z hz, hg0 z hz]
    have hgi : InjOn g U := ((hb.2.1.congr fun z _ ↦ (hg z).symm) : InjOn ((· ^ 2) ∘ g) U).of_comp
    let G := diskShift (-g x₀) ∘ g
    have hG : A G := shift ⟨hgm, hgi, hgd⟩
      (by simpa using hgm hx₀)
    apply (hmax (subset_closure (a := UniformOnFun.ofFun 𝔖 G) ⟨hG, by simp [F, G]⟩)).not_gt
    change ‖f x₁‖ < ‖G x₁‖
    have hc' : c = -(g x₀) ^ 2 := by simpa [b, hzero] using (congrArg Neg.neg (hg x₀)).symm
    have hf : f x₁ = G x₁ * diskShift (g x₀) (g x₁) := by
      have h := diskShift_neg_apply hnc (hm hx₁)
      change diskShift (- -c) (b x₁) = f x₁ at h
      rw [← h, ← hg, neg_neg, hc']
      simp only [G, comp_apply, diskShift, div_mul_div_comm, map_neg, map_pow]
      congr 1 <;> ring
    rw [hf, norm_mul] at hpos ⊢
    exact mul_lt_of_lt_one_right (pos_of_mul_pos_left hpos (norm_nonneg _))
      (mem_disk_iff _ |>.mp (diskShift_mapsTo (hgm hx₀) (hgm hx₁)))
  have hb : BijOn f U disk := ⟨hm, hi, hsurj⟩
  have hinv := hb.invOn_invFunOn
  let φ := invFunOn f U
  have dφ w (hw : w ∈ disk) : DifferentiableAt ℂ φ w ∧ deriv φ w ≠ 0 := by
    obtain ⟨z, hz, rfl⟩ := hsurj hw
    have hd : HasStrictDerivAt φ (deriv f z)⁻¹ (f z) :=
      (strict z hz).to_local_left_inverse
        (hdn z hz) ((hUo.eventually_mem hz).mono fun _ hz ↦ hinv.1 hz)
    exact ⟨hd.hasDerivAt.differentiableAt, by simp [hd.hasDerivAt.deriv, hdn z hz]⟩
  exact ⟨φ, f, fun w hw ↦ (dφ w hw).1.differentiableWithinAt,
    hdiff, hb.symm hinv.symm, hinv.symm, fun w hw ↦ (dφ w hw).2⟩

end BergmanWeakType
