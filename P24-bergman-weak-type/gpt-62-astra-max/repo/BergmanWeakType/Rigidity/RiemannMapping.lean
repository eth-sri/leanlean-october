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
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import BergmanWeakType.Rigidity.DiskAutomorphism
public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# A normalized extremal chart for bounded simply connected domains
-/

open Set Metric Function Filter BergmanWeakType
open scoped Pointwise Topology ComplexConjugate Real BigOperators Uniformity

public section

namespace Complex

/-- Local Hurwitz theorem: a zero of a locally uniform holomorphic limit of
nonvanishing functions cannot be isolated. -/
private theorem hurwitz {ι : Type*} {U : Set ℂ} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (op : IsOpen U) (hn : ∀ᶠ i in l, ∀ z ∈ U, F i z ≠ 0)
    (hd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (lim : TendstoLocallyUniformlyOn F f l U)
    {c : ℂ} (hc : c ∈ U) (h₀ : f c = 0) : f =ᶠ[𝓝 c] 0 := by
  have df := lim.differentiableOn hd op
  apply ((df.analyticAt (op.mem_nhds hc)).eventually_eq_zero_or_eventually_ne_zero).resolve_right
  intro h
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨R,hR,h⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (h.and (op.eventually_mem hc))
  have sub : closedBall c R ⊆ U := by grind
  -- On the circle the limit is nonzero, while at the center it vanishes. The
  -- same strict comparison holds simultaneously on the circle eventually.
  have e : ∀ᶠ p : ι × ℂ in l ×ˢ 𝓝ˢ (sphere c R), ‖F p.1 c‖ < ‖F p.1 p.2‖ := by
    apply (isCompact_sphere c R).mem_prod_nhdsSet_of_forall
    intro w hw
    have hwU := sub (sphere_subset_closedBall hw)
    apply ((lim.tendsto_at hc).norm.comp tendsto_fst).eventually_lt (((df.continuousOn.continuousAt (op.mem_nhds hwU)).tendsto.comp (tendsto_snd )).congr_uniformity (by grind [op.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp])).norm
    simpa [h₀] using (norm_pos_iff.mpr ((h (sphere_subset_closedBall hw)).1 (by aesop)))
  obtain ⟨i,hi,di,lt⟩ := (hn.and (hd.and (e.curry.mono fun _ he ↦ he.self_of_nhdsSet))).exists
  obtain ⟨w,hw,H⟩ := exists_mem_frontier_isMaxOn_norm isBounded_ball (by simp_all)
    ((di.inv hi).diffContOnCl_ball sub)
  rw [frontier_ball _ hR.ne'] at hw
  have := H (subset_closure (mem_ball_self hR))
  simp [inv_le_inv₀ (norm_pos_iff.mpr (hi c hc)) (norm_pos_iff.mpr (hi w (sub (sphere_subset_closedBall hw)))), (lt w hw).not_ge] at this

private theorem RegularOn.injOn_limit {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (reg : RegularOn f U) (hUo : IsOpen U) (hF : ∀ᶠ i in l, InjOn (F i) U)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    InjOn f U := by
  intro x hx y hy hxy
  by_contra! hne
  let V := U \ {y}
  have sub : V ⊆ U := sdiff_subset
  have e := hurwitz (hUo.sdiff isClosed_singleton)
    (hn := hF.mono fun i hi z hz ↦ sub_ne_zero.mpr (hi.ne (sub hz) hy hz.2))
    (hFd.mono fun i hi ↦ (hi.mono sub).sub_const _) ((hf.mono sub).fun_sub
      ((hf.tendsto_at hy).tendstoUniformlyOn_const _).tendstoLocallyUniformlyOn) ⟨hx,hne⟩ (sub_eq_zero.mpr hxy)
  have he : f =ᶠ[𝓝 x] fun _ ↦ f y := e.mono fun z hz ↦ sub_eq_zero.mp hz
  exact reg x hx (by simp_all [he.deriv_eq.trans])

private structure Candidate (U : Set ℂ) (x : ℂ) (f : ℂ → ℂ) : Prop where
  mapsTo : MapsTo f U disk
  inj : InjOn f U
  reg : RegularOn f U
  base : f x = 0

private theorem recenter {f : ℂ → ℂ} {U : Set ℂ} {x : ℂ} (hx : x ∈ U)
    (hm : MapsTo f U disk) (hi : InjOn f U) (hr : RegularOn f U) : Candidate U x (diskSwap (f x) ∘ f) :=
  let b := diskSwap_bijOn (hm hx)
  ⟨b.mapsTo.comp hm, b.injOn.comp hi hm, (diskSwap_regular (hm hx)).comp hr hm, diskSwap_self _⟩

/-- Moving an omitted point to zero, taking a square root, and moving its value at the
base point back to zero strictly increases the conformal radius functional. -/
private theorem exists_improved_chart {U : Set ℂ} (hU : IsOpen U) (hsc : IsSimplyConnected U)
    {x : ℂ} (hx : x ∈ U) {f : ℂ → ℂ} (cf : Candidate U x f) (hn : ¬ SurjOn f U disk) :
    ∃ g, Candidate U x g ∧ ‖deriv f x‖ < ‖deriv g x‖ := by
  obtain ⟨hm,hi,hf,hf₀⟩ := cf
  obtain ⟨c,hc,hmiss⟩ := not_subset.mp hn
  let T := diskSwap c ∘ f
  have dt z (hz : z ∈ U) := (diskSwap_hasDerivAt hc (hm hz)).comp z (hf.hd z hz)
  have tn : 0 ∉ T '' U := by
    rintro ⟨z,hz,eq⟩
    exact hmiss ⟨z,hz, (diskSwap_bijOn hc).injOn (hm hz) hc (eq.trans (by simp))⟩
  obtain ⟨g,cg,root⟩ := exists_continuousOn_pow_eq hsc hU (show ContinuousOn T U from
    fun z hz ↦ (dt z hz).continuousAt.continuousWithinAt) tn  two_ne_zero
  have gm : MapsTo g U disk := by
    intro z hz
    have h := (mem_disk_iff _).mp (diskSwap_mem hc (hm hz))
    change ‖T z‖ < 1 at h
    rw [← root, norm_pow] at h
    simp_all
  have gn z (hz : z ∈ U) : g z ≠ 0 := by grind
  have dg z (hz : z ∈ U) := (hasDerivAt_pow 2 (g z)).of_comp_left (cg.continuousAt (hU.mem_nhds hz)) (dt z hz)
    (by simp_all) (.of_forall (root))
  have dh z (hz : z ∈ U) := (diskSwap_hasDerivAt (gm hx) (gm hz)).comp z (dg z hz)
  refine ⟨_, recenter hx gm ?_ ?_, ?_⟩
  · intro a ha b hb eq
    exact hi ha hb ((diskSwap_bijOn hc).injOn (hm ha) (hm hb) (by grind))
  · intro z hz
    rw [(dg z hz).deriv]
    simp [(diskFactor_pos hc).ne', hf z hz, gn z hz]; exact diskSwap_den hc (hm hz)
  · have hs : ‖g x‖^2 = ‖c‖ := by simp [← norm_pow, root, T, hf₀]
    have G := diskFactor_pos (gm hx)
    rw [(dh x hx).deriv, ← factor_complex (g x)]
    simp [hf₀, abs_of_pos G, abs_of_pos (diskFactor_pos hc)]
    field_simp [(norm_pos_iff.mpr (gn x hx))]
    dsimp [diskFactor] at *
    rw [← hs]
    nlinarith [mul_pos (sq_pos_of_pos (sub_pos.mpr ((mem_disk_iff _).mp (gm hx)))) (norm_pos_iff.mpr (hf x hx))]

private theorem equicontinuousAt_of_mapsTo_disk {ι : Type*} {f : ι → ℂ → ℂ} {U : Set ℂ}
    {x : ℂ} (hU : U ∈ 𝓝 x) (hd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hm : ∀ i, MapsTo (f i) U disk) : EquicontinuousAt f x := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  apply equicontinuousAt_of_continuity_modulus (fun z ↦ 2 / r * dist z x) (by simpa using (show Continuous (fun z ↦ 2 / r * dist z x) by fun_prop).tendsto x)
  filter_upwards [ball_mem_nhds x hr] with z hz i
  rw [dist_comm]
  apply dist_le_div_mul_dist_of_mapsTo_ball ((hd i).mono hsub) _ hz
  intro w hw
  refine (dist_le_norm_add_norm _ _).trans ?_
  linarith [(mem_disk_iff _).mp (hm i (hsub hw)), (mem_disk_iff _).mp (hm i (mem_of_mem_nhds hU))]

open scoped UniformConvergence in
theorem exists_regular_bijOn_disk {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hb : Bornology.IsBounded U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, RegularOn f U ∧ BijOn f U disk := by
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  set F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
  have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s}, TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := by
    intro f s
    have : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using this
  let s := {f : ℂ →ᵤ[𝔖] ℂ | Candidate U x₀ (F f)}
  have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) U := fun _ hf ↦ hf.reg.diff
  have hs_ne : s.Nonempty := by
    obtain ⟨R,hR,sub⟩ := hb.subset_ball_lt 0 0
    have hn := ofReal_ne_zero.mpr hR.ne'
    refine ⟨_, recenter (f := fun z ↦ z/R) hx₀ (fun z hz ↦ ?_) (by simp_all) (by simp_all [RegularOn])⟩
    simpa [abs_of_pos hR,div_lt_one₀ hR] using sub hz
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ ↦ And.right)  (s := s) (F := F)
    .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    exact (equicontinuousAt_of_mapsTo_disk (hUo.mem_nhds (hKU hz)) (by measurability)
      (fun i ↦ i.2.1)).equicontinuousWithinAt _
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1 (hK.1 hx)⟩
  have hder {f} (hf : f ∈ closure s) : DifferentiableOn ℂ (F f) U := by
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    exact hF.differentiableOn (eventually_mem_nhdsWithin.mono hsd) hUo
  obtain ⟨f, hf, hmax⟩ := hcmpct.exists_isMaxOn hs_ne.closure (fun f _ ↦ ((hF.deriv (eventually_mem_nhdsWithin.mono (by assumption)) hUo).tendsto_at hx₀).norm)
  obtain ⟨f', hf'⟩ := hs_ne
  rw [mem_closure_iff_nhdsWithin_neBot] at hf
  have ht := hF (f := f) (s := s)
  have ev := @eventually_mem_nhdsWithin _ _ f s
  have H := ev.mono hsd
  have pc := hUc.isPathConnected.isConnected.isPreconnected
  have reg : RegularOn (F f) U := by
    intro z hz hzero
    have ht' := ht.deriv H hUo
    have H' := H.mono fun g h ↦ (h.analyticOnNhd hUo).deriv.differentiableOn
    have zero := hurwitz hUo (ev.mono fun g hg ↦ hg.reg) H' ht' hz hzero
    simpa [(((ht'.differentiableOn H' hUo).analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero pc hz zero hx₀), (hf'.reg x₀ hx₀)] using hmax (subset_closure hf')
  have fi := reg.injOn_limit hUo (ev.mono fun g hg ↦ hg.inj) H ht
  have f₀  := tendsto_nhds_unique (ht.tendsto_at hx₀)
    (tendsto_const_nhds.congr' (ev.mono fun g hg ↦ hg.base.symm))
  have fm : MapsTo (F f) U disk := by
    have hb z (hz : z ∈ U)  := le_of_tendsto (ht.tendsto_at hz).norm
      (ev.mono fun g hg ↦ ((mem_disk_iff _).mp (hg.1 hz)).le)
    intro z hz
    rw [mem_disk_iff]; by_contra! H
    have : F f x₀ = F f z := eqOn_of_isPreconnected_of_isMaxOn_norm pc hUo reg.diff hz (fun y hy ↦ (hb y hy).trans H) hx₀
    norm_num [← this, f₀] at H
  refine ⟨F f, reg, fm, fi, ?_⟩
  by_contra hn
  obtain ⟨g, hg, hlt⟩ := exists_improved_chart hUo hUc hx₀ ⟨fm,fi,reg,f₀⟩ hn
  exact hlt.not_ge (hmax (subset_closure (by assumption)))

end Complex
