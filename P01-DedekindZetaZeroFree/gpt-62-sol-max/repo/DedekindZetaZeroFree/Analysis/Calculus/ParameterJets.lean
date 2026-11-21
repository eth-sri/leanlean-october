module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ParameterJets

section GenericChart
open scoped Topology
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option backward.isDefEq.respectTransparency.types false in

private theorem chartPartialEq (h : A → E → Y) (s : A) (z : E)
    (hh : DifferentiableAt ℝ (Function.uncurry h) (s, z)) :
    fderiv ℝ (h s) z =
      (fderiv ℝ (Function.uncurry h) (s, z)).comp (ContinuousLinearMap.inr ℝ A E) := (hh.hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)).fderiv

set_option backward.isDefEq.respectTransparency.types false in

private theorem chartMixedPartial (h : A → E → Y) (s : A) (z : E)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry h) (s, z)) (v : A) (w : E) :
    (fderiv ℝ (fun t => fderiv ℝ (h t) z) s) v w =
      (fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w v := by
  let H := Function.uncurry h
  let D := fderiv ℝ H
  let L := ContinuousLinearMap.inl ℝ A E
  let R := ContinuousLinearMap.inr ℝ A E
  let CR := (ContinuousLinearMap.compL ℝ E (A × E) Y).flip R
  let CL := (ContinuousLinearMap.compL ℝ A (A × E) Y).flip L
  have hD : HasFDerivAt D (fderiv ℝ D (s, z)) (s, z) :=
    (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hs : (fun t => fderiv ℝ (h t) z) =ᶠ[𝓝 s]
      (fun t => CR (D (t, z))) := by
    have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hn] with t ht
    exact chartPartialEq h t z (ht.differentiableAt (by simp))
  have hz : (fun x => fderiv ℝ (fun t => h t x) s) =ᶠ[𝓝 z]
      (fun x => CL (D (s, x))) := by
    have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hn] with x hx
    have hd : HasFDerivAt H (D (s, x)) (s, x) := (hx.differentiableAt (by simp)).hasFDerivAt
    have hleft : HasFDerivAt (fun t : A => H (t, x)) (CL (D (s, x))) s :=
      by convert hd.comp s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x) using 1 <;> rfl
    exact hleft.fderiv
  have hsd := CR.hasFDerivAt.comp s (hD.comp s (hasFDerivAt_prodMk_left s z))
  have hzd := CL.hasFDerivAt.comp z (hD.comp z (hasFDerivAt_prodMk_right s z))
  have hsde := hsd.fderiv
  have hzde := hzd.fderiv
  dsimp only [Function.comp_def] at hsde hzde
  rw [hs.fderiv_eq, hz.fderiv_eq, hsde, hzde]
  exact (hh.isSymmSndFDerivAt (by simp)).eq (v, 0) (0, w)

end GenericChart

section Complex
open Filter
open scoped Topology
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
lemma hasDerivAt_fderiv_space (h k : ℂ → E → Y) (Ω : Set ℂ) (hΩ : IsOpen Ω) (U : Set E) (hU : IsOpen U)
 (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Ω ×ˢ U))
 (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Ω ×ˢ U))
 (hd : ∀ s ∈ Ω, ∀ z, z ∈ U → HasDerivAt (fun t => h t z) (k s z) s)
 (s : ℂ) (hs : s ∈ Ω) (z : E) (hz : z ∈ U) :
 HasDerivAt (fun t => fderiv ℝ (h t) z) (fderiv ℝ (k s) z) s := by
 have hlocal := hh.contDiffAt ((hΩ.prod hU).mem_nhds (show (s,z) ∈ Ω ×ˢ U from ⟨hs,hz⟩))
 have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
     (fun q : ℂ × E => h q.1 q.2) (s,z) := hlocal
 have hder : DifferentiableAt ℝ (fun t => fderiv ℝ (h t) z) s := by
   have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
       (Function.uncurry (fun t x => h t x)) (s,z) := hlocal
   exact (h2.fderiv (g := fun _ : ℂ => z) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)
 have heq : (ContinuousLinearMap.toSpanSingleton ℂ (fderiv ℝ (k s) z)).restrictScalars ℝ =
     fderiv ℝ (fun t => fderiv ℝ (h t) z) s := by
   ext d w
   rw [chartMixedPartial h s z hlocal d w]
   have ht : (fun x => (fderiv ℝ (fun t => h t x) s) d) =ᶠ[𝓝 z]
       (fun x => d • k s x) := by
     filter_upwards [hU.mem_nhds hz] with x hx
     rw [((hd s hs x hx).hasFDerivAt.restrictScalars ℝ).fderiv]
     rfl
   have hp := (hk.contDiffAt ((hΩ.prod hU).mem_nhds (show (s,z) ∈ Ω ×ˢ U from ⟨hs,hz⟩))).comp
     z (contDiffAt_const.prodMk contDiffAt_id)
   have hf := hp.differentiableAt (by simp)
   have hswap : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (fun x t => h t x)) (z,s) :=
     hlocal.comp (z,s) (contDiff_snd.prodMk contDiff_fst).contDiffAt
   have happ := (ContinuousLinearMap.apply ℝ Y d).hasFDerivAt.comp z
     ((hswap.fderiv (g := fun _ : E => s) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)).hasFDerivAt
   have he : (fderiv ℝ (fun x => (fderiv ℝ (fun t => h t x) s) d) z) w =
       ((fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w) d := by
     have he := happ.fderiv
     dsimp only [Function.comp_def] at he
     convert congrArg (fun T : E →L[ℝ] Y => T w) he using 1 <;> rfl
   rw [← he, ht.fderiv_eq]
   have hf' : DifferentiableAt ℝ (k s) z := hf
   change (d • fderiv ℝ (k s) z) w = (fderiv ℝ (d • k s) z) w
   rw [fderiv_const_smul hf' d]
 exact hasFDerivAt_of_restrictScalars ℝ hder.hasFDerivAt heq

end Complex

section JointJets
open scoped Topology
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
section ComplexJets
variable [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
end ComplexJets
end JointJets

section CompactDifferentiation
open scoped Topology
open Filter
open scoped Topology
variable {X Y : Type*} [UniformSpace X] [CompactSpace X]
 [NormedAddCommGroup Y] [NormedSpace ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
lemma compact_hasDeriv (h k : ℂ → C(X,Y))
 (hk : Continuous (Function.uncurry (fun t x => k t x)))
 (hd : ∀ t x, HasDerivAt (fun r => h r x) (k t x) t) (s : ℂ) :
 HasDerivAt h (k s) s := by
 apply HasDerivAt.of_isLittleO
 rw [Asymptotics.isLittleO_iff]
 intro c hc
 have hu := Metric.tendstoUniformly_iff.mp (hk.tendstoUniformly (fun t x => k t x) s) c hc
 have hseg : ∀ᶠ t in 𝓝 s, ∀ r ∈ segment ℝ s t, ∀ x : X, ‖k r x - k s x‖ ≤ c := by
   have hs : ∀ᶠ t in 𝓝[Set.univ] s, ∀ x : X, ‖k t x - k s x‖ ≤ c := by
     simpa only [nhdsWithin_univ, dist_eq_norm_sub, norm_sub_rev] using hu.mono (fun t ht x => (ht x).le)
   simpa only [nhdsWithin_univ] using (convex_univ : Convex ℝ (Set.univ : Set ℂ)).eventually_nhdsWithin_segment (Set.mem_univ s) hs
 filter_upwards [hseg] with t ht
 apply (ContinuousMap.norm_le (h t - h s - (t-s) • k s) (mul_nonneg hc.le (norm_nonneg _))).mpr
 intro x
 have H := (convex_segment s t).norm_image_sub_le_of_norm_hasFDerivWithin_le'
   (f := fun r => h r x) (f' := fun r => ContinuousLinearMap.toSpanSingleton ℂ (k r x))
   (φ := ContinuousLinearMap.toSpanSingleton ℂ (k s x)) (C := c)
   (fun r _ => (hd r x).hasFDerivAt.hasFDerivWithinAt)
   (fun r hr => by
     have he : ContinuousLinearMap.toSpanSingleton ℂ (k r x) - ContinuousLinearMap.toSpanSingleton ℂ (k s x) =
       ContinuousLinearMap.toSpanSingleton ℂ (k r x - k s x) := by ext a; simp [smul_sub]
     rw [he, ContinuousLinearMap.norm_toSpanSingleton]
     exact ht r hr x)
   (left_mem_segment ℝ s t) (right_mem_segment ℝ s t)
 simpa using H

end CompactDifferentiation

end DedekindZetaZeroFree.ParameterJets
