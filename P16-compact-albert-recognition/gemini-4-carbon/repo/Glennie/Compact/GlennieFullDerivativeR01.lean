module
public import Glennie.BasicLaws
public import Glennie.Compactness
public import Glennie.Covariance
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

@[expose] public section
namespace Glennie.Compact.GlennieScalarPotentialR01
open Glennie
noncomputable section
set_option autoImplicit false

def commU (x y z : Albert) : Albert := U x (U y z) - U y (U x z)

def doubledTriple (a z b : Albert) : Albert :=
  (2 : ℝ) • (jordan a (jordan z b) + jordan (jordan a z) b - jordan (jordan a b) z)

def glennieVector (x y z : Albert) : Albert :=
  doubledTriple (commU x y z) z (jordan x y) - commU x y (U z (jordan x y))

end
end Glennie.Compact.GlennieScalarPotentialR01

@[expose] public section
namespace Glennie.Compact.GlennieFullDerivativeR01

open Glennie
open Glennie.Compact.GlennieScalarPotentialR01
open Glennie.NativeGenerationEndpointR01

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

abbrev NativeTriple := Albert × (Albert × Albert)

def phiTriple (p : NativeTriple) : ℝ := phi p.1 p.2.1 p.2.2

section StableFullDerivative
set_option backward.isDefEq.respectTransparency false
attribute [local instance 20000] Glennie.nativeRealSMulComm Glennie.nativeRealContinuousAdd Glennie.nativeRealContinuousSMul
def fullDerivative (x y z : Albert) : NativeTriple →L[ℝ] ℝ :=
  (nativeInnerContinuous (glennieVector y z x)).coprod
    ((nativeInnerContinuous (glennieVector z x y)).coprod
      (nativeInnerContinuous (glennieVector x y z)))
end StableFullDerivative

private def Uc (a : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous a).comp (jordanContinuous a) - jordanContinuous (jordan a a)

private def cU (x y : Albert) : Albert →L[ℝ] Albert := (Uc x).comp (Uc y) - (Uc y).comp (Uc x)

private def UBd (z p : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous (jordan z p) + (jordanContinuous z).comp (jordanContinuous p) -
    (jordanContinuous p).comp (jordanContinuous z))

private theorem hasFDerivAt_phi_third (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x y w) (nativeInnerContinuous (glennieVector x y z)) z := by
  have hcU (w : Albert) : cU x y w = commU x y w := by
    simp only [cU, Uc, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, jordanContinuous_apply, commU, U]
  have hj {f g : Albert → Albert} {f' g' : Albert →L[ℝ] Albert}
      (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
      HasFDerivAt (fun w => jordan (f w) (g w))
        ((jordanContinuous (f z)).comp g' + (jordanContinuous (g z)).comp f') z :=
    (jordanContinuous.hasFDerivAt_of_bilinear hf hg).congr_fderiv <| ContinuousLinearMap.ext fun h => by
      change jordan (f z) (g' h) + jordan (f' h) (g z) = _
      rw [jordan_comm (f' h)]; rfl
  let p := jordan x y
  have hid : HasFDerivAt (fun w : Albert => w) (.id ℝ Albert) z := hasFDerivAt_id z
  have hp0 : HasFDerivAt (fun w => jordan w p) (jordanContinuous p) z := by
    simpa only [show (fun w => jordan w p) = jordanContinuous p from funext fun w => jordan_comm w p] using
      (jordanContinuous p).hasFDerivAt (x := z)
  have h1 := hj hid hp0
  have h2 : HasFDerivAt (fun w => jordan (jordan w w) p)
      ((jordanContinuous p).comp ((jordanContinuous z).comp (.id ℝ Albert) + (jordanContinuous z).comp (.id ℝ Albert))) z := by
    simpa only [Function.comp_def, jordanContinuous_apply, jordan_comm p] using (jordanContinuous p).hasFDerivAt.comp z (hj hid hid)
  have hUb : HasFDerivAt (fun w => U w p) (UBd z p) z :=
    ((h1.const_smul (2 : ℝ)).fun_sub h2).congr_fderiv <| ContinuousLinearMap.ext fun h => by
      simp only [UBd, sub_apply, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, jordanContinuous_apply, jordan_add_right, smul_sub, two_smul]; abel
  have hp := nativeInnerContinuous.hasFDerivAt_of_bilinear ((cU x y).hasFDerivAt (x := z)) hUb
  rw [show (fun w => nativeInnerContinuous (cU x y w) (U w p)) = fun w => phi x y w from
    funext fun w => by change inner (cU x y w) _ = _; rw [hcU]; rfl] at hp
  refine hp.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  have hj_adj (u q r : Albert) : inner q (jordan u r) = inner (jordan u q) r := by
    rw [← inner_jordan_associative, jordan_comm q u]
  have hU_adj (u q r : Albert) : inner q (U u r) = inner (U u q) r := by
    simp only [U, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hj_adj]
  have hdT_adj (a : Albert) : inner a (doubledTriple h p z) = inner h (doubledTriple a z p) := by
    have k1 : inner a (jordan h (jordan p z)) = inner h (jordan a (jordan z p)) := by
      rw [← inner_jordan_associative, jordan_comm a h, inner_jordan_associative, jordan_comm p z]
    have k2 (q r : Albert) : inner a (jordan (jordan h q) r) = inner h (jordan (jordan a r) q) := by
      rw [inner_comm a, inner_jordan_associative, inner_jordan_associative, jordan_comm r a, jordan_comm q (jordan a r)]
    simp only [doubledTriple, inner_smul_right, inner_sub_right, inner_add_right, k1, k2]
  have hUb_eq : UBd z p h = doubledTriple h p z := by
    simp only [UBd, doubledTriple, sub_apply, smul_apply, add_apply, ContinuousLinearMap.comp_apply, jordanContinuous_apply,
      jordan_comm z p, jordan_comm p h, jordan_comm (jordan p z) h, jordan_comm z (jordan h p), jordan_comm z h, jordan_comm p (jordan h z)]
  change inner (cU x y z) (UBd z p h) + inner (cU x y h) (U z p) = inner (glennieVector x y z) h
  rw [hcU, hcU, hUb_eq, hdT_adj, show inner (commU x y h) (U z p) = -inner h (commU x y (U z p)) by
    simp only [commU, inner_sub_left, inner_sub_right, ← hU_adj]; ring,
    inner_comm (glennieVector x y z) h, glennieVector, inner_sub_right]
  ring

theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) := by
  have hj {f g : NativeTriple → Albert} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
      Differentiable ℝ (fun p => jordan (f p) (g p)) := by
    simpa only [Function.comp_def, jordanContinuous_apply] using
      jordanContinuous.isBoundedBilinearMap.differentiable.comp (hf.prodMk hg)
  have hU {f g : NativeTriple → Albert} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
      Differentiable ℝ (fun p => U (f p) (g p)) := by
    simpa only [U, Pi.smul_apply] using ((hj hf (hj hf hg)).const_smul (2 : ℝ)).fun_sub (hj (hj hf hf) hg)
  have hdiff : Differentiable ℝ phiTriple := by
    have hl := (hU differentiable_fst (hU differentiable_snd.fst differentiable_snd.snd)).fun_sub
      (hU differentiable_snd.fst (hU differentiable_fst differentiable_snd.snd))
    have hr := hU differentiable_snd.snd (hj differentiable_fst differentiable_snd.fst)
    simpa only [Function.comp_def, show (fun p : NativeTriple => nativeInnerContinuous _ _) = phiTriple from rfl] using
      nativeInnerContinuous.isBoundedBilinearMap.differentiable.comp (hl.prodMk hr)
  have hcyc (a b c : Albert) : phi b c a = phi a b c := by
    rw [phi_swap_first_two c b a, phi_swap_first_third a b c, neg_neg]
  have hd1 : HasFDerivAt (fun w => phi w y z) (nativeInnerContinuous (glennieVector y z x)) x := by
    simpa only [show (fun w => phi w y z) = fun w => phi y z w from funext fun w => (hcyc w y z).symm] using
      hasFDerivAt_phi_third y z x
  have hd2 : HasFDerivAt (fun w => phi x w z) (nativeInnerContinuous (glennieVector z x y)) y := by
    simpa only [show (fun w => phi x w z) = fun w => phi z x w from funext fun w => hcyc z x w] using
      hasFDerivAt_phi_third z x y
  let D := fderiv ℝ phiTriple (x, y, z)
  have hd : HasFDerivAt phiTriple D (x, y, z) := (hdiff (x, y, z)).hasFDerivAt
  have hx : HasFDerivAt (fun w => phi w y z) (D.comp (.inl ℝ Albert (Albert × Albert))) x := by
    simpa only [Function.comp_def, phiTriple] using hd.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (y, z))
  have hyz : HasFDerivAt (fun q : Albert × Albert => phi x q.1 q.2)
      (D.comp (.inr ℝ Albert (Albert × Albert))) (y, z) := by
    simpa only [Function.comp_def, phiTriple] using hd.comp (y, z) (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (y, z))
  have hy : HasFDerivAt (fun w => phi x w z)
      ((D.comp (.inr ℝ Albert (Albert × Albert))).comp (.inl ℝ Albert Albert)) y := by
    simpa only [Function.comp_def] using hyz.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y z)
  have hz : HasFDerivAt (fun w => phi x y w)
      ((D.comp (.inr ℝ Albert (Albert × Albert))).comp (.inr ℝ Albert Albert)) z := by
    simpa only [Function.comp_def] using hyz.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) y z)
  refine hd.congr_fderiv ?_
  rw [← ContinuousLinearMap.coprod_comp_inl_inr D, hx.unique hd1,
    ← ContinuousLinearMap.coprod_comp_inl_inr (D.comp _), hy.unique hd2,
    hz.unique (hasFDerivAt_phi_third x y z), fullDerivative]

theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  by_contra hK
  have hU {a b : Albert} (ha : a ∈ K) (hb : b ∈ K) : U a b ∈ K :=
    K.sub_mem (K.smul_mem 2 (hJ a ha _ (hJ a ha b hb))) (hJ _ (hJ a ha a ha) b hb)
  have hcU {a b c : Albert} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : commU a b c ∈ K :=
    K.sub_mem (hU ha (hU hb hc)) (hU hb (hU ha hc))
  have hg0 {a b c : Albert} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : glennieVector a b c = 0 := by
    have hp := hJ a ha b hb
    have hg : glennieVector a b c ∈ K := K.sub_mem
      (K.smul_mem 2 (K.sub_mem (K.add_mem (hJ _ (hcU ha hb hc) _ (hJ c hc _ hp))
        (hJ _ (hJ _ (hcU ha hb hc) c hc) _ hp)) (hJ _ (hJ _ (hcU ha hb hc) _ hp) c hc)))
      (hcU ha hb (hU hc hp))
    have hcurve : (fun t : ℝ => phi a b (c + t • glennieVector a b c)) = fun _ => 0 := funext fun t => by
      by_contra hne
      exact hK (eq_top_of_phi_ne_zero K h1 hJ a b _ ha hb (K.add_mem hc (K.smul_mem t hg)) hne)
    have hlin : HasDerivAt (fun t : ℝ => c + t • glennieVector a b c) (glennieVector a b c) 0 := by
      simpa only [id_eq, one_smul] using HasDerivAt.const_add c ((hasDerivAt_id (0 : ℝ)).smul_const _)
    have hder : HasDerivAt (fun t : ℝ => phi a b (c + t • glennieVector a b c))
        (inner (glennieVector a b c) (glennieVector a b c)) 0 := by
      simpa only [Function.comp_def, zero_smul, add_zero] using
        ((hasFDerivAt_phi_third a b (c + (0 : ℝ) • glennieVector a b c)).comp_hasDerivAt 0 hlin).congr_deriv
          (show (nativeInnerContinuous _) _ = inner _ _ from rfl)
    rw [hcurve] at hder
    exact (inner_self_eq_zero _).mp (hder.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  refine hd ((hasFDerivAt_phiTriple x y z).fderiv.trans (ContinuousLinearMap.ext fun ⟨a, b, c⟩ => ?_))
  change inner (glennieVector y z x) a + (inner (glennieVector z x y) b + inner (glennieVector x y z) c) = 0
  simp only [hg0 hy hz hx, hg0 hz hx hy, hg0 hx hy hz, inner_zero_left, add_zero]

end
end Glennie.Compact.GlennieFullDerivativeR01
