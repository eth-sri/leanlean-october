module
public import Glennie.Compact.LocalContrast
public import Glennie.Compactness
public import Glennie.NativeGenerationEndpointR01
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
open Glennie Glennie.Compact.OperationalPhi
noncomputable section
set_option autoImplicit false

def commU (x y z : Albert) : Albert := U x (U y z) - U y (U x z)

def doubledTriple (a z b : Albert) : Albert :=
  (2 : ℝ) • (jordan a (jordan z b) + jordan (jordan a z) b - jordan (jordan a b) z)

def glennieVector (x y z : Albert) : Albert :=
  doubledTriple (commU x y z) z (jordan x y) - commU x y (U z (jordan x y))

theorem commU_pairing (x y a b : Albert) :
    inner (commU x y a) b = -inner a (commU x y b) := by
  simp only [commU, inner_sub_left, inner_sub_right, ← U_pairing_selfadjoint]; ring

end
end Glennie.Compact.GlennieScalarPotentialR01

namespace Glennie.Compact.GlennieFullDerivativeR01
open Glennie Glennie.Compact.GlennieScalarPotentialR01
open Glennie.NativeGenerationEndpointR01
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

@[simp] private theorem pairingContinuous_apply (a b : Albert) :
    nativeInnerContinuous a b = inner a b := rfl

private def UContinuous (x : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous x).comp (jordanContinuous x) - jordanContinuous (jordan x x)

@[simp] private theorem UContinuous_apply (x z : Albert) : UContinuous x z = U x z := rfl

private def commUContinuous (x y : Albert) : Albert →L[ℝ] Albert :=
  (UContinuous x).comp (UContinuous y) - (UContinuous y).comp (UContinuous x)

@[simp] private theorem commUContinuous_apply (x y z : Albert) :
    commUContinuous x y z = commU x y z := by
  simp only [commUContinuous, sub_apply, ContinuousLinearMap.comp_apply, UContinuous_apply, commU]

private def UBaseDerivative (z p : Albert) : Albert →L[ℝ] Albert :=
  (2 : ℝ) • (jordanContinuous (jordan z p) +
    (jordanContinuous z).comp (jordanContinuous p) -
    (jordanContinuous p).comp (jordanContinuous z))

@[simp] private theorem UBaseDerivative_apply (z p h : Albert) :
    UBaseDerivative z p h =
      (2 : ℝ) • (jordan (jordan z p) h + jordan z (jordan p h) - jordan p (jordan z h)) := rfl

private theorem UBaseDerivative_eq_triple (z p h : Albert) :
    UBaseDerivative z p h = doubledTriple h p z := by
  simp only [UBaseDerivative_apply, doubledTriple,
    jordan_comm z p, jordan_comm p h, jordan_comm (jordan p z) h,
    jordan_comm z (jordan h p), jordan_comm z h, jordan_comm p (jordan h z)]

private theorem hasFDerivAt_jordan {f g : Albert → Albert} {f' g' : Albert →L[ℝ] Albert} {z : Albert}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => jordan (f w) (g w))
      ((jordanContinuous (f z)).comp g' + (jordanContinuous (g z)).comp f') z := by
  have hp := jordanContinuous.hasFDerivAt_of_bilinear hf hg
  change HasFDerivAt (fun w => jordan (f w) (g w)) _ z at hp
  refine hp.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  change jordan (f z) (g' h) + jordan (f' h) (g z) = jordan (f z) (g' h) + jordan (g z) (f' h)
  rw [jordan_comm (f' h) (g z)]

private theorem hasFDerivAt_U_base (z p : Albert) :
    HasFDerivAt (fun w : Albert => U w p) (UBaseDerivative z p) z := by
  have hid : HasFDerivAt (fun w : Albert => w) (.id ℝ Albert) z := hasFDerivAt_id z
  have hp : HasFDerivAt (fun w : Albert => jordan w p) (jordanContinuous p) z := by
    have hfun : (fun w : Albert => jordan w p) = (jordanContinuous p : Albert → Albert) :=
      funext fun w => by rw [jordanContinuous_apply, jordan_comm]
    rw [hfun]; exact (jordanContinuous p).hasFDerivAt (x := z)
  have hsecond : HasFDerivAt (fun w : Albert => jordan (jordan w w) p)
      ((jordanContinuous p).comp
        ((jordanContinuous z).comp (.id ℝ Albert) + (jordanContinuous z).comp (.id ℝ Albert))) z := by
    simpa only [Function.comp_def, jordanContinuous_apply, jordan_comm p] using
      (jordanContinuous p).hasFDerivAt.comp z (hasFDerivAt_jordan hid hid)
  have hU := ((hasFDerivAt_jordan hid hp).const_smul (2 : ℝ)).sub hsecond
  have hfun : ((2 : ℝ) • (fun w : Albert => jordan w (jordan w p)) -
      (fun w : Albert => jordan (jordan w w) p)) = (fun w : Albert => U w p) :=
    funext fun w => by simp only [Pi.sub_apply, Pi.smul_apply, U]
  rw [hfun] at hU
  refine hU.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  simp only [sub_apply, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, jordanContinuous_apply, UBaseDerivative_apply]
  rw [jordan_add_right, smul_sub, add_comm (jordan (jordan z p) h), two_smul ℝ (jordan p (jordan z h))]

private theorem doubledTriple_adjoint (a h p z : Albert) :
    inner a (doubledTriple h p z) = inner h (doubledTriple a z p) := by
  have h1 : inner a (jordan h (jordan p z)) = inner h (jordan a (jordan z p)) := by
    rw [← inner_jordan_associative, jordan_comm a h, inner_jordan_associative, jordan_comm p z]
  have h2 : inner a (jordan (jordan h p) z) = inner h (jordan (jordan a z) p) := by
    rw [inner_comm a, inner_jordan_associative, inner_jordan_associative,
      jordan_comm z a, jordan_comm p (jordan a z)]
  have h3 : inner a (jordan (jordan h z) p) = inner h (jordan (jordan a p) z) := by
    rw [inner_comm a, inner_jordan_associative, inner_jordan_associative,
      jordan_comm p a, jordan_comm z (jordan a p)]
  simp only [doubledTriple, inner_smul_right, inner_sub_right, inner_add_right, h1, h2, h3]

private theorem hasFDerivAt_phi_third (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x y w) (nativeInnerContinuous (glennieVector x y z)) z := by
  have hp := nativeInnerContinuous.hasFDerivAt_of_bilinear
    ((commUContinuous x y).hasFDerivAt (x := z)) (hasFDerivAt_U_base z (jordan x y))
  have hfun : (fun w : Albert => nativeInnerContinuous (commUContinuous x y w) (U w (jordan x y))) =
      (fun w : Albert => phi x y w) :=
    funext fun w => by simp only [pairingContinuous_apply, commUContinuous_apply, phi, commU]
  rw [hfun] at hp
  refine hp.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  simp only [add_apply, ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    pairingContinuous_apply, commUContinuous_apply]
  rw [UBaseDerivative_eq_triple, doubledTriple_adjoint, commU_pairing x y h (U z (jordan x y)),
    inner_comm (glennieVector x y z) h, glennieVector, inner_sub_right]
  ring

private theorem glennieVector_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z ∈ K := by
  have hU {a b} (ha : a ∈ K) (hb : b ∈ K) : U a b ∈ K :=
    K.sub_mem (K.smul_mem 2 (hJ _ ha _ (hJ _ ha _ hb))) (hJ _ (hJ _ ha _ ha) _ hb)
  have hC {a b c} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : commU a b c ∈ K :=
    K.sub_mem (hU ha (hU hb hc)) (hU hb (hU ha hc))
  have hT {a b c} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : doubledTriple a b c ∈ K :=
    K.smul_mem 2 (K.sub_mem (K.add_mem (hJ _ ha _ (hJ _ hb _ hc)) (hJ _ (hJ _ ha _ hb) _ hc))
      (hJ _ (hJ _ ha _ hc) _ hb))
  have hp := hJ _ hx _ hy
  exact K.sub_mem (hT (hC hx hy hz) hz hp) (hC hx hy (hU hz hp))

private theorem glennieVector_eq_zero_of_ne_top
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K) (hK : K ≠ ⊤)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    glennieVector x y z = 0 := by
  let g := glennieVector x y z
  have hg : g ∈ K := glennieVector_mem K hJ x y z hx hy hz
  have hcurve : (fun t : ℝ => phi x y (z + t • g)) = (fun _ : ℝ => (0 : ℝ)) :=
    funext fun t => by
      by_contra hphi
      exact hK (eq_top_of_phi_ne_zero K h1 hJ x y (z + t • g) hx hy (K.add_mem hz (K.smul_mem t hg)) hphi)
  have hc : HasDerivAt (fun t : ℝ => z + t • g) g 0 := by
    simpa only [id_eq, one_smul] using HasDerivAt.const_add z ((hasDerivAt_id (0 : ℝ)).smul_const g)
  have hd : HasDerivAt (fun t : ℝ => phi x y (z + t • g)) (inner g g) 0 := by
    simpa only [Function.comp_def, pairingContinuous_apply, zero_smul, add_zero] using
      (hasFDerivAt_phi_third x y (z + (0 : ℝ) • g)).comp_hasDerivAt 0 hc
  rw [hcurve] at hd
  exact (inner_self_eq_zero g).mp (hd.unique (hasDerivAt_const 0 0))

abbrev NativeTriple := Albert × (Albert × Albert)

def phiTriple (p : NativeTriple) : ℝ := phi p.1 p.2.1 p.2.2

private theorem phi_cyclic (x y z : Albert) : phi y z x = phi x y z := by
  rw [phi_swap_first_two z y x, phi_swap_first_third x y z, neg_neg]

private theorem hasFDerivAt_phi_first (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi w y z) (nativeInnerContinuous (glennieVector y z x)) x := by
  have hfun : (fun w : Albert => phi w y z) = (fun w => phi y z w) := funext fun w => (phi_cyclic w y z).symm
  rw [hfun]; exact hasFDerivAt_phi_third y z x

private theorem hasFDerivAt_phi_second (x y z : Albert) :
    HasFDerivAt (fun w : Albert => phi x w z) (nativeInnerContinuous (glennieVector z x y)) y := by
  have hfun : (fun w : Albert => phi x w z) = (fun w => phi z x w) := funext fun w => phi_cyclic z x w
  rw [hfun]; exact hasFDerivAt_phi_third z x y

private theorem diff_J {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => jordan (f p) (g p)) := by
  have hd := jordanContinuous.isBoundedBilinearMap.differentiable.comp (hf.prodMk hg)
  have hfun : ((fun q : Albert × Albert => jordanContinuous q.1 q.2) ∘ (fun p => (f p, g p))) =
      (fun p => jordan (f p) (g p)) := funext fun _ => rfl
  rwa [hfun] at hd

private theorem diff_U {f g : NativeTriple → Albert}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun p => U (f p) (g p)) := by
  have hd := ((diff_J hf (diff_J hf hg)).const_smul (2 : ℝ)).sub (diff_J (diff_J hf hf) hg)
  have hfun : ((2 : ℝ) • (fun p : NativeTriple => jordan (f p) (jordan (f p) (g p))) -
      (fun p => jordan (jordan (f p) (f p)) (g p))) = (fun p => U (f p) (g p)) :=
    funext fun _ => rfl
  rwa [hfun] at hd

private theorem differentiable_phiTriple : Differentiable ℝ phiTriple := by
  have hx : Differentiable ℝ (fun p : NativeTriple => p.1) := differentiable_fst
  have hy : Differentiable ℝ (fun p : NativeTriple => p.2.1) := differentiable_snd.fst
  have hz : Differentiable ℝ (fun p : NativeTriple => p.2.2) := differentiable_snd.snd
  have hd := nativeInnerContinuous.isBoundedBilinearMap.differentiable.comp
    (((diff_U hx (diff_U hy hz)).sub (diff_U hy (diff_U hx hz))).prodMk
      (diff_U hz (diff_J hx hy)))
  have hfun : ((fun q : Albert × Albert => nativeInnerContinuous q.1 q.2) ∘
      (fun p : NativeTriple => (U p.1 (U p.2.1 p.2.2) - U p.2.1 (U p.1 p.2.2), U p.2.2 (jordan p.1 p.2.1)))) =
      phiTriple := funext fun _ => rfl
  simp only [Pi.sub_apply] at hd
  rwa [hfun] at hd

section StableFullDerivative
set_option backward.isDefEq.respectTransparency false
attribute [local instance 20000] Glennie.nativeRealSMulComm Glennie.nativeRealContinuousAdd Glennie.nativeRealContinuousSMul
def fullDerivative (x y z : Albert) : NativeTriple →L[ℝ] ℝ :=
  (nativeInnerContinuous (glennieVector y z x)).coprod
    ((nativeInnerContinuous (glennieVector z x y)).coprod
      (nativeInnerContinuous (glennieVector x y z)))
end StableFullDerivative

theorem hasFDerivAt_phiTriple (x y z : Albert) :
    HasFDerivAt phiTriple (fullDerivative x y z) (x, y, z) := by
  let D : NativeTriple →L[ℝ] ℝ := fderiv ℝ phiTriple (x, y, z)
  have hd : HasFDerivAt phiTriple D (x, y, z) := (differentiable_phiTriple (x, y, z)).hasFDerivAt
  have hx : HasFDerivAt (fun w : Albert => phi w y z) (D.comp (.inl ℝ Albert (Albert × Albert))) x := by
    simpa only [Function.comp_def, phiTriple] using hd.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (y, z))
  have hyz : HasFDerivAt (fun q : Albert × Albert => phi x q.1 q.2)
      (D.comp (.inr ℝ Albert (Albert × Albert))) (y, z) := by
    simpa only [Function.comp_def, phiTriple] using hd.comp (y, z) (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (y, z))
  have hy : HasFDerivAt (fun w : Albert => phi x w z)
      ((D.comp (.inr ℝ Albert (Albert × Albert))).comp (.inl ℝ Albert Albert)) y := by
    simpa only [Function.comp_def] using hyz.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y z)
  have hz : HasFDerivAt (fun w : Albert => phi x y w)
      ((D.comp (.inr ℝ Albert (Albert × Albert))).comp (.inr ℝ Albert Albert)) z := by
    simpa only [Function.comp_def] using hyz.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) y z)
  have h1 := hx.unique (hasFDerivAt_phi_first x y z)
  have h2 := hy.unique (hasFDerivAt_phi_second x y z)
  have h3 := hz.unique (hasFDerivAt_phi_third x y z)
  have hfull : D = fullDerivative x y z := by
    rw [← ContinuousLinearMap.coprod_comp_inl_inr D,
      ← ContinuousLinearMap.coprod_comp_inl_inr (D.comp (.inr ℝ Albert (Albert × Albert))),
      h1, h2, h3]
    rfl
  exact hd.congr_fderiv hfull

theorem eq_top_of_fderiv_phiTriple_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hd : fderiv ℝ phiTriple (x, y, z) ≠ 0) : K = ⊤ := by
  by_contra hK
  apply hd
  rw [(hasFDerivAt_phiTriple x y z).fderiv, fullDerivative,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK y z x hy hz hx,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK z x y hz hx hy,
    glennieVector_eq_zero_of_ne_top K h1 hJ hK x y z hx hy hz]
  apply ContinuousLinearMap.ext; rintro ⟨a, b, c⟩
  simp only [ContinuousLinearMap.coprod_apply, pairingContinuous_apply, inner_zero_left, add_zero, zero_apply]

end
end Glennie.Compact.GlennieFullDerivativeR01
