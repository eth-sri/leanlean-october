module

public import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows
public import OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorCollected

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

private lemma normalized_central_transport (A P C F N : ℂ) (a b v : ℝ)
    (ha : ‖A-P-C‖≤a) (hb : ‖P/N-F‖≤b) (hv : ‖N⁻¹‖≤v) (ha0 : 0≤a) :
    ‖A/N-F-C/N‖≤a*v+b := by
  calc
    _ = ‖(A-P-C)*N⁻¹+(P/N-F)‖ := by congr 1;simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-P-C)*N⁻¹‖+‖P/N-F‖ := norm_add_le _ _
    _ ≤ a*v+b := by rw [norm_mul];gcongr

set_option maxHeartbeats 600000 in
theorem actual_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (mw : MellinWindows)
    (hr0 : ∀y,(mw.left y).im=0) (hr1 : ∀y,(mw.right y).im=0)
    (hp0 : ∀y,0≤(mw.left y).re) (hp1 : ∀y,0≤(mw.right y).re) (hn0 : mw.left≠0) (hn1 : mw.right≠0)
    (sigma : ℝ) (hsigma : 0<sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*ellMin) (hlarge : sigma+nu≤saving+3/16)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0<eps) (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax)
    (hrmin : 0<rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hmargin : 0<margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε<rmin*mesh)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (hcap : 13/16+ζ≤dmax-margin)
    (helllo : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hfloorbudget : 2*ζ+26*e+(K+8)*eps+loss+mesh/6+nu+sigma≤7/1200) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := poolOutside (RayQuotient.identityClass M H) S a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant mw.left mw.right (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      ∃idx grid : FreeRow→ℕ,
      (∀ u, CubeBin (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (Z^τ) e n (idx u) (grid u)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) mw.left mw.right
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid) T hT WC Yp
          mw.left mw.right (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := canonical_probe_exists_ray_cube M H hH K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha (ha.trans_le hab) hB hβ S hS hmax hfirst mw
  obtain ⟨Cn,hCn,hnormalizer⟩ := actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    (fun j=>hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    mw hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  have hflo := actual_floor_rows_saving M H hH K n ⟨⟨e, eps, a, b, B, R, dmin, dmax, rmin, τ, ε, κ, cost, mesh, margin, loss,
      he, he', heps, ha, hab, hB, hR, hdmin, hdmax, hdRange, hrmin, hτ, hε, hκ, hcost, hmesh, hphasebudget, hphasegap, hmargin, hheight, hloss⟩, (1/100), (by norm_num)⟩ S hS hfirst hmax ell hellinj helllo hellhi
    W hsupp hW hWB hcompact hne hellsum mw hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu ζ sigma hζ.le (by linarith) hsigma hfloorbudget
  obtain ⟨Cf,hCf,hfloor⟩ := hflo
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hcmp⟩ := ProbePrincipalNormalized.actual_ray_principal_comparison M H hH η S hS
    a b B ellMin ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    mw hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by linarith) (by linarith)
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0≤D := by dsimp [D];positivity
  let Ct := 4*(D+Cp)
  let C := Ct+Cf*(η.modulus.absNorm:ℝ)^(2*eps)
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hcanonical,hnormalizer,hcmp,hfloor η,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_ge_atTop (1:ℝ)] with Z hcan hnorm hcmp hf hdis hZ1
  have hZ : 0<Z := by linarith
  dsimp only at hnorm hcmp ⊢
  let Yp : Fin K→ℝ := fun j=>Z^(ell j)
  let T : Fin K→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := poolOutside (RayQuotient.identityClass M H) S a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ)≤b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hbins,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  refine ⟨idx,grid,hbins,?_⟩
  have hh := normalized_central_transport _ _ _ _ _ _ _ _ herror hcmp.2 hnorm.2 (by positivity)
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ (HeckeZeroSupremum.beta-11/16-63/800+8*e) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq] at hh
  have h1 : D≤D+Cp := by linarith
  have h2 : Cp≤D+Cp := by linarith
  let c := HeckeZeroSupremum.beta-11/16-sigma
  have hp {x : ℝ} (h : x≤c) : Z^x≤Z^c := Real.rpow_le_rpow_of_exponent_le hZ1 h
  have h3 := hp (show HeckeZeroSupremum.beta-11/16-63/800+8*e+nu≤c by dsimp [c]; linarith)
  have h4 := hp (show -saving+nu≤c by dsimp [c]; linarith)
  have h5 := hp (show HeckeZeroSupremum.beta-11/16-17/48000+nu≤c by dsimp [c]; linarith)
  have h6 := hp (show HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin≤c by dsimp [c]; linarith)
  have hsave : D*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)+Z^(-saving+nu))+
      Cp*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) ≤ Ct*Z^c := by
    calc
      _ ≤ (D+Cp)*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)+Z^(-saving+nu))+
        (D+Cp)*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
        gcongr
      _ ≤ (D+Cp)*(4*Z^c) := by rw [← mul_add]; gcongr; linarith
      _ = _ := by dsimp [Ct]; ring
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  let floors := supportedFloorRows S hmax rows grid
  have hrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(dmax-margin) := by
    intro u hu
    rcases (mem_supportedFloorRows S hmax rows grid u).mp hu with ⟨hur,hcal,hg⟩
    have hm := mem_rowBand.mp hur
    exact ⟨hm.1,hm.2.1,hcal,hm.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hZ1 hcap)⟩
  have hnorms : ∀u∈floors,rowNorm u≤Z^((13/16:ℝ)+ζ) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows S hmax rows grid u).mp hu).1).2.2.le
  have hfloorbin : ∀u∈floors,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e := by
    intro u hu
    have hg := ((mem_supportedFloorRows S hmax rows grid u).mp hu).2.2
    have hh := (hbins u).next
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hh
  have hb := (hf dmax hdRange le_rfl (13/16+ζ) (by linarith) le_rfl floors hrows hnorms idx
    (fun u hu=>(hbins u).height_index) hfloorbin).2
  have hsplit := finiteCentralCubeRows_supported_split S hS hmax η rows T hT WC Yp mw.left mw.right
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e grid (fun u=>(3*idx u+1:ℕ)*Z^τ)
  rw [hsplit] at hh
  have hh := normalized_nonfloor_error _ _ _ _ _ _ _ (hh.trans hsave) hb
  apply hh.trans
  have hp : Z^(3/16-sigma)≤Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  calc
    _ ≤ Ct*Z^(HeckeZeroSupremum.beta-11/16-sigma)+
      (Cf*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by gcongr
    _ = _ := by dsimp [C];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
