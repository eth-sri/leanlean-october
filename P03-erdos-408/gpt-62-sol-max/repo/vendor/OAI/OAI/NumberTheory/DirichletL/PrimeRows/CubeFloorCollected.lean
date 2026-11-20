module

public import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobal
public import OAI.NumberTheory.DirichletL.Detector.CentralExponent
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows
public import OAI.NumberTheory.DirichletL.Detector.Scales

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeRaySlots
open HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_floor_rows_saving (N n : ℕ) (sc : FloorDetectorScales)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*sc.e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,sc.dmax*sc.rmin≤ell j) (hellhi : ∀j,ell j≤sc.dmin*sc.R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo sc.c sc.b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤sc.A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (mw : MellinWindows)
    (hr0 : ∀y,(mw.left y).im=0) (hr1 : ∀y,(mw.right y).im=0)
    (hp0 : ∀y,0≤(mw.left y).re) (hp1 : ∀y,0≤(mw.right y).re) (hn0 : mw.left≠0) (hn1 : mw.right≠0)
    (nu : ℝ) (hnu : 0<nu)
    (ζ saving : ℝ) (hζ : 0≤ζ) (hζhi : ζ≤3/16) (hsaving : 0<saving)
    (htotal : 2*ζ+26*sc.e+(N+8)*sc.eps+sc.loss+sc.mesh/6+nu+saving≤7/1200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,sc.dmin≤d → d≤sc.dmax → ∀(v : ℝ),0≤v → v≤13/16+ζ → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^sc.δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-sc.margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀idx : FreeRow→ℕ,(∀u∈rows,idx u≤n) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^sc.τ)<51/100+2*sc.e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant mw.left mw.right (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Yp) (fun j y=>(W j y:ℂ)) Yp
        mw.left mw.right (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*sc.eps)*
          Z^(3/16-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo sc.c sc.b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤sc.A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨Ca,hCa,hArith⟩ := actual_global_floor_cube_arithmetic M H hH N n sc
    S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm mw
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (sc.hdmin.trans_le sc.hdRange) sc.hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS sc.c sc.b sc.hc sc.hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne mw
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  let C := Cp*Ca*Cn
  refine ⟨(n+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hArith η, hnormer, source_cube_height_eventually sc.τ sc.hτ] with Z hb hn hz
  intro d hd hd' v hv hvhi rows hrows hnorm idx hidx hbin
  dsimp only
  let Yp : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Yp j)
  let hT := poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Yp
  let normer := PrincipalMellinResidues.sourceResidueConstant mw.left mw.right (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
  let Ri : ℕ→Finset FreeRow := fun i=>rows.filter (fun u=>idx u=i)
  have hZp : 0 < Z := zero_lt_one.trans_le hz.1
  refine ⟨hn.1,?_⟩
  have hpart := finiteCentralCubeRows_bin_partition S hS hmax η rows T hT WC Yp mw.left mw.right
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (Z^sc.τ) idx (fun _=>0) n 0 (fun u hu=>⟨hidx u hu,le_rfl⟩)
  have heq : finiteCentralCubeRows S hS hmax η rows T hT WC Yp mw.left mw.right
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ)=
      ∑i∈Finset.range (n+1),finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp mw.left mw.right
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^sc.τ) := by
    simpa [cubeBinRows,Ri] using hpart
  change ‖finiteCentralCubeRows S hS hmax η rows T hT WC Yp mw.left mw.right
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ)/normer‖≤_
  rw [heq,Finset.sum_div]
  apply (norm_sum_le _ _).trans
  have hboundi (i : ℕ) (hi : i∈Finset.range (n+1)) :
      ‖finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp mw.left mw.right
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^sc.τ)/normer‖≤
      C*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^(3/16-saving) := by
    have hsub : Ri i⊆rows := Finset.filter_subset _ _
    have hbi : ∀u∈Ri i,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^sc.τ)<51/100+2*sc.e := by
      intro u hu
      have hh := hbin u (hsub hu)
      rwa [(Finset.mem_filter.mp hu).2] at hh
    have hsteps : (3*i+1:ℕ)*Z^sc.τ≤(3*i+2:ℕ)*Z^sc.τ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
      exact_mod_cast (show 3*i+1≤3*i+2 by omega)
    let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^(v*(67/100+12*sc.e+sc.eps*(N+8))+sc.loss-1/40+sc.mesh/6)
    have hp := hprofile sc.e (51/100) (Z^sc.τ) ((3*i+1:ℕ)*Z^sc.τ) i sc.he sc.he1 le_rfl (by norm_num)
      hz.2 hsteps S hS hmax hfirst η (Ri i) (fun u hu=>(hrows u (hsub hu)).1) T
      (poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Yp) (rayCubeFamily M H hH) hbi WC Yp
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
      (hb d hd hd' v hv (Ri i) (fun u hu=>hrows u (hsub hu))
        (fun u hu=>hnorm u (hsub hu)) i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hbi)
    rw [div_eq_mul_inv,norm_mul]
    have hterm := mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    rw [ProbeCentralExponent.physical_scale_identity Z (51/100) sc.e hZp] at hterm
    have hpow : Z^((25/48)*(51/100)-181/300+(105/8)*sc.e) *
        Z^(v*(67/100+12*sc.e+sc.eps*(N+8))+sc.loss-1/40+sc.mesh/6) * Z^nu ≤
        Z^(3/16-saving) := by
      rw [← Real.rpow_add hZp, ← Real.rpow_add hZp]
      apply Real.rpow_le_rpow_of_exponent_le hz.1
      have hm := ProbeCentralExponent.floor_source_margin (1/100) 0 ζ v le_rfl hζ hvhi
      have hl := ProbeCentralExponent.realLoss_bound N v sc.e sc.eps sc.loss sc.mesh
        (by linarith) sc.he.le sc.heps.le
      change _ + _ + nu ≤ _
      have hexp : ((25/48:ℝ)*(51/100)-181/300+(105/8)*sc.e)+
          (v*(67/100+12*sc.e+sc.eps*(N+8))+sc.loss-1/40+sc.mesh/6) =
          ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
            ProbeCentralExponent.realLoss N v sc.e sc.eps sc.loss sc.mesh := by
        unfold ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
        ring
      rw [hexp]
      linarith
    apply hterm.trans
    dsimp only [mass,C]
    calc
      _ = (Cp*Ca*Cn)*(η.modulus.absNorm:ℝ)^(2*sc.eps)*
        (Z^((25/48)*(51/100)-181/300+(105/8)*sc.e)*
          Z^(v*(67/100+12*sc.e+sc.eps*(N+8))+sc.loss-1/40+sc.mesh/6)*Z^nu) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑i∈Finset.range (n+1),C*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^(3/16-saving) := Finset.sum_le_sum hboundi
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
