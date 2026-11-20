module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorTransport
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows
public import OAI.NumberTheory.DirichletL.Detector.Scales
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyClass
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual

local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

set_option maxHeartbeats 1200000 in
theorem actual_high_probe_from_raw_moments (N : ℕ) (sc : DetectorScales)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*sc.e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,sc.dmax*sc.rmin≤ell j) (hellhi : ∀j,ell j≤sc.dmin*sc.R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo sc.c sc.b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤sc.A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : sc.dmax≤37/42) (hε1 : sc.ε≤1/1000) (hκ1 : sc.κ≤1)
    (hτzero : sc.τ<sc.dmin/2) (hτheight : 4*sc.τ<sc.dmin*sc.cost)
    (hwbudget : 12*sc.e*((22:ℝ)+2)+8*sc.κ+2*sc.cost≤sc.ε/2)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : sc.τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*sc.ε+εm+sc.R+7*ν≤1/32)
    (hfinal : (13/16)*(159*sc.ε+εm+sc.R+7*ν)+2*ζ+(3/2)*μ+
      (26*sc.e+(N+8)*sc.eps+sc.loss+sc.mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (mw : MellinWindows)
    (hr0 : ∀y,(mw.left y).im=0) (hr1 : ∀y,(mw.right y).im=0)
    (hp0 : ∀y,0≤(mw.left y).re) (hp1 : ∀y,0≤(mw.right y).re) (hn0 : mw.left≠0) (hn1 : mw.right≠0)
    (nu : ℝ) (hnu : 0<nu)
    (dyadCost : ℝ) (hdyadCost : 0<dyadCost)
    (hdmin1 : sc.dmin<1/100) (hconductor : 13/16+ζ+2*sc.margin≤sc.dmax)
    (hmuMargin : 2*sc.margin≤μ)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0<sigma)
    (hgeometric : sigma+8*sc.e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+sc.e≤(7/8)*(sc.dmax*sc.rmin))
    (hfloorbudget : 2*ζ+26*sc.e+(N+8)*sc.eps+sc.loss+sc.mesh/6+nu+sigma≤7/1200)
    (hcentral : sigma+nu+dyadCost≤saving) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∃C : ℝ,
      0<C ∧
    ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Yp j)
      let _hT := poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant mw.left mw.right (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      ∃idx grid : FreeRow→ℕ,
      (∀ u, CubeBin (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (Z^sc.τ) sc.e n (idx u) (grid u)) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤C0 →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/sc.e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^sc.τ ∧ |t.2|≤(3*i+1:ℕ)*Z^sc.τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^sc.τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z sc.margin k) (51/100+sc.e*j) sc.ε sc.τ sc.dmax sc.b sc.R sc.mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (HeckeZeroSupremum.beta-7/8)
          (if 2*(51/100+sc.e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+sc.e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) mw.left mw.right
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*sc.eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0<sc.dmax*sc.rmin := mul_pos (sc.hdmin.trans_le sc.hdRange) sc.hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N sc.e (1/4) sc.c sc.b sc.A ζ 1 sc.τ (sc.dmax*sc.rmin) nu
    sc.he sc.he1 (by norm_num) (by norm_num) hζ hζ1 sc.hτ sc.hc sc.hcb sc.hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne mw
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith)
    sc.eps sc.R sc.dmin sc.dmax sc.rmin sc.ε sc.κ sc.cost sc.mesh sc.margin sc.loss sc.heps sc.hR sc.hdmin sc.hdmax sc.hdRange sc.hrmin sc.hε sc.hκ sc.hcost sc.hmesh sc.hmargin
    sc.hbudget sc.hgap sc.hheight sc.hloss (by linarith [sc.hmargin]) hello hellhi hfloorbudget
  have hΔ : 0≤HeckeZeroSupremum.beta-7/8 := by linarith
  have hΔ1 : HeckeZeroSupremum.beta-7/8≤1/8 := by linarith [HeckeZeroSupremum.beta_le_one]
  let Δ := HeckeZeroSupremum.beta-7/8
  let m := ⌊(49/100:ℝ)/sc.e⌋₊
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo sc.c sc.b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤sc.A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨C,hC,hclass⟩ :=
    actual_nonfloor_class_from_raw_moments M H hH N n sc S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      εm Δ ν logCost heightCost momentCost hΔ hΔ1 hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound sc.mesh:ℝ)^N
  have hcardCost : 0≤cardCost := by dsimp [cardCost];positivity
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm mw
  have hellpos (j : Fin N) : 0<ell j := (mul_pos (sc.hdmin.trans_le sc.hdRange) sc.hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS sc.c sc.b sc.hc sc.hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne mw
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  let B := Cp*((cardCost+1)*C)*Cn
  have hB : 0 < B := by dsimp [B]; positivity
  let Ctot := Cd*(n+1:ℕ)*(m+1:ℕ)*B
  refine ⟨n,hn,Ctot,by dsimp [Ctot]; positivity,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hclass η,hnormer,(tendsto_rpow_atTop sc.hτ).eventually (eventually_gt_atTop (2:ℝ)),
    sourceDyad_geometry_eventually sc.dmin sc.dmax sc.margin (13/16+ζ) hdmin1 sc.hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z ht hclass hn hτlarge hg hZ
  dsimp only at ht ⊢
  obtain ⟨idx,grid,hbins,herror⟩ := ht
  refine ⟨idx,grid,hbins,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/sc.e⌋₊ ∧ grid u≠0 ∧ 51/100+sc.e*grid u≤1 := by
    intro u hu
    exact ⟨(hbins u).height_index,(hbins u).grid_index,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).alpha_le_one⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^sc.τ)<51/100+sc.e*grid u+2*sc.e := fun u _=>(hbins u).next
  have hcurrent : ∀u∈rows,51/100+sc.e*grid u≤detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^sc.τ) := fun u _ => (hbins u).lower
  dsimp only at hn
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Y j)
  let hT := poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y
  let normer := PrincipalMellinResidues.sourceResidueConstant mw.left mw.right (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := B*C0*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^(3/16+Δ-saving+nu)
  have hD : 0≤D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun rr a H=>
    finiteCentralCubeRows S hS hmax η rr T hT WC Y mw.left mw.right
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(13/16+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+sc.e*j) (fun _=>(3*i+1:ℕ)*Z^sc.τ)/normer‖≤D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabel u (hsub hu)).2.2.1
      have ha : 51/100<51/100+sc.e*j := by
        have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith [mul_pos sc.he hjp]
      have ha' : 51/100+sc.e*j≤1 := by simpa only [huj] using (hlabel u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^sc.τ)<51/100+sc.e*j+2*sc.e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+sc.e*j≤detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^sc.τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      let d := sourceDyadConductor Z sc.margin k
      let v := sourceDyadExponent Z k
      let a := 51/100+sc.e*j
      have ha0 : 51/100 < a := ha
      have hdv : d-v≤μ := by change sourceDyadConductor Z sc.margin k-v≤μ; unfold sourceDyadConductor; dsimp [v]; linarith
      have hrows' (u : FreeRow) (hu : u∈Rij) :=
        And.intro (hrows u (hsub hu)).1 (And.intro (hrows u (hsub hu)).2.1
          (And.intro (hrows u (hsub hu)).2.2.1 (hgeo.2.2.2.2.2 u (hsubk hu))))
      have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      let shift := (25/48)*a-181/300+(105/8)*sc.e
      let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^(3/16+Δ-saving-shift)
      let amp := (cardCost+1)*bound
      have hb : 0≤bound := by dsimp [bound]; positivity
      have hamp : 0≤amp := by dsimp [amp]; positivity
      have hp := hprofile sc.e a (Z^sc.τ) ((3*i+1:ℕ)*Z^sc.τ) i sc.he sc.he1 ha.le ha' hτlarge
        (by gcongr; omega) S hS hmax hfirst η Rij (fun u hu=>(hrows' u hu).1)
        T hT (rayCubeFamily M H hH) hnext' WC Y
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp amp hamp (by
          intro t ht
          let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
          let Q := physical M H (fun u : FreeRow=>u.val) WC (fun _=>sc.b) (fun j=>ell j/d) (fun _=>z) (Z^d)
          have hpart := cubeArithmeticSum_class_uniform S hS hmax η Rij T hT WC Y a sc.e t Finset.univ
            (Z^d) ((2*a-1)/2) sc.mesh sc.hmesh (by dsimp only [a]; linarith only [ha']) (fun j=>ell j/d) Q bound hb (by
            intro bin hne
            have hp := hclass d hgeo.2.2.1 hgeo.2.2.2.1 v a C0 hgeo.1 ha ha' hC0 Rij hrows'
              (fun u hu=>hgeo.2.2.2.2.1 u (hsubk hu)) i hi' hnext' hcurrent' t ht
              (hmom k hk i hi j hj ⟨u,hu⟩ t ht) bin hne
            dsimp only at hp
            let q := classMean Finset.univ ((2*a-1)/2) sc.mesh (fun j=>ell j/d) bin
            have hs := adaptive_mixed_saving N a q Δ sc.ε εm sc.R ν ζ μ v d sc.e sc.eps sc.loss sc.mesh
              (logCost+heightCost+momentCost) saving (by linarith) ha' hp.1 hp.2.1 hΔ hΔ1 sc.hε.le hεm.le
              sc.hR hν.le hcount hζ.le (by linarith) hgeo.2.1 hμ hdv sc.he.le sc.heps.le hfinal
            have hid := central_class_exponent_identity N a v d
              (adaptiveRowExponent (2*a-1) q Δ sc.ε εm sc.R ν) q sc.e sc.eps sc.loss sc.mesh (logCost+heightCost+momentCost)
            apply hp.2.2.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (by positivity))
            dsimp only [bound,shift]
            linarith)
          simp only [Finset.card_univ,Fintype.card_fin] at hpart
          exact hpart.trans (mul_le_mul_of_nonneg_right (by linarith) hb))
      rw [div_eq_mul_inv,norm_mul]
      apply (mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)).trans_eq
      rw [ProbeCentralExponent.physical_scale_identity Z a sc.e hZp]
      have hexp : Z^shift * Z^(3/16+Δ-saving-shift) * Z^nu = Z^(3/16+Δ-saving+nu) := by
        rw [← Real.rpow_add hZp, ← Real.rpow_add hZp]
        congr 1
        ring
      change Cp*Z^shift*amp*(Cn*Z^nu) = D
      dsimp only [amp,bound,D,B]
      linear_combination Cp*((cardCost+1)*C)*Cn*C0*(η.modulus.absNorm:ℝ)^(2*sc.eps)*hexp
    · have hRij : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from hRij,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+sc.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ)=
      ∑k∈smallDyadicIndices (Z^(13/16+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+sc.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  have hglobal : ‖F rows (fun u=>51/100+sc.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ)/normer‖ ≤
      Ctot*C0*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^(3/16+Δ-saving+nu+dyadCost) := by
    rw [hpartition,Finset.sum_div]
    calc
      _ ≤ ∑k∈smallDyadicIndices (Z^(13/16+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
          mw.left mw.right (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z sc.e (Z^sc.τ) idx grid n m
          (fun u hu=>⟨(hlabel u (Finset.mem_inter.mp hu).1).1,(hlabel u (Finset.mem_inter.mp hu).1).2.1⟩)
        change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+sc.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^sc.τ)/normer‖≤_
        dsimp only [F]
        rw [hpart,Finset.sum_div]
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.sum_div]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=>hcell k hk i hi j hj))
          _ = _ := by simp;ring
      _ = ((smallDyadicIndices (Z^(13/16+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
      _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
        mul_le_mul_of_nonneg_right (hdyad Z (13/16+ζ) hZ.le (by linarith)) (by positivity)
      _ = _ := by dsimp [Ctot,D];rw [Real.rpow_add hZp (3/16+Δ-saving+nu) dyadCost];ring
  have hexp : Z^(3/16+(HeckeZeroSupremum.beta-7/8)-saving+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [F,normer,WC,Y,T,hT,rows,sub_add_cancel,add_mul] using hsum

end SevenEighths.ProbeFinalAssembly

end

end OAI
