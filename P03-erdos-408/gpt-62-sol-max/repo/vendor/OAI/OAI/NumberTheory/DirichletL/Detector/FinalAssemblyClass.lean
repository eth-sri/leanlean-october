module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount
public import OAI.NumberTheory.DirichletL.Detector.Scales

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_class_from_raw_moments (N n : ℕ) (sc : DetectorScales)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*sc.e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,sc.dmax*sc.rmin≤ell j) (hellhi : ∀j,ell j≤sc.dmin*sc.R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo sc.c sc.b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤sc.A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : sc.dmax≤37/42) (hε1 : sc.ε≤1/1000) (hκ1 : sc.κ≤1)
    (hτzero : sc.τ<sc.dmin/2) (hτheight : 4*sc.τ<sc.dmin*sc.cost)
    (hwbudget : 12*sc.e*((22:ℝ)+2)+8*sc.κ+2*sc.cost≤sc.ε/2)
    (εm Δ ν logCost heightCost momentCost : ℝ)
 (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : sc.τ<heightCost) (counts : CountParameters M H εm) :
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,sc.dmin≤d → d≤sc.dmax → ∀(v a C0 : ℝ),0≤v → 51/100<a → a≤1 → 0≤C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-sc.margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^sc.τ)<a+2*sc.e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^sc.τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^sc.τ ∧ |t.2|≤(3*i+1:ℕ)*Z^sc.τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^sc.τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a sc.ε sc.τ sc.dmax sc.b sc.R sc.mesh i z Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>sc.b) (fun j=>ell j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) sc.mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) sc.mesh sc.hmesh (fun j=>ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) sc.mesh (fun j=>ell j/d) bin
      rows'.Nonempty → 0≤q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y) W Y a sc.e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*sc.eps)*
          Z^(logCost+heightCost+momentCost+
            d*adaptiveRowExponent (2*a-1) q Δ sc.ε εm sc.R ν+
            v*(a-1/2+12*sc.e+sc.eps*(N+8)-17/50)+sc.loss-2/75+q/6+sc.mesh/6) := by
  have hdmax0 : 0<sc.dmax := sc.hdmin.trans_le sc.hdRange
  obtain ⟨K,hK,hcount⟩ :=
    adaptive_source_count_from_raw_moments M H
      (Sum Bool (RayQuotient.Characters M H)) N n sc.dmin sc.dmax sc.τ logCost heightCost momentCost sc.mesh
      sc.hdmin hdmax0 sc.hτ hlog hMomentHeight sc.hmesh counts
  obtain ⟨C,hC,hphysical⟩ := actual_class_cube_arithmetic M H hH N n ⟨⟨sc.e, sc.eps, sc.c, sc.b, sc.A, sc.R, sc.dmin, sc.dmax, sc.rmin, sc.τ, sc.ε, sc.κ, sc.cost, sc.mesh, sc.margin, sc.loss,
      sc.he, sc.he1, sc.heps, sc.hc, sc.hcb, sc.hA, sc.hR, sc.hdmin, sc.hdmax, sc.hdRange, sc.hrmin, sc.hτ, sc.hε, sc.hκ, sc.hcost, sc.hmesh, sc.hbudget, sc.hgap, sc.hmargin, sc.hheight, sc.hloss⟩, (1/100), (by norm_num)⟩ S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches M H hH S hS hmax η
    sc.dmin sc.dmax sc.τ sc.ε sc.e sc.κ sc.cost sc.margin sc.R sc.mesh n sc.hdmin sc.hdRange hdtop sc.hτ hτzero hτheight
    sc.hε sc.he sc.he1 sc.hκ hκ1 sc.hcost sc.hmargin sc.hR sc.hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := sc.hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>sc.b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) sc.mesh sc.hmesh (fun j=>ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) sc.mesh (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0<ell j := (mul_pos hdmax0 sc.hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi hellsum W (fun _=>sc.b) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a sc.ε Δ ν C0 q i hi ha ha' sc.hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) sc.mesh sc.hmesh (fun j=>ell j/d) Q bin
    (by linarith) (fun j _=>div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum Finset.univ ell d hellsum];positivity) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (adaptiveRowExponent (2*a-1) q Δ sc.ε εm sc.R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=>hrows u (hsub hu)) (fun u hu=>hnorm u (hsub hu)) hcard i hi
    (fun u hu=>hnext u (hsub hu)) t ht
    (fun u hu=>source_amplitude_class_mean M H ell W Z d sc.b a sc.mesh z hZp hd0.ne' sc.hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*adaptiveRowExponent (2*a-1) q Δ sc.ε εm sc.R ν+
      v*(a-1/2+12*sc.e+sc.eps*(N+8)-17/50)+sc.loss-2/75+q/6+sc.mesh/6=
      (logCost+heightCost+momentCost)+(d*adaptiveRowExponent (2*a-1) q Δ sc.ε εm sc.R ν+
      v*(a-1/2+12*sc.e+sc.eps*(N+8)-17/50)+sc.loss-2/75+q/6+sc.mesh/6) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
