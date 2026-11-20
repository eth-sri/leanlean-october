module
public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorClass
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorIntegral
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorNormalized
public import OAI.NumberTheory.DirichletL.PrimeRows.ProbeFrames

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily (WithProbeScales WithProbeScaleMargins WithPositiveProbeSlots WithPositiveResidueTests WithAssemblyMargins)
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ) :
    WithProbeScales e eps c b A R dmin dmax rmin τ ε κ cost mesh (fun _ =>
    WithProbeScaleMargins e R dmin rmin τ ε κ cost mesh margin eps loss (
    ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal), WithPositiveProbeSlots N dmin dmax rmin R c b A (fun ell W =>
    WithAssemblyMargins dmin dmax τ ε e κ cost (
    ∀ (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640), WithPositiveResidueTests (fun W0 W1 a0 b0 a1 b1 =>
    ∀ (nu : ℝ) (hnu : 0<nu) (counts : CountParameters M H εm), letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu)))))) := by
  intro he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hbudget hgap hmargin hheight
    hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum hdtop hε1 hκ1 hτzero
    hτheight hwbudget φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm Δ ν logCost heightCost momentCost
    hεm hΔ hΔ1 hν hlog hMomentHeight ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0
    hr1 hp0 hp1 hn0 hn1 nu hnu counts
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hdmax0 : 0<dmax := hdmin.trans_le hdRange
  obtain ⟨K,hK,hcounts⟩ :=
    adaptive_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨Ca,hCa,hphysical⟩ := actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  let Cclass := Ca*K
  have hCclass : 0 < Cclass := mul_pos hCa hK
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0 ≤ cardCost := by dsimp [cardCost]; positivity
  let Ccube := D*((cardCost+1)*Cclass)
  have hCcube : 0 < Ccube := by dsimp [Ccube]; positivity
  refine ⟨Ccube*Cn,mul_pos hCcube hCn,?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcounts,hbatches,hnormer,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hphysical hcounts hbatch hn hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1,?_⟩
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let bound : ℝ := Cclass*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))
  have hb : 0 ≤ bound := by dsimp [bound]; positivity
  have hcube := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le ha' hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext WC Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp ((cardCost+1)*bound) (by positivity)
    (by
      intro t ht
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q := physical M H (fun u : FreeRow=>u.val) WC (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
      have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
        (nonfloorPoolOutside M H S N c b Y) WC Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
        (by linarith) (fun j=>ell j/d) Q bound hb (by
          intro bin hne
          let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
          let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
          have hsub : rows'⊆rows := Finset.filter_subset _ _
          have hrowne : rows.Nonempty := hne.mono hsub
          have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
            intro u hu
            exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
          obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
            hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
              (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
              N ell hellpos hellhi hellsum WC (fun _=>b) (fun _=>z) bin hne
          have hBsub : B.rows⊆rows := hBr ▸ hsub
          have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
            intro u hu j
            exact hFam u (hBr ▸ hu) j
          have hraw := hmom t ht q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
          have hrowCard := hcounts d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
            (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
          rw [hBr,hMesh] at hrowCard
          have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=>ell j/d) Q bin
            (by linarith) (fun j _=>div_nonneg (hellpos j).le hd0.le)
            (by rw [source_slot_length_sum Finset.univ ell d hellsum];positivity) hne
          have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
            (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
            (fun u hu=>hrows u (hsub hu)) (fun u hu=>hnorm u (hsub hu)) hrowCard i hi
            (fun u hu=>hnext u (hsub hu)) t ht
            (fun u hu=>source_amplitude_class_mean M H ell WC Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
          have hs := adaptive_mixed_saving N a q Δ ε εm R ν ζ μ v d e eps loss mesh
            (logCost+heightCost+momentCost) saving (by linarith) ha' hqb.1 hqb.2 hΔ hΔ1 hε.le hεm.le
            hR hν.le hcount hζ hζ1 hv' hμ hdv he.le heps.le hfinal
          have hid := central_class_exponent_identity N a v d
            (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) q e eps loss mesh (logCost+heightCost+momentCost)
          let x := d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6
          refine hp.trans ?_
          change Ca*(K*C0*Z^(logCost+heightCost+momentCost))*(η.modulus.absNorm:ℝ)^(2*eps)*Z^x ≤ bound
          dsimp only [bound]
          calc
            _ = Cclass*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(logCost+heightCost+momentCost+x) := by
              rw [Real.rpow_add hZp (logCost+heightCost+momentCost) x]; dsimp [Cclass]; ring
            _ ≤ _ := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.rpow_le_rpow_of_exponent_le hZ.le
              dsimp only [x]
              linarith)
      simp only [Finset.card_univ,Fintype.card_fin] at hpart
      exact hpart.trans (mul_le_mul_of_nonneg_right (by linarith) hb))
  have hh : ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) WC Y
      W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖ ≤
      Ccube*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving) := by
    refine hcube.trans_eq ?_
    rw [ProbeCentralExponent.physical_scale_identity Z a e hZp]
    dsimp only [bound, Ccube]
    calc
      _ = (D*((cardCost+1)*Cclass))*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          (Z^((25/48)*a-181/300+(105/8)*e)*Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))) := by
        ring
      _ = _ := by rw [←Real.rpow_add hZp]; congr 2 <;> ring
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZp (3/16+Δ-saving) nu]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
