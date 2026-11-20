module
public import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
public import OAI.NumberTheory.DirichletL.Detector.CentralExponent
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
public import OAI.NumberTheory.DirichletL.PrimeRows.ProbeFrames

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_floor_cube_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ) :
    WithProbeScales e eps c b A R dmin dmax rmin τ ε κ cost mesh (fun _ =>
    ∀ (hδ : 0<δ), WithProbeScaleMargins e R dmin rmin τ ε κ cost mesh margin eps loss (
    ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal), WithPositiveProbeSlots N dmin dmax rmin R c b A (fun ell W =>
    WithPositiveResidueTests (fun W0 W1 a0 b0 a1 b1 =>
    ∀ (nu : ℝ) (hnu : 0<nu)
    (ζ saving : ℝ) (hζ : 0≤ζ) (hζhi : ζ≤3/16) (_hsaving : 0<saving)
    (htotal : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+saving≤7/1200), letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → v≤13/16+ζ → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (ProbeHighRowFamily.rayPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(3/16-saving))))) := by
  intro he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin
    hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ζ saving hζ hζhi _hsaving htotal
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
  obtain ⟨C0,hC0,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB
  let α : ℝ := 1/100+12*e+eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  let θ : ℝ := 67/100+12*e+eps*(N+8)
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨Cg,hCg,hgeom⟩ := bounded_dyadic_power_sum θ hθ
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  let C := 256*C0*(AA+1)
  have hC : 0 < C := by dsimp [C]; positivity
  let Ca := C*Cg
  have hCa : 0 < Ca := mul_pos hC hCg
  refine ⟨(Cp*Ca)*Cn,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,source_cube_height_eventually τ hτ,eventually_gt_atTop (1:ℝ)] with Z hb hn hZheight hZ
  intro d hd hd' v hv hvhi rows hrows hnorm i hi hbin
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  have hheight' : (3*i+1:ℕ)*Z^τ≤(3*i+2:ℕ)*Z^τ := by
    gcongr; omega
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*θ+loss-1/40+mesh/6)
  have hp := hprofile e (51/100) (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 le_rfl (by norm_num)
    hZheight.2 hheight' S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T
    (ProbeHighRowFamily.rayPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hbin WC Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
    (by
      intro t ht
      have hZle := hZ.le
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
        (fun j=>ProbeHighRowFamily.rayPoolOutside M H S N c b Y j _ (P j).property) WC Y
        (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
      let D₀ : ℝ := C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-1/40+mesh/6)
      have hD₀ : 0≤D₀ := by dsimp [D₀];positivity
      have hF (u : FreeRow) (hu : u∈rows) : F u≤D₀*rowNorm u^α := by
        rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
        have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
        dsimp only at hh
        let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (WC j) b (Y j) z)
        have hq := weightedMean_bounds Finset.univ (fun j=>ell j/d) g (1/50)
          (fun j _=>div_nonneg (hellpos j).le hd0.le)
          (by rw [source_slot_length_sum _ _ _ hellsum];positivity)
          (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
        have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))≤Z^(-1/40+mesh/6) := by
          rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
            Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+mesh/6) from
            source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
          apply Real.rpow_le_rpow_of_exponent_le hZle
          linarith [hq.2]
        have hN : 0≤rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
        have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
        convert h using 1 ; dsimp [F,D₀,α,Y,z,g] ; norm_num ; ring
      let Rn : ℕ→Finset FreeRow := fun k=>rows∩dyadicRows 1 k
      let term : FreeRow→ℂ := fun u=>frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
        ∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>ProbeHighRowFamily.rayPoolOutside M H S N c b Y j _ (P j).property) WC Y
          (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I)
          ((17/50:ℂ)+t.1.2*Complex.I)
      let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(loss-1/40+mesh/6)
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hθ' : 1+α-17/50=θ := by dsimp [α,θ]; ring
      have hD' : 256*D₀*(AA+1) = D := by
        dsimp only [D₀,D,C]
        rw [show loss-1/40+mesh/6 = loss+(-1/40+mesh/6) by ring,
          Real.rpow_add hZp loss (-1/40+mesh/6)]
        ring
      have hdyad (k : ℕ) : ‖∑u∈Rn k,term u‖≤D*((2:ℝ)^k)^θ := by
        have hsub : Rn k ⊆ rows := Finset.inter_subset_left
        have hk : ∀u∈Rn k,(2:ℝ)^k≤rowNorm u ∧ rowNorm u≤2*(2:ℝ)^k := by
          intro u hu
          have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
          simpa only [one_mul] using And.intro h.1 h.2.le
        have hh := dyadic_weighted_rows α (17/50) D₀ ((2:ℝ)^k) hD₀
          (one_le_pow₀ (by norm_num)) (Rn k) hk F (fun u hu=>hF u (hsub hu)) z (by simp [z])
        rw [hθ'] at hh
        apply (norm_sum_le _ _).trans
        change (∑u∈Rn k, ‖term u‖) ≤ _
        simp_rw [term,norm_mul]
        change ∑u∈Rn k,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u ≤ _
        apply hh.trans
        rw [← hD']
        gcongr
        linarith
      have hpart := retained_dyadic_sum rows (Z^v) (fun u hu=>⟨(hrows u hu).1,hnorm u hu⟩) term
      change ‖∑u∈rows,term u‖≤mass
      rw [hpart]
      calc
        _ ≤ ∑k∈smallDyadicIndices (Z^v),‖∑u∈Rn k,term u‖ := norm_sum_le _ _
        _ ≤ ∑k∈smallDyadicIndices (Z^v),D*((2:ℝ)^k)^θ := Finset.sum_le_sum (fun k _=>hdyad k)
        _ = D*∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^θ := (Finset.mul_sum _ _ _).symm
        _ ≤ D*(Cg*(Z^v)^θ) := mul_le_mul_of_nonneg_left
          (hgeom (Z^v) (by positivity) (smallDyadicIndices (Z^v)) (fun k hk=>mem_smallDyadicIndices.mp hk)) hD
        _ = _ := by
          have hp : Z^(loss-1/40+mesh/6)*(Z^v)^θ=Z^(v*θ+loss-1/40+mesh/6) := by
            rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp]
            congr 1
            ring
          dsimp only [D,mass,Ca]
          calc
            _ = (C*Cg)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(loss-1/40+mesh/6)*(Z^v)^θ) := by ring
            _ = _ := by rw [hp])
  have hh := hp.trans_eq (show _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*
      Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
        ProbeCentralExponent.realLoss N v e eps loss mesh) by
    rw [ProbeCentralExponent.physical_scale_identity Z (51/100) e hZp]
    let x : ℝ := (25/48)*(51/100)-181/300+(105/8)*e
    let y : ℝ := v*θ+loss-1/40+mesh/6
    have hxy : x+y=ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
        ProbeCentralExponent.realLoss N v e eps loss mesh := by
      dsimp [x,y,θ,ProbeCentralExponent.sourceExponent,ProbeCentralExponent.realLoss]
      ring
    rw [←hxy,Real.rpow_add hZp x y]
    dsimp only [mass]
    change Cp*Z^x*(Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^y) = _
    ring)
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)).trans
  let x := ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
    ProbeCentralExponent.realLoss N v e eps loss mesh
  calc
    _ = (Cp*Ca*Cn)*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(x+nu) := by
      rw [Real.rpow_add hZp x nu]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le _) (by positivity)
      have hm := ProbeCentralExponent.floor_source_margin (1/100) 0 ζ v le_rfl hζ hvhi
      have hl := ProbeCentralExponent.realLoss_bound N v e eps loss mesh (by linarith) he.le heps.le
      dsimp only [x]
      linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
