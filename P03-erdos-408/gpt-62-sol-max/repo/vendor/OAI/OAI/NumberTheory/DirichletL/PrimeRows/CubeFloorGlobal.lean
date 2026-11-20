module

public import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
public import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
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

theorem actual_global_floor_cube_arithmetic (N n : ℕ) (sc : FloorDetectorScales)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*sc.e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,sc.dmax*sc.rmin≤ell j) (hellhi : ∀j,ell j≤sc.dmin*sc.R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo sc.c sc.b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤sc.A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,sc.dmin≤d → d≤sc.dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^sc.δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-sc.margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^sc.τ)<51/100+2*sc.e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^sc.τ ∧ |t.2|≤(3*i+1:ℕ)*Z^sc.τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^sc.τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y) W Y (51/100) sc.e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*sc.eps)*
          Z^(v*(67/100+12*sc.e+sc.eps*(N+8))+sc.loss-1/40+sc.mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n sc.e sc.eps sc.c sc.b sc.A sc.R sc.dmin sc.dmax sc.rmin sc.τ sc.ε sc.κ sc.cost sc.mesh sc.δ sc.margin sc.loss
    sc.he sc.he1 sc.heps sc.hc sc.hcb sc.hA sc.hR sc.hdmin sc.hdmax sc.hdRange sc.hrmin sc.hτ sc.hε sc.hκ sc.hcost sc.hmesh sc.hδ sc.hbudget sc.hgap sc.hmargin sc.hheight sc.hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let α : ℝ := 1/100+12*sc.e+sc.eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  let θ : ℝ := 67/100+12*sc.e+sc.eps*(N+8)
  have hθ : 0<θ := by have := sc.he; have := sc.heps; dsimp [θ]; positivity
  obtain ⟨Cg,hCg,hgeom⟩ := bounded_dyadic_power_sum θ hθ
  refine ⟨256*C*(AA+1)*Cg,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := sc.hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y j _ (P j).property) W Y
    (((51/100+16*sc.e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*sc.e:ℝ):ℂ)+t.2*Complex.I) z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^sc.loss*Z^(-1/40+sc.mesh/6)
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤D*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) sc.mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) sc.b (Y j) z)
    have hellpos (j : Fin N) : 0≤ell j := by
      exact (mul_nonneg sc.hdmax sc.hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j=>ell j/d) g (1/50)
      (fun j _=>div_nonneg (hellpos j) hd0.le)
      (by rw [source_slot_length_sum _ _ _ hellsum];positivity)
      (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+sc.mesh))≤Z^(-1/40+sc.mesh/6) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+sc.mesh))=
        Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+sc.mesh/6) from
        source_slot_product Finset.univ ell g Z d sc.mesh hZp hd0.ne' hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [hq.2]
    have hN : 0≤rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert h using 1 ; dsimp [F,D,α,Y,z,g] ; norm_num ; ring
  let Rn : ℕ→Finset FreeRow := fun k=>rows∩dyadicRows 1 k
  let term (u : FreeRow) := frequencyWeight z ⟨u.val,u.property.1⟩*
    ∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y j _ (P j).property) W Y
      (((51/100+16*sc.e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*sc.e:ℝ):ℂ)+t.2*Complex.I) z
  let D' := 256*D*(AA+1)
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hdyad (k : ℕ) : ‖∑u∈Rn k,term u‖≤D'*((2:ℝ)^k)^θ := by
    have hn : ∀u∈Rn k,(2:ℝ)^k≤rowNorm u ∧ rowNorm u≤2*(2:ℝ)^k := by
      intro u hu
      have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [one_mul] using And.intro h.1 h.2.le
    apply (norm_sum_le _ _).trans
    simp only [term,norm_mul]
    refine (dyadic_weighted_rows α (17/50) D ((2:ℝ)^k) hD (one_le_pow₀ (by norm_num))
      (Rn k) hn F (fun u hu=>hF u (Finset.mem_inter.mp hu).1) z (by simp [z])).trans ?_
    rw [show 1+α-17/50 = θ by dsimp [α,θ]; ring]
    dsimp only [D']
    change 256*D*AA*_ ≤ _
    gcongr
    linarith
  have hpart := retained_dyadic_sum rows (Z^v) (fun u hu=>⟨(hrows u hu).1,hnorm u hu⟩) term
  change ‖∑u∈rows,term u‖≤_
  rw [hpart]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^v),‖∑u∈Rn k,term u‖ := norm_sum_le _ _
    _ ≤ ∑k∈smallDyadicIndices (Z^v),D'*((2:ℝ)^k)^θ := Finset.sum_le_sum (fun k _=>hdyad k)
    _ = D'*∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^θ := (Finset.mul_sum _ _ _).symm
    _ ≤ D'*(Cg*(Z^v)^θ) := mul_le_mul_of_nonneg_left
      (hgeom (Z^v) (by positivity) (smallDyadicIndices (Z^v)) (fun k hk=>mem_smallDyadicIndices.mp hk)) hD'
    _ = _ := by
      have hp : Z^sc.loss*Z^(-1/40+sc.mesh/6)*(Z^v)^θ=Z^(v*θ+sc.loss-1/40+sc.mesh/6) := by
        rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
        congr 1; ring
      dsimp only [D',D]
      rw [←hp]
      ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
