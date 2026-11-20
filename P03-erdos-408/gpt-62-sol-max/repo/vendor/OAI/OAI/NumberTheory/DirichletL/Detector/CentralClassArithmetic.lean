module

public import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
public import OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight
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

theorem actual_class_cube_arithmetic (N n : ℕ) (sc : FloorDetectorScales)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*sc.e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,sc.dmax*sc.rmin≤ell j) (hellhi : ∀j,ell j≤sc.dmin*sc.R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo sc.c sc.b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤sc.A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,sc.dmin≤d → d≤sc.dmax → ∀(v a q D Rcount : ℝ),0≤v → 51/100≤a → a≤1 → 0≤D → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^sc.δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-sc.margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      (rows.card:ℝ)≤D*(Z^d)^Rcount →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^sc.τ)<a+2*sc.e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^sc.τ ∧ |t.2|≤(3*i+1:ℕ)*Z^sc.τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^sc.τ) →
      (∀u∈rows,weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) sc.mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) sc.b (Y j) ((17/50:ℂ)+t.1.2*Complex.I)))=q) →
      ‖cubeArithmeticSum S hS hmax η rows T (poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y) W Y a sc.e t‖≤
        C*D*(η.modulus.absNorm:ℝ)^(2*sc.eps)*
          Z^(d*Rcount+v*(a-1/2+12*sc.e+sc.eps*(N+8)-17/50)+sc.loss-2/75+q/6+sc.mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n sc.e sc.eps sc.c sc.b sc.A sc.R sc.dmin sc.dmax sc.rmin sc.τ sc.ε sc.κ sc.cost sc.mesh sc.δ sc.margin sc.loss
    sc.he sc.he1 sc.heps sc.hc sc.hcb sc.hA sc.hR sc.hdmin sc.hdmax sc.hdRange sc.hrmin sc.hτ sc.hε sc.hκ sc.hcost sc.hmesh sc.hδ sc.hbudget sc.hgap sc.hmargin sc.hheight sc.hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2:ℝ)^(4/25+12*sc.e+sc.eps*(N+8)))
  have hAA : 0<AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*AA,mul_pos hC hAA,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hd0 : 0<d := sc.hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S sc.c sc.b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let α : ℝ := a-1/2+12*sc.e+sc.eps*(N+8)
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y j _ (P j).property) W Y
    (((a+16*sc.e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*sc.e:ℝ):ℂ)+t.2*Complex.I) z‖
  let E : ℝ := C*(η.modulus.absNorm:ℝ)^(2*sc.eps)*Z^sc.loss*Z^(-2/75+q/6+sc.mesh/6)
  have hE : 0≤E := by dsimp [E];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤E*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) sc.mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) sc.b (Y j) z)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+sc.mesh))=Z^(-2/75+q/6+sc.mesh/6) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+sc.mesh))=
        Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+sc.mesh/6) from
        source_slot_product Finset.univ ell g Z d sc.mesh hZp hd0.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j=>ell j/d) g=q from hq u hu]
      congr 1 ; ring
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 ; dsimp [F,E,α,Y,z,g] ; ring
  have hh := dyadic_weighted_rows_card α (17/50) E (Z^v) (D*(Z^d)^Rcount) hE
    (Real.rpow_pos_of_pos hZp _) rows hcard hnorm F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (poolOutside (RayQuotient.identityClass M H) S sc.c sc.b Y) W Y a sc.e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)≤AA :=
    annular_power_uniform _ _ (by dsimp [α];linarith)
  apply (hsum.trans hh).trans
  have hpow : (Z^d)^Rcount*Z^sc.loss*Z^(-2/75+q/6+sc.mesh/6)*(Z^v)^(α-17/50)=
      Z^(d*Rcount+v*(a-1/2+12*sc.e+sc.eps*(N+8)-17/50)+sc.loss-2/75+q/6+sc.mesh/6) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D*(Z^d)^Rcount)*E*AA*(Z^v)^(α-17/50) := by gcongr
    _ = _ := by
      dsimp [E]
      calc
        _ = (C*AA)*D*(η.modulus.absNorm:ℝ)^(2*sc.eps)*
          ((Z^d)^Rcount*Z^sc.loss*Z^(-2/75+q/6+sc.mesh/6)*(Z^v)^(α-17/50)) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeHighRowFamily

end

end OAI
