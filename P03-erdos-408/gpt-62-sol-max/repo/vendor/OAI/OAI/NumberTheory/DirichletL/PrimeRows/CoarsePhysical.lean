module

public import OAI.NumberTheory.DirichletL.PrimeRows.CoarseUniform
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstJoint
public import OAI.NumberTheory.DirichletL.PrimeRows.DiskControl
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedBin
public import OAI.NumberTheory.DirichletL.Hecke.StripActual

public import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalProductBounds

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem buffered_denominator_polynomial_growth (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (ψ : ι→Character)
      (a B H : ℝ) (i : ℕ),(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^2*(3+|H|)^2 := by
  obtain ⟨C,hC,hbound⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  refine ⟨2*C*(1+A^2),by positivity,?_⟩
  intro η u ψ a B H i ha haTop hB hH hbin x hxl hxr hxi
  let χ := (targetRow η u).excludePrimes S hS
  have hb := hbound (sourceDetectorFamily S hS η u ψ) B a H i hB ha haTop hH hbin (Sum.inl false) x hxl hxr hxi
  simp only [sourceDetectorFamily_denominator,Real.rpow_one] at hb
  have hQ : (χ.modulus.absNorm:ℝ)≤(η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [χ,A]
    exact_mod_cast (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hh)
  apply hb.trans
  unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity
  have hrad := HeckeDyadic.radical_norm_le_modulus χ
  calc
    _ ≤ C*((χ.modulus.absNorm:ℝ)*(2*(χ.modulus.absNorm:ℝ)*(3+|H|)^2)) := by gcongr
    _ ≤ C*(((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*
        (2*((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*(3+|H|)^2)) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ((η.modulus.absNorm:ℝ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)*(3+|H|))]

def coarsePrimeCost (T : Finset PrimeIdeal) : ℝ := ∏P∈T,(8192:ℝ)*(P.val.absNorm:ℝ)^3


theorem calibrated_physicalRow_buffered_polynomial_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (ψ : ι→Character),
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*
          coarsePrimeCost T*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_denominator_polynomial_growth (ι:=ι) e he he' S hS.prime
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*Cr*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT ψ a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn u hu w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec := hreciprocal η u ψ a B H i ha ha1 hB hH hbin x hxl hxr hxi
  have hg : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ coarsePrimeCost T := by
    unfold coarsePrimeCost
    rw [← Finset.prod_attach]
    apply rowLocalProduct_first_bound S hS T hT η u x w z 2 (by linarith) hxr (by rw [hw]; linarith) hz (by rw [hw]; linarith)
    intro P
    have hQ := hS.tail.norm_four P.val (hT P.val P.property)
    exact selectedFirstBound_polynomial (by exact_mod_cast (by omega : 1 ≤ P.val.val.absNorm))
  exact (physicalRow_norm_le S hS T hT η u x w z (star ((calibrationForSet S hmax).residueMonoid u.val)) hl hrec hn' hh' hg).trans_eq
    (by dsimp [N]; ring)


theorem calibrated_physicalRow_first_joint_polynomial_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S),∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*coarsePrimeCost T*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*L*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hn' := hn u hu w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖rowLocalProduct S hS T hT η u x w z‖ ≤ coarsePrimeCost T := by
    unfold coarsePrimeCost
    rw [← Finset.prod_attach]
    apply rowLocalProduct_first_bound S hS T hT η u x w z 2 (by rw [hx]; norm_num) hx.le hw hz (by rw [hx]; linarith)
    intro P
    have hQ := hS.tail.norm_four P.val (hT P.val P.property)
    exact selectedFirstBound_polynomial (by exact_mod_cast (by omega : 1 ≤ P.val.val.absNorm))
  exact (physicalRow_norm_le S hS T hT η u x w z (star ((calibrationForSet S hmax).residueMonoid u.val)) hl hrec hn' hh' hg).trans_eq
    (by dsimp [N]; ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
