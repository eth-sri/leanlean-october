module

public import OAI.NumberTheory.DirichletL.Hecke.DyadicScaled

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_reflected_bound (e κ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤η → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) false W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cg,Cr,hCg,hCr,hbound⟩ := reflected_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+(2*Cr)*Real.pi+2*(Cg)*3+E*Real.pi
  have hC : 0<C := by positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU  := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp  := lt_of_lt_of_le zero_lt_one hU
  have hD  := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := reflected_central_cost (χ j) U H a e κ η r hQ hH (by linarith) he.le hκ.le hκ' hheight
  have hexternal := reflected_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |1+a+6*e|≤3 := abs_le.mpr ⟨by linarith,by linarith⟩
  let Q : ℝ := (χ j).modulus.absNorm
  let Rad : ℝ := (HeckeDeletionBounds.radical (χ j).modulus).absNorm
  let L := (U^r)^(1/2-a-6*e)*(Cr*Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
      (presentationComplexity (χ j) H)^κ)
  let J := (U^r)^(3/2 : ℝ)*(Cg*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)
  have hb' : ‖polynomial (χ j) false W (U^r) σ freq‖≤
      (1/(2*Real.pi))*(C₂*L*Real.pi+2*(Cn*J/(1+V)^n)*|1+a+6*e|+
        Cn*(U^r)^(3/2:ℝ)*E/(1+V)^n*Real.pi) := by
    convert hb using 1 <;> dsimp only [L,J,E] <;> ring
  exact HeckeDyadic.rescale_rectangle_bound hC₂ hCn hE (by positivity) (by positivity)
    (by positivity) (by positivity)
    (by dsimp [J,Q,Rad]; positivity) hV
    (by convert mul_le_mul_of_nonneg_left hcentral hCr.le using 1 <;> ring)
    (by convert mul_le_mul_of_nonneg_left hexternal hCg.le using 1 <;> ring) hpow hwidth hb'

end SevenEighths.HeckeDyadic

end

end OAI
