module

public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds
public import OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve

theorem continued_selected_slot_bound (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b →
      (∀y,‖W y‖≤B) → ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
          (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal HeckeFamily.O).absNorm:ℝ)^eps*Y^r := by
  obtain ⟨C,hC,hmain⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T→Ideal HeckeFamily.O := fun P=>P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T→ℂ := fun P=>continuedCompensatedLocal η u P.val (by grind) x w z
    (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  have hg (P : T) (_ : P∈Finset.univ) : ‖G P‖≤
      961*(if f P∣Ideal.span {u.val} then (Ideal.absNorm (f P):ℝ)^(1/2:ℝ) else 1) := by
    have hh := continuedCompensatedLocal_bound η u P.val (by grind)
      (by grind) x w z hx hw (by linarith)
    apply hh.trans
    by_cases hp : f P∣Ideal.span {u.val}
    · simp only [show P.val.val=f P from rfl,ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by grind)
        (by grind)
    · grind
  exact hmain f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G hg z hz

end SevenEighths.ProbeHighRowFamily
end

end OAI
