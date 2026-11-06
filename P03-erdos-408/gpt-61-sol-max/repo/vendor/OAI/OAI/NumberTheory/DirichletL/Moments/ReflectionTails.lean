module

public import OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson



section
variable (η : Character) (F : ℝ→ℂ) (A B : ℕ) (hB : 2≤B) (D Y : ℝ) (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) (R : ℝ)

include hB in
lemma ideal_norm_rpow_summable     :
    Summable (fun I : UnrestrictedIdealReindex.NonzeroIdeal=>(I.val.absNorm:ℝ)^(-(B:ℝ))) := by
  have hb : (1:ℝ)<B := by exact_mod_cast (by omega : 1<B)
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (B:ℂ)
    (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : UnrestrictedIdealReindex.NonzeroIdeal=>I.val))
  apply hs.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property]
  change ‖((I.val.absNorm:ℝ):ℂ)^(-(B:ℂ))‖=_
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hi]
  simp

include hY hF in
lemma plain_term_rapid_bound        
        (I : UnrestrictedIdealReindex.NonzeroIdeal) :
    ‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤
      (D*Y^B)*(I.val.absNorm:ℝ)^(-(B:ℝ)) := by
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  have hx : 0<(I.val.absNorm:ℝ)/Y := div_pos hi hY
  have hb : ‖F ((I.val.absNorm:ℝ)/Y)‖≤D/((I.val.absNorm:ℝ)/Y)^B :=
    (le_div_iff₀ (pow_pos hx B)).mpr (by simpa only [mul_comm] using hF _ hx)
  calc
    _≤‖F ((I.val.absNorm:ℝ)/Y)‖:=by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)
    _≤D/((I.val.absNorm:ℝ)/Y)^B:=hb
    _=_:=by
      rw [Real.rpow_neg hi.le,Real.rpow_natCast,div_pow]
      field_simp

include hB hY hF in
theorem plain_rapid_summable        
          :
    Summable (fun I : UnrestrictedIdealReindex.NonzeroIdeal=>idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (plain_term_rapid_bound η F B D Y hY hF)
    ((ideal_norm_rpow_summable B hB).mul_left (D*Y^B))

include hB in
theorem plain_rapid_bound     :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(F : ℝ→ℂ)(D Y : ℝ),0≤D → 0<Y →
      (∀x : ℝ,0<x → x^B*‖F x‖≤D) →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*D*(Y^B/Real.sqrt Y) := by
  let C := 1+∑' I : UnrestrictedIdealReindex.NonzeroIdeal,(I.val.absNorm:ℝ)^(-(B:ℝ))
  have hs := ideal_norm_rpow_summable B hB
  have hnon : 0≤∑' I : UnrestrictedIdealReindex.NonzeroIdeal,(I.val.absNorm:ℝ)^(-(B:ℝ)) :=
    tsum_nonneg (fun I=>Real.rpow_nonneg (HeckeDyadic.norm_pos I).le _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro η F D Y hD hY hF
  have ht := plain_rapid_summable η F B hB D Y hY hF
  have hh := ht.norm.tsum_le_tsum (plain_term_rapid_bound η F B D Y hY hF)
    (hs.mul_left (D*Y^B))
  rw [tsum_mul_left] at hh
  have hb : ‖∑' I : UnrestrictedIdealReindex.NonzeroIdeal,idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤D*Y^B*C := (norm_tsum_le_tsum_norm ht.norm).trans (hh.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C];linarith) (by positivity)))
  rw [polynomial_plain η F Y hY,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _≤(Real.sqrt Y)⁻¹*(D*Y^B*C):=mul_le_mul_of_nonneg_left hb (by positivity)
    _=C*D*(Y^B/Real.sqrt Y):=by ring

lemma discarded_rapid_control      
    (hD : 0≤D) (hR : 0<R) (hF : ∀x : ℝ,0<x → x^(B+A)*‖F x‖≤D) :
    ∀x : ℝ,0<x → x^B*‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤D/R^A := by
  intro x hx
  by_cases hz : CenteredMomentSectorLocalization.discardedWeight R x=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
    positivity
  have hRx := (CenteredMomentSectorLocalization.discardedWeight_support R x hz).le
  have hw := CenteredMomentSectorLocalization.discardedWeight_bounds R x
  have hnorm : ‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤‖F x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  apply (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hx.le B)).trans
  apply (le_div_iff₀ (pow_pos hR A)).mpr
  calc
    _≤(x^B*‖F x‖)*x^A :=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRx A) (by positivity)
    _=x^(B+A)*‖F x‖ :=by rw [pow_add];ring
    _≤D :=hF x hx

end

end SevenEighths.CenteredMomentComparisonReflection



end OAI
