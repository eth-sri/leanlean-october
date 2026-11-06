module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceAllocatedProfile
public import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
public import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion
open CenteredMomentCounting CenteredMomentComparisonReflection
open CenteredMomentOriginalReflectionErrorMass

theorem naturalSlot_ideal_bound (χ : Character) (pool : Finset (Ideal HeckeFamily.O))
    (β : Ideal HeckeFamily.O→ℂ) (b M P : ℝ) (hM : 0≤M) (hP : 0<P)
    (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool β P‖≤(128*max 1 b*M)*Real.sqrt P := by
  let f : Ideal HeckeFamily.O→ℂ:=fun I=>if I∈pool then idealCoeff χ I*β I else 0
  have hf0 : f 0=0:=by simp only [f,idealCoeff_zero,zero_mul,ite_self]
  have hf : ∀I,‖f I‖≤M := by
    intro I
    by_cases hi : I∈pool
    · simp only [f,ite_eq_left hi,norm_mul]
      exact (mul_le_mul (idealCoeff_norm_le_one χ I) (by grind) (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    · simpa only [f,ite_eq_right hi,norm_zero] using hM
  have hsup : ∀I,f I≠0 → (I.absNorm:ℝ)≤max 1 b*P := by
    intro I hi
    have hm : I∈pool:=by by_contra hn;exact hi (by grind)
    have hb : β I≠0:=by intro hz;exact hi (by grind)
    exact (hs I hm hb).trans (mul_le_mul_of_nonneg_right (by simp) hP.le)
  have he : (∑'I:Ideal HeckeFamily.O,f I)=∑I∈pool,idealCoeff χ I*β I := by
    rw [tsum_eq_sum (s:=pool) (fun I hi=>by grind)]
    exact Finset.sum_congr rfl (fun I hi=>by grind)
  have hh:=norm_tsum_ideal_ball f (max 1 b*P) M (by positivity) hM hf0 hf hsup
  rw [he] at hh
  unfold naturalSlot
  rw [←inverse_half_power P hP.le]
  apply normalized_linear_bound P _ hP
  linarith

theorem radialEnergy_le_absolute_mass (R : HeckeFamily.O→ℂ) (keep : HeckeFamily.O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hPhi : ∀z:HeckeFamily.O,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hs : Summable (fun z:HeckeFamily.O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)) :
    CenteredMomentOriginalRadialComparison.radialEnergy R keep Φ K≤
      ∑'z:HeckeFamily.O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
  let f:=fun z:HeckeFamily.O=>if keep z then ‖R z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hn (z:HeckeFamily.O):0≤f z:=by dsimp only [f];split_ifs;exact mul_nonneg (sq_nonneg _) (hPhi z);exact le_rfl
  have hb (z:HeckeFamily.O):f z≤‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
    dsimp only [f]
    split_ifs
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Complex.re_le_norm (Φ (‖eisEmbedding z‖^2/K))) (by positivity)
    · positivity
  exact (Summable.of_nonneg_of_le hn hb hs).tsum_le_tsum hb hs

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
