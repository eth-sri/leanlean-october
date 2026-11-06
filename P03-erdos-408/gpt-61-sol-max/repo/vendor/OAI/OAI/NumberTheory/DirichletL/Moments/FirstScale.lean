module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

public import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
public import OAI.NumberTheory.DirichletL.Moments.Scale

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve


def firstNominalScale (I J E : Ideal ActualEisensteinCubic.O) (K X : ℝ)  :=
  (Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*X^2 /
    (K*(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (commonPart J I):ℝ))

section
variable (I J E : Ideal ActualEisensteinCubic.O) (hI : I≠0) (hJ : J≠0) (hE : E≠0) (K X H HN Tsec : ℝ) (hK : 0<K) (hX : 0<X) (hH : 0≤H) (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X) (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X)

include hI in
theorem norm_pos     : 0<(Ideal.absNorm I:ℝ) := by solve_by_elim [_root_.OAI.SevenEighths.CenteredExceptionalCount.norm_pos]

theorem active_norm_pos   :
    0<(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ) := by
  apply norm_pos
  exact Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)

include hE hK hX in
theorem firstNominalScale_pos      
        : 0<firstNominalScale I J E K X := by
  unfold firstNominalScale
  exact div_pos (mul_pos (mul_pos (norm_pos E hE) (active_norm_pos I J)) (sq_pos_of_pos hX))
    (mul_pos (mul_pos hK (norm_pos _ (commonPart_ne_zero I J))) (norm_pos _ (commonPart_ne_zero J I)))

include hI hJ hE hK hX in
theorem first_kernel_ratio        
          :
    K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
      (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) =
      (H/firstNominalScale I J E K X)*(X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) := by
  have hc := norm_pos _ (commonPart_ne_zero I J)
  have hd := norm_pos _ (commonPart_ne_zero J I)
  have he := norm_pos E hE
  have hr := active_norm_pos I J
  have ha := norm_pos _ (residualPart_ne_zero I J)
  have hb := norm_pos _ (residualPart_ne_zero J I)
  have hi : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (residualPart I J):ℝ) := by
    exact_mod_cast absNorm_reconstruct I J hI
  have hj : (Ideal.absNorm J:ℝ)=(Ideal.absNorm (commonPart J I):ℝ)*(Ideal.absNorm (residualPart J I):ℝ) := by
    exact_mod_cast absNorm_reconstruct J I hJ
  rw [hi,hj]
  unfold firstNominalScale
  field_simp

include hI hJ hE hK hX hH hi hj in
theorem first_kernel_lower        
           
     
      :
    H/(Real.exp (2*HN)*firstNominalScale I J E K X) ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  rw [first_kernel_ratio I J E hI hJ hE K X H hK hX]
  have hnI := norm_pos I hI
  have hnJ := norm_pos J hJ
  have hT := firstNominalScale_pos I J E hE K X hK hX
  have hh : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*HN)*X^2 := by
    calc
      _ ≤ (Real.exp HN*X)*(Real.exp HN*X) := mul_le_mul hi hj hnJ.le (by positivity)
      _ = _ := by rw [show 2*HN=HN+HN by ring,Real.exp_add];ring
  have hr : 1/Real.exp (2*HN) ≤ X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
    apply (div_le_div_iff₀ (Real.exp_pos _) (mul_pos hnI hnJ)).mpr
    simpa only [one_mul,mul_comm] using hh
  calc
    _ = (H/firstNominalScale I J E K X)*(1/Real.exp (2*HN)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (div_nonneg hH hT.le)

include hI hJ hE hK hX hH hi hj in
theorem first_kernel_sector_lower        
           
     
     
    (hsec : firstNominalScale I J E K X≤Tsec) :
    (Real.exp (-2*HN)/Tsec)*H ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  have hT := firstNominalScale_pos I J E hE K X hK hX
  calc
    _ = H/(Real.exp (2*HN)*Tsec) := by rw [show -2*HN=-(2*HN) by ring,Real.exp_neg];ring
    _ ≤ H/(Real.exp (2*HN)*firstNominalScale I J E K X) :=
      (by bound)
    _ ≤ _ := first_kernel_lower I J E hI hJ hE K X H HN hK hX hH hi hj

end

end SevenEighths.CenteredMomentFirstScale

end

end OAI
