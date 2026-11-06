module

public import OAI.NumberTheory.DirichletL.Descent.SecondProfileIdentity

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

def secondRelativeNorm (q : Fin 6 → ℝ) (G E V K X : ℝ)  :=
  ![q 0/G,q 1/E,q 2/V,q 3/K,q 4/X,q 5/X]

def secondRelativeLog (q : Fin 6 → ℝ) (G E V K X : ℝ) (i : Fin 6)  :=
  Real.log (secondRelativeNorm q G E V K X i)

lemma secondRelativeNorm_pos  q  (hq : ∀ i, 0 < q i)
     G E V K X  (hG : 0 < G) (hE : 0 < E) (hV : 0 < V) (hK : 0 < K) (hX : 0 < X) :
    ∀ i, 0 < secondRelativeNorm q G E V K X i := by
  intro i
  fin_cases i
  · exact div_pos (hq 0) hG
  · exact div_pos (hq 1) hE
  · exact div_pos (hq 2) hV
  · exact div_pos (hq 3) hK
  · exact div_pos (hq 4) hX
  · exact div_pos (hq 5) hX

lemma secondNormProfile_eq_full_of_windows  W₁ W₂   Φ 
     V   R   q  (hq : ∀ i, 0 < q i)
    (hV : ∀ i, V i (Real.log (q i)) = 1) :
    secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R q =
      secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) := by
  rw [secondPoissonProfile_log W₁ W₂ Φ V R q hq]
  simp only [secondNormProfile, hV, Finset.prod_const_one]

end
end SevenEighths.InverseMoment

end OAI
