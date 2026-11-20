module
public import OAI.NumberTheory.DirichletL.Detector.InitialFubini

@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

lemma sourceMellinWeight_shear (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z (t+1-z) w z=
      (X:ℂ)^(1/2-z)*(Z:ℂ)^t*(Y:ℂ)^(w-1)*Complex.exp (t^2)*
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w := by
  simp only [sourceMellinWeight,show t+1-z+z-1=t by ring]

end SevenEighths.ProbePhysical
end

end OAI
