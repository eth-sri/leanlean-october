module

public import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

alias _root_.OAI.SevenEighths.CenteredMomentConjugateWindow.star_logPhase := _root_.OAI.SecondPassIntegration.logPhase_conjugate

theorem star_columnPhase (V : ℝ → ℂ) (u t : ℝ) :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  rw [columnPhase,star_mul,star_logPhase,columnPhase,mul_comm]
  congr 1
  simp only [rootWindow,Complex.star_def,map_div₀,Complex.conj_ofReal]

end SevenEighths.CenteredMomentConjugateWindow

end

end OAI
