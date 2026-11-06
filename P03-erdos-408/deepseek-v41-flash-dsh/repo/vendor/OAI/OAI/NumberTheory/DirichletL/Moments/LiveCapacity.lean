module

public import OAI.NumberTheory.DirichletL.Moments.ActualLiveSlotRemoval

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentLiveCapacity

 def excess {ι:Type*} (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ:ℝ) : ℝ :=
  max (n₁+n₂+6*κ*(∑i∈J,w i)-M) 0

 theorem remaining_capacity {ι:Type*} [DecidableEq ι]
    (J R:Finset ι) (hR:R⊆J) (w:ι→ℝ) (n₁ n₂ M κ:ℝ)
    (hpay:R=J ∨ excess J w n₁ n₂ M κ≤6*κ*(∑i∈R,w i)) :
    R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M := by
  rcases hpay with h|h
  · exact Or.inl h
  · right
    have hs:=Finset.sum_sdiff hR (f:=w)
    have hm:=le_max_left (n₁+n₂+6*κ*(∑i∈J,w i)-M) (0:ℝ)

    have hh:=hm.trans h
    rw [←hs] at hh
    nlinarith

end SevenEighths.CenteredMomentLiveCapacity

end

end OAI
