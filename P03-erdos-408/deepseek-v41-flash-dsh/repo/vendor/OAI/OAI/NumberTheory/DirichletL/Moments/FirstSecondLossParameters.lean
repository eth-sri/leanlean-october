module

public import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters


def depth (Mcap σ:ℝ):ℕ:=⌈2*Mcap/σ⌉₊+1

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI
