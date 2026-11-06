module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.WidthSchedule
public import OAI.NumberTheory.DirichletL.Energy.Profiles
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

def step (M B L:ℝ):=4*(L+M+B+4)
def range (M B L:ℝ):ℕ→ℝ
  | 0=>max 1 L
  | n+1=>step M B (range M B L n)
def sourceCap (M B L:ℝ)(n:ℕ):=10*(range M B L n+M+B+1)
def finalSourceCap (M B L ε:ℝ):=sourceCap M B L (count M ε)
def fineMesh (M B L κ ε:ℝ):=mesh M (finalSourceCap M B L ε) κ ε

section
variable (M B L κ ε : ℝ) (hM : 0≤M) (hB : 0≤B) (n : ℕ)

include hM hB in
lemma range_nonneg     :0≤range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

include hM hB in
lemma range_mono    :Monotone (range M B L):=by
  apply monotone_nat_of_le_succ
  grind [hh, range_nonneg, range, step]

include hM hB in
lemma sourceCap_nonneg     :0≤sourceCap M B L n:=by
  grind [range_nonneg, sourceCap]

include hM hB in
lemma fineMesh_pos    (hκ:0≤κ)(hε:0<ε):
    0<fineMesh M B L κ ε:=(bounds M (finalSourceCap M B L ε) κ ε hM
    (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.2.1

end

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI
