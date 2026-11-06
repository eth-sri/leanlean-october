module
public import Mathlib.Tactic

public import Erdos821.P4Probe.SelectedTuples

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

-- Slot counts for the two sides (generic ell).
def kFalse (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count)  :=
  if h : P.big g = true then
    if block ⟨g, h⟩ = false then (ν.changed g).card else 0
  else 0

def kTrue (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (g : Fin P.count)  :=
  if h : P.big g = true then
    if block ⟨g, h⟩ = true then (ν.changed g).card else 0
  else 0

section
variable (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (g : Fin P.count) (hs : g ∈ (P4Probe.analyticGroups P).small)


lemma kFalse_le    
      : kFalse ν block g ≤ m := by
  unfold kFalse
  split_ifs with h1 h2
  · exact (ν.bound g).trans (by omega)
  · omega
  · omega

lemma kTrue_le    
      : kTrue ν block g ≤ m := by
  unfold kTrue
  split_ifs with h1 h2
  · exact (ν.bound g).trans (by omega)
  · omega
  · omega

include hs in
lemma kFalse_small    
        :
    kFalse ν block g = 0 := by
  have hb : P.big g = false := by
    have hmem : g ∈ P.smallGroups := hs
    simpa [PrimeGroups.smallGroups] using hmem
  unfold kFalse
  simp [hb]

include hs in
lemma kTrue_small    
        :
    kTrue ν block g = 0 := by
  have hb : P.big g = false := by
    have hmem : g ∈ P.smallGroups := hs
    simpa [PrimeGroups.smallGroups] using hmem
  unfold kTrue
  simp [hb]

end

-- Nonempty changed for ProbeChoice witnesses (generic ell).
lemma choiceBase_changed_nonempty (hj : m ≤ J)
    (c : P.BigGroup → Finset (Fin m)) (g : P.BigGroup)
    (hne : (c g).Nonempty) :
    (((choiceBase hj c : Pattern P J ell m).changed g.val).Nonempty) := by
  have himg : ((c g).image (Fin.castLE hj)).Nonempty :=
    hne.image _
  have heq : (choiceBase hj c : Pattern P J ell m).changed g.val =
      (c g).image (Fin.castLE hj) := by
    simp [choiceBase, liftChoice, g.property]
  rw [heq]
  exact himg

section
variable (hj : m ≤ J) (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (c : ProbeChoice P m block) (g : P.BigGroup) (hg : block g = false) (hne : (c.val g).Nonempty)


include hg hne in
lemma kFalse_pos    
       
        :
    0 < kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val := by
  grind [choiceBase, choiceBase_changed_nonempty, kFalse]

lemma kTrue_pos    
       
    (hg : block g = true) (hne : (c.val g).Nonempty) :
    0 < kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val := by
  grind [choiceBase, choiceBase_changed_nonempty, kTrue]

include hg hne in
lemma kFalse_bigSlots    
       
        :
    Blueprint.Analytic.bigSlots (P4Probe.analyticGroups P)
      (kFalse (choiceBase hj c.val : Pattern P J ell m) block) m := by
  refine ⟨?_, fun g => ⟨kFalse_le _ _ g, kFalse_small _ _ g⟩⟩
  have hpos : 0 < kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val :=
    kFalse_pos hj block c g hg hne
  have hle : kFalse (choiceBase hj c.val : Pattern P J ell m) block g.val ≤
      ∑ g, kFalse (choiceBase hj c.val : Pattern P J ell m) block g := by
    apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
    exact Finset.mem_univ _
  exact lt_of_lt_of_le hpos hle

lemma kTrue_bigSlots    
       
    (hg : block g = true) (hne : (c.val g).Nonempty) :
    Blueprint.Analytic.bigSlots (P4Probe.analyticGroups P)
      (kTrue (choiceBase hj c.val : Pattern P J ell m) block) m := by
  refine ⟨?_, fun g => ⟨kTrue_le _ _ g, kTrue_small _ _ g⟩⟩
  have hpos : 0 < kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val :=
    kTrue_pos hj block c g hg hne
  have hle : kTrue (choiceBase hj c.val : Pattern P J ell m) block g.val ≤
      ∑ g, kTrue (choiceBase hj c.val : Pattern P J ell m) block g := by
    apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
    exact Finset.mem_univ _
  exact lt_of_lt_of_le hpos hle

lemma sideCounts_false_eq     :
    selectedCounts (patternAuxCoordinates ν block false) = kFalse ν block := by
  funext g
  unfold selectedCounts kFalse patternAuxCoordinates
  split_ifs <;> simp

lemma sideCounts_true_eq     :
    selectedCounts (patternAuxCoordinates ν block true) = kTrue ν block := by
  funext g
  unfold selectedCounts kTrue patternAuxCoordinates
  split_ifs <;> simp

end

end
end Erdos821.P4Bridge
