/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathFractions

@[expose] public section

namespace OAI.EuclideanRamsey

open scoped commutatorElement
variable {G : Type*} [Group G]

def Derived (N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n+1 => ⁅Derived N n,Derived N n⁆
instance derived_normal (N : Subgroup G) [N.Normal] (n : ℕ) : (Derived N n).Normal := by
  induction n with
  | zero => exact inferInstanceAs N.Normal
  | succ n ih =>
    let := ih
    exact Subgroup.commutator_normal _ _
section
variable {ι : Type*} [DecidableEq ι] {a : ι → Hilbert}

private lemma FractionOn.commutator {s : Finset ι} {z t : ι → LetterGroup}
    (hz : FractionOn a s z) (ht : FractionOn a s t)
    {i j k : ι} (hjk : j ≠ k)
    (hsz : ∀ l ∈ s, l ≠ i → l ≠ j → z l = 1) (hst : ∀ l ∈ s, l ≠ i → l ≠ k → t l = 1) :
    FractionOn a s (Pi.mulSingle i ⁅z i,t i⁆) := by
  have h := (hz.mul_pair (j:=i) (k:=k) ht hst).mul_pair (j:=i) (k:=j) hz.inv
    (by simpa only [Pi.inv_apply, inv_eq_one] using hsz)
  apply (h.mul_pair (j:=i) (k:=k) ht.inv (by simpa using hst)).congr
  intro l hl
  by_cases hli : l = i
  · subst l; simp [commutatorElement_def]
  · have hm : z l = 1 ∨ t l = 1 := by grind
    rcases hm with h|h <;> simp [hli,h]

/-- Commutators of fractions corrected away from two different coordinates are
corrected everywhere except the target coordinate. -/
theorem derived_subset_single (ha : Function.Injective a) {s : Finset ι} {i : ι}
    (his : i ∈ s) : Derived (LetterDifferences Hilbert) (s.card-2) ≤ Correctable a s i := by
  let N := LetterDifferences Hilbert
  have hsmall {s : Finset ι} (h : (s.erase i).card ≤ 1) : N ≤ Correctable a s i := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨⟨x,y⟩,rfl⟩
    change FractionOn a s (Pi.mulSingle i (FreeGroup.of x * (FreeGroup.of y)⁻¹))
    by_cases h' : (s.erase i).Nonempty
    · obtain ⟨j,hj⟩ := h'
      obtain ⟨z,m,hz,hzi,hzj⟩ := pair_difference a ha (Finset.ne_of_mem_erase hj).symm x y
      apply FractionOn.of_word hz
      intro l hl
      by_cases hli : l = i
      · subst l; simpa using hzi.symm
      have hlj := Finset.card_le_one_iff.mp h (Finset.mem_erase.mpr ⟨hli,hl⟩) hj
      subst l
      simpa [hli] using hzj.symm
    · apply FractionOn.of_word (Path.diag (FreeGroup.of x * (FreeGroup.of y)⁻¹))
      intro l hl
      have hli : l = i := by by_contra hn; exact h' ⟨l,Finset.mem_erase.mpr ⟨hn,hl⟩⟩
      simp [hli]
  induction s using Finset.strongInductionOn
  rename_i s ih
  have hc := Finset.card_erase_of_mem his
  by_cases h : (s.erase i).card ≤ 1
  · aesop
  let n := s.card-3
  rw [show s.card-2 = n+1 by omega]
  obtain ⟨j,k,hj,hk,hjk⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (s.erase i).card)
  have lift {j : ι} (hj : j ∈ s.erase i) {g : LetterGroup} (hg : g ∈ Derived N n) :
      ∃ z, FractionOn a s z ∧ z i = g ∧ ∀ l ∈ s, l ≠ i → l ≠ j → z l = 1 := by
    obtain ⟨hji,hjs⟩ := Finset.mem_erase.mp hj
    have h': i ∈ s.erase j := Finset.mem_erase.mpr ⟨hji.symm,his⟩
    have he : (s.erase j).card-2 = n := by rw [Finset.card_erase_of_mem hjs]; omega
    obtain ⟨c,u,v,m,n,hu,hv,hq,hc⟩ : FractionOn a (s.erase j) (Pi.mulSingle i g) :=
      ih _ (Finset.erase_ssubset hjs) h' (he.symm ▸ hg)
    refine ⟨u*v⁻¹,⟨c,u,v,m,n,hu,hv,fun _ _ => rfl,hc⟩,by simpa using (hq i h').symm,?_⟩
    intro l hl hli hlj
    simp_all; grind
  apply Subgroup.commutator_le.mpr
  intro g hg b hb
  obtain ⟨z,hz,hzi,hsz⟩ := lift hj hg
  obtain ⟨t,ht,hti,hst⟩ := lift hk hb
  change FractionOn a s (Pi.mulSingle i ⁅g,b⁆)
  simpa only [hzi,hti] using FractionOn.commutator hz ht hjk hsz hst

end

end OAI.EuclideanRamsey
