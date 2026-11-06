module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.PhysicalEnergy
public import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {φ σ : Type*} [Fintype φ] [Fintype σ] {a c : ActualEisensteinCubic.O} {mode : Bool}

def survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (nset bset : Finset (Ideal ActualEisensteinCubic.O))  :=
  Finset.univ.filter (fun e => ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0)

lemma mem_survivingFrozenBranches (F : PrimeFamily φ)  jF 
     A   nset bset   e  :
    e∈survivingFrozenBranches F jF A nset bset ↔
      ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0 := by
  simp [survivingFrozenBranches]

section
variable (F : PrimeFamily φ) (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ) (e : φ→Fin 3) (S : Ideal ActualEisensteinCubic.O→PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (κ : ℂ) (A : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (r aw : Ideal ActualEisensteinCubic.O→ℂ) (w : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O)) (K : Ideal ActualEisensteinCubic.O) (Y B : ℝ) (hn : ∀ n∈nset, primaryGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y) (hb : ∀ b∈bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)


lemma frozenBranchColumn_weight      
       n b  :
    frozenBranchColumn F jF e (fun n b => A n b*w n b) n b =
      w n b*frozenBranchColumn F jF e A n b := by
  unfold frozenBranchColumn
  ring

lemma weighted_branch_zero_of_not_surviving      
     
     
       
           
       
    (he : e∉survivingFrozenBranches F jF A nset bset) :
    weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K=0 := by
  have hz : ∀ n∈nset, ∀ b∈bset, frozenBranchColumn F jF e A n b=0 := by
    simp_all [mem_survivingFrozenBranches]
  unfold weightedReflectedBranchHybridRow hybridRow hybridInner
  simp only [frozenBranchColumn_weight]
  simp_all

lemma sum_branches_eq_surviving    
     
     
       
           
        :
    (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K)=
    ∑ e∈survivingFrozenBranches F jF A nset bset,
      weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K := by
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  simp_all [weighted_branch_zero_of_not_surviving]

include hF hn hb in
theorem surviving_forced_norms  
       
         
     
     
     e  (he : e∈survivingFrozenBranches F jF A nset bset) :
    (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)≤Y ∧
    (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)≤B := by
  obtain ⟨n,hn',b,hb',hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b (hn n hn').1 (hb b hb').1 hz
  have hn0 : n≠0 := by intro h; exact (hn n hn').1 (by rw [h,primaryGenerator_zero])
  have hb0 : b≠0 := by intro h; exact (hb b hb').1 (by rw [h,primaryGenerator_zero])
  have hnpos : 0<Ideal.absNorm n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0)
  have hbpos : 0<Ideal.absNorm b := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb0)
  constructor
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm hd1)) (hn n hn').2
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hbpos (map_dvd Ideal.absNorm hd2)) (hb b hb').2

include hF hn hb in
theorem surviving_extracted_scales  
       
         
     
     
     e  (he : e∈survivingFrozenBranches F jF A nset bset) :
    extractedDualScale (frozenExtracted F jF e 1) Y = Y/Ideal.absNorm (frozenExtracted F jF e 1) ∧
    extractedDualScale (frozenExtracted F jF e 2) B = B/Ideal.absNorm (frozenExtracted F jF e 2) := by
  have h := surviving_forced_norms F hF jF A nset bset Y B hn hb e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact ⟨max_eq_right ((one_le_div (hp 1)).mpr h.1),
    max_eq_right ((one_le_div (hp 2)).mpr h.2)⟩

end

end
end SevenEighths.InverseReflectedPhase

end OAI
