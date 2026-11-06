module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.GramShell
public import OAI.NumberTheory.DirichletL.Detector.GramAnnularCount

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT


def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)  :=
  (elementWindow_finite_support W hW N hN).toFinset

section
variable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n : ActualEisensteinCubic.O) (hn : n∈shellLatticeColumns W hW N hN) (m : ActualEisensteinCubic.O) (f : ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ)

lemma shellLatticeColumns_mem           :
    n∈shellLatticeColumns W hW N hN ↔ W (‖eisEmbedding n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rfl

include ha hs hn in
lemma shellLatticeColumns_nonzero        
           
      : n≠0 := by
  intro hz
  have hh := (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).1
  simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div] at hh
  linarith

include hs hn in
lemma shellLatticeColumns_norm        
         
      : ‖eisEmbedding n‖^2≤b*N :=
  (div_le_iff₀ hN).mp (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).2

lemma shell_lattice_support        
         
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

include hW hN in
lemma shell_lattice_summable        
          :
    Summable (fun m : ActualEisensteinCubic.O×ActualEisensteinCubic.O=>f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  grind [shellLatticeColumns, shell_lattice_support]

lemma shell_lattice_tsum        
          :
    (∑'m : ActualEisensteinCubic.O×ActualEisensteinCubic.O,f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N))=
      ∑n∈shellLatticeColumns W hW N hN,∑m∈shellLatticeColumns W hW N hN,
        f n m*shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N) := by
  rw [tsum_eq_sum (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN)) (by
    grind [shellLatticeColumns, shell_lattice_support])]
  exact Finset.sum_product _ _ _

end

end SevenEighths.ProbeGramCommon
end

end OAI
