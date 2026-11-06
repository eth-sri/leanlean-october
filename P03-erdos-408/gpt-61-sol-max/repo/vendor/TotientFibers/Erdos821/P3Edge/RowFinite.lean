module
public import Mathlib.Tactic

public import Erdos821.P3Edge.RowSupport

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def mkTarget (A : Model F P J m) {n } (i : Fin n)
    (s ) :
    EdgeChoice A s × P.Labels (J + F.ell) → P.MemoryState (J + F.ell) :=
  fun p => (targetSmall A i s p.1, p.2, targetMem A i s p.1)

section
variable (A : Model F P J m) {n : ℕ} (i : Fin n) (s t : P.MemoryState (J + F.ell))


lemma mkTarget_eq      
      (c : EdgeChoice A s)
    (h : edgeChoiceValid A .all i s t c) :
    t = mkTarget A i s (c, t.2.1) := Prod.ext (Erdos821.P3Edge.valid_target_small A i s t c h) (Prod.ext (Eq.refl t.2.1) (funext (Erdos821.P3Edge.valid_target_mem A i s t c h)))

lemma row_valid_set_finite      
      :
    Set.Finite {t : P.MemoryState (J + F.ell) | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} := Set.Finite.subset (Set.Finite.image (Erdos821.P3Edge.mkTarget A i s) Set.finite_univ) fun ⦃t⦄ ht => Exists.casesOn ht fun c hc => Exists.intro (c, t.2.1) ⟨Set.mem_univ (c, t.2.1), Eq.symm (Erdos821.P3Edge.mkTarget_eq A i s t c hc)⟩

end

end Erdos821.P3Edge
