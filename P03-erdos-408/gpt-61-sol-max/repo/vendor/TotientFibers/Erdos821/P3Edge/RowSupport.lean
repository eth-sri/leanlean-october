module
public import Mathlib.Tactic

public import Erdos821.S2.MemoryEdge
public import Erdos821.S2.EdgeTasks

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def targetSmall (A : Model F P J m) {n } (i : Fin n)
    (s ) (c : EdgeChoice A s)  :=
  translateSmallResidues
    (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
    (permuteActive c.1 s).1

def targetMem (A : Model F P J m) {n } (i : Fin n)
    (s ) (c : EdgeChoice A s)
    (g : P.BigGroup)  :=
  translateMemory
    (edgeDelta A (A.pattern c.2.2.1) (edgeForward i) (permuteActive c.1 s).2.1 c.2.2.2.1)
    (deleteMemoryIndices ((permuteActive c.1 s).2.2 g) (retrievedIndices c.2.2.2.2 g) +
      storedMemory ((permuteActive c.1 s).2.1 (g : P.Group)) (c.2.2.2.2.1 g))

section
variable (A : Model F P J m) {n : ℕ} (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) (h : edgeChoiceValid A .all i s t c)
include A n i s t c h

lemma valid_target_small      
       
      :
    t.1 = targetSmall A i s c := Eq.mp (congrArg (fun _a => _a = Erdos821.S2Core.translateSmallResidues (Erdos821.S2Core.edgeDelta A (A.pattern c.2.2.1) (Erdos821.S2Core.edgeForward i) (Erdos821.S2Core.permuteActive c.1 s).2.1 c.2.2.2.1) (Erdos821.S2Core.permuteActive c.1 s).1) rfl) h.left.right.right.right.right.left

lemma valid_target_mem      
       
       g  :
    t.2.2 g = targetMem A i s c g := by
  have h2 : rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
      (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 := by
    simpa [edgeChoiceValid] using h.1
  have hmem := ((h2.2.2.2.2.2 g).2.2.2.2)
  assumption

end

end Erdos821.P3Edge
