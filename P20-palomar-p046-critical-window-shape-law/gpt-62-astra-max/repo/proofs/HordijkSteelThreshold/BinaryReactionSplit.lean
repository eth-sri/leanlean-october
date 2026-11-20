module
public import proofs.RAF.Concrete.PolymerCRS

/-! Binary word encoding and its compatibility with physical concatenation and cleavage. -/

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete
variable {N : ℕ}

/-- The actual big-endian bit pattern, with leading zeros retained by the width. -/
def binaryWordCode (s : List Bool) := (BitVec.ofBoolListBE s).toNat

@[simp] theorem binaryWordCode_append (s t : List Bool) :
    binaryWordCode (s ++ t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  unfold binaryWordCode
  induction s with
  | nil => simp [BitVec.ofBoolListBE]
  | cons b s ih => simp only [List.cons_append,BitVec.ofBoolListBE,BitVec.toNat_cons',Nat.shiftLeft_eq,List.length_append,pow_add,ih]; ring

theorem binaryWordCode_injective_length {s t : List Bool}
    (hl : s.length = t.length) (hc : binaryWordCode s = binaryWordCode t) : s = t := by
  have he : (BitVec.ofBoolListBE s).cast hl = BitVec.ofBoolListBE t := BitVec.eq_of_toNat_eq hc
  apply List.ext_getElem hl; intro i hi hi'
  simpa [List.getD_eq_getElem?_getD,hi,hi'] using congrArg (fun x => x.getMsbD i) he

def moleculeWord (x : Molecule N) : List Bool :=
  List.ofFn (fun i : Fin (molLength x) => (BitVec.ofFin x.2).getMsbD i.val)

@[simp] theorem moleculeWord_length (x : Molecule N) :
    (moleculeWord x).length = molLength x :=
  List.length_ofFn

@[simp] theorem binaryWordCode_moleculeWord (x : Molecule N) :
    binaryWordCode (moleculeWord x) = x.2.val := by
  have he : (BitVec.ofBoolListBE (moleculeWord x)).cast (moleculeWord_length _) = BitVec.ofFin x.2 := by
    apply BitVec.eq_of_getMsbD_eq; intro i hi
    rw [BitVec.getMsbD_cast,BitVec.getMsbD_ofBoolListBE]
    simp [moleculeWord,List.getD_eq_getElem?_getD,hi]
    rfl
  exact congrArg BitVec.toNat he

theorem moleculeWord_injective : Function.Injective (@moleculeWord N) :=
  fun _ _ h => molecule_ext (by simpa using congrArg List.length h) (by simpa using congrArg binaryWordCode h)

@[simp] theorem moleculeWord_nonempty (x : Molecule N) : moleculeWord x ≠ [] := by
  grind [moleculeWord_length,molLength]

theorem moleculeWord_cap (x : Molecule N) : (moleculeWord x).length ≤ N := by
  rw [moleculeWord_length]
  simp [molLength]

/-- Recombining the decoded quotient and remainder recovers the literal product. -/
theorem reaction_words_append (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) = moleculeWord (reactionProduct r) := by
  apply binaryWordCode_injective_length
  · simp [moleculeWord_length,reaction_length_add]
  · simp only [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,molLength_reactionRight]
    exact Nat.div_add_mod' ..

variable (s : List Bool) (hs : s ≠ []) (hN : s.length ≤ N)

def sourceWordMolecule : Molecule N := moleculeOfCode (List.length_pos_iff.mpr hs) hN (BitVec.ofBoolListBE s).toFin

@[simp] theorem sourceWordMolecule_length :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word : moleculeWord (sourceWordMolecule s hs hN) = s :=
  binaryWordCode_injective_length (by simp) (binaryWordCode_moleculeWord _)

theorem source_append_split (u v : List Bool)
    (hu : u ≠ []) (hv : v ≠ []) (hN : (u++v).length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  have := List.length_pos_iff.mpr hu; have := List.length_pos_iff.mpr hv
  let x := sourceWordMolecule (u ++ v) (by grind) hN
  have hlen : molLength x = u.length+v.length := by simp [x]
  let r : Reaction N := ⟨x.1,x.2,⟨u.length-1,by dsimp [molLength] at hlen; omega⟩⟩
  have hp : moleculeWord (reactionProduct r) = u ++ v := by change moleculeWord x = _; simp [x]
  have he := (reaction_words_append r).trans hp
  have hl : (moleculeWord (reactionLeft r)).length = u.length := by
    rw [moleculeWord_length,molLength_reactionLeft]; change u.length-1+1 = _; omega
  exact ⟨r,List.append_inj_left he hl,List.append_inj_right he hl,hp⟩

end HordijkSteelThreshold
