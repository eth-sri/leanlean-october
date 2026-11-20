module

public import proofs.RAF.Concrete.PolymerCRS

@[expose] public section

namespace HordijkSteelThreshold
open RAF.Polymer RAF.Concrete

/-- Big-endian code, matching the source's mixed-radix concatenation. -/
def binaryWordCode (w : List Bool) : ℕ := Nat.ofDigits 2 (w.reverse.map Bool.toNat)

theorem binaryWordCode_lt (w : List Bool) : binaryWordCode w < 2^w.length := by
  simpa [binaryWordCode] using Nat.ofDigits_lt_base_pow_length
    (l := w.reverse.map Bool.toNat) Nat.one_lt_two (by aesop)

@[simp] theorem binaryWordCode_append (s t : List Bool) :
    binaryWordCode (s++t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  simp [binaryWordCode, List.reverse_append, Nat.ofDigits_append, add_comm, mul_comm]

theorem binaryWordCode_injective_length {s t : List Bool}
    (hlen : s.length = t.length) (hcode : binaryWordCode s = binaryWordCode t) : s = t := by
  simpa using (List.map_injective_iff.mpr (by simp : Function.Injective Bool.toNat))
    (Nat.ofDigits_inj_of_len_eq (by decide) (by simpa using hlen) (by aesop) (by aesop) hcode)

noncomputable def binaryListWordEquiv (m : ℕ) :
    {s : List Bool // s.length = m} ≃ RAF.Polymer.Word m :=
  Equiv.ofBijective
    (fun s => ⟨binaryWordCode s.val, by simpa only [s.property] using binaryWordCode_lt s.val⟩)
    (by
      change Function.Bijective (_ : List.Vector Bool m → _)
      apply (Fintype.bijective_iff_injective_and_card _).mpr
      exact ⟨fun s t h => Subtype.ext
        (binaryWordCode_injective_length (s.property.trans t.property.symm) (congrArg Fin.val h)), by simp⟩)

section
variable {n : ℕ}

noncomputable def moleculeWord (x : Molecule n) : List Bool :=
  ((binaryListWordEquiv (molLength x)).symm x.2).val

@[simp] theorem moleculeWord_length (x : Molecule n) :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv (molLength x)).symm x.2).property

@[simp] theorem binaryWordCode_moleculeWord (x : Molecule n) :
    binaryWordCode (moleculeWord x) = x.2.val :=
  congrArg Fin.val ((binaryListWordEquiv (molLength x)).apply_symm_apply x.2)

theorem moleculeWord_injective : Function.Injective (@moleculeWord n) :=
  fun _ _ h => molecule_ext (by grind [moleculeWord_length])
    (by grind [binaryWordCode_moleculeWord])

theorem reaction_words_append (r : Reaction n) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) = moleculeWord (reactionProduct r) := by
  apply binaryWordCode_injective_length
  · simpa using reaction_length_add r
  · simp only [binaryWordCode_append, binaryWordCode_moleculeWord, moleculeWord_length,
      molLength_reactionRight]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod r.2.1.val _

section
variable (s : List Bool) (hs : 0 < s.length) (hN : s.length ≤ n)

def sourceWordMolecule : Molecule n := moleculeOfCode hs hN ⟨binaryWordCode s,binaryWordCode_lt s⟩

@[simp] theorem sourceWordMolecule_length :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word : moleculeWord (sourceWordMolecule s hs hN) = s := by
  apply binaryWordCode_injective_length
  · simp
  · rw [binaryWordCode_moleculeWord]
    rfl

end

theorem source_append_split (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ n) :
    ∃ r : Reaction n,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  let x := sourceWordMolecule (u ++ v) (by simp; omega) (by simpa using hN)
  let r : Reaction n := ⟨x.1, x.2, ⟨u.length-1, by
    grind [molLength, sourceWordMolecule_length]⟩⟩
  have hp : moleculeWord (reactionProduct r) = u ++ v := show moleculeWord x = _ by simp [x]
  have hl : (moleculeWord (reactionLeft r)).length = u.length := by
    simpa [r, reactionLeftLength] using Nat.sub_add_cancel hu
  obtain ⟨h₁,h₂⟩ := List.append_inj ((reaction_words_append r).trans hp) hl
  grind

end

def lowerMolecule {n t : ℕ} (x : Molecule n) (h : molLength x ≤ t) : Molecule t :=
  ⟨⟨x.1.val, h⟩, x.2⟩

theorem lowerMolecule_inj {n t : ℕ} {x y : Molecule n} {hx : molLength x ≤ t} {hy : molLength y ≤ t}
    (h : lowerMolecule x hx = lowerMolecule y hy) : x = y :=
  by apply molecule_ext <;> grind [lowerMolecule]

theorem binaryFood_card_le_cutoff (n t : ℕ) : (binaryFood n t).card ≤ Fintype.card (Molecule t) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (fun x : ↥(binaryFood n t) => lowerMolecule x.val (by grind [binaryFood]))
    (fun _ _ h => Subtype.ext (lowerMolecule_inj h))

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

end HordijkSteelThreshold
