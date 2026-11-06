
import proofs.RAF.Polymer.Words




namespace HordijkSteelThreshold

/-- Big-endian code, matching the source's mixed-radix concatenation. -/
def binaryWordCode : List Bool → ℕ
  | [] => 0
  | b :: s => (if b then 2 ^ s.length else 0) + binaryWordCode s

theorem binaryWordCode_lt (s : List Bool) : binaryWordCode s < 2 ^ s.length := by
  induction s <;> grind [binaryWordCode]

variable (s t : List Bool)

theorem binaryWordCode_append  :
    binaryWordCode (s ++ t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  induction s <;> grind [binaryWordCode]

def listWord (s : List Bool) : RAF.Polymer.Word s.length :=
  ⟨binaryWordCode s, binaryWordCode_lt s⟩

theorem binaryWordCode_append_div  :
    binaryWordCode (s ++ t) / 2 ^ t.length = binaryWordCode s := by
  rw [binaryWordCode_append, Nat.mul_comm, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (binaryWordCode_lt t), Nat.add_zero]

theorem binaryWordCode_append_mod  :
    binaryWordCode (s ++ t) % 2 ^ t.length = binaryWordCode t := by
  rw [binaryWordCode_append, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (binaryWordCode_lt t)]

/-- Length together with code uniquely determines the binary word. -/
theorem binaryWordCode_injective_length {s t : List Bool}
    (hlen : s.length = t.length) (hcode : binaryWordCode s = binaryWordCode t) : s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons b s ih =>
    cases t with
    | nil => simp_all
    | cons c t =>
      grind [binaryWordCode, binaryWordCode_lt]

/-- A length-preserving bijection with the source's actual fixed-length
word type. This prevents dropping leading zeros or losing source words. -/
noncomputable def binaryListWordEquiv (m : ℕ) :
    List.Vector Bool m ≃ RAF.Polymer.Word m :=
  Equiv.ofBijective
    (fun s => ⟨binaryWordCode s.val, by simpa only [s.property] using binaryWordCode_lt s.val⟩)
    (by
      rw [Fintype.bijective_iff_injective_and_card]
      constructor
      · intro s t h
        apply Subtype.ext
        exact binaryWordCode_injective_length (s.property.trans t.property.symm)
          (congrArg Fin.val h)
      · simp)

end HordijkSteelThreshold
