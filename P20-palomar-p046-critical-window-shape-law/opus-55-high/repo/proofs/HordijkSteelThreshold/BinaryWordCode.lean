module

public import proofs.RAF.Polymer.Words

@[expose] public section

namespace HordijkSteelThreshold

/-- Big-endian code, matching the source's mixed-radix concatenation. -/
def binaryWordCode : List Bool → ℕ
  | [] => 0
  | b :: s => (if b then 2 ^ s.length else 0) + binaryWordCode s

theorem binaryWordCode_lt (s : List Bool) : binaryWordCode s < 2 ^ s.length := by
  induction s with
  | nil => positivity
  | cons b s ih =>
    cases b <;> simp only [binaryWordCode, Bool.false_eq_true, ite_false,
      ite_true, List.length_cons] <;> omega

variable (s t : List Bool)

theorem binaryWordCode_append  :
    binaryWordCode (s ++ t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  induction s with
  | nil => aesop
  | cons b s ih =>
    cases b <;> simp [binaryWordCode, ih, pow_add, Nat.add_mul, Nat.add_assoc]

def listWord (s : List Bool) : RAF.Polymer.Word s.length :=
  ⟨binaryWordCode s, binaryWordCode_lt s⟩

theorem binaryWordCode_append_div  :
    binaryWordCode (s ++ t) / 2 ^ t.length = binaryWordCode s := by
  rw [binaryWordCode_append, Nat.mul_comm, Nat.mul_add_div $ by positivity,
    Nat.div_eq_of_lt $ binaryWordCode_lt t, Nat.add_zero]

theorem binaryWordCode_append_mod  :
    binaryWordCode (s ++ t) % 2 ^ t.length = binaryWordCode t := by
  rw [binaryWordCode_append, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt $ binaryWordCode_lt t]


/-- Length together with code uniquely determines the binary word. -/
theorem binaryWordCode_injective_length {s t : List Bool}
    (hlen : s.length = t.length) (hcode : binaryWordCode s = binaryWordCode t) : s = t := by
  induction s generalizing t with
  | nil => grind
  | cons b s ih =>
    cases t with
    | nil => simp_all
    | cons c t =>
      have hst : s.length = t.length := by simp_all
      have hs := binaryWordCode_lt s
      have ht := binaryWordCode_lt t
      rw [← hst] at ht
      cases b <;> cases c <;> simp only [binaryWordCode, Bool.false_eq_true,
        ite_false, ite_true, ← hst] at hcode
      · grind
      · omega
      · omega
      grind

theorem exists_binaryWordCode (m k : ℕ) (hk : k < 2 ^ m) :
    ∃ s : List Bool, s.length = m ∧ binaryWordCode s = k := by
  induction m generalizing k with
  | zero =>
    aesop
  | succ m ih =>
    by_cases hlow : k < 2 ^ m
    · obtain ⟨s, hs, hc⟩ := ih k hlow
      refine ⟨false :: s, by simp_all, ?_⟩
      simpa [binaryWordCode] using hc
    · have ht : k - 2 ^ m < 2 ^ m := by
        omega
      obtain ⟨s, hs, hc⟩ := ih (k - 2 ^ m) ht
      refine ⟨true :: s, by simp_all, ?_⟩
      simp only [binaryWordCode, ite_true, hs]
      omega

/-- A length-preserving bijection with the source's actual fixed-length
word type. This prevents dropping leading zeros or losing source words. -/
noncomputable def binaryListWordEquiv (m : ℕ) :
    {s : List Bool // s.length = m} ≃ RAF.Polymer.Word m :=
  Equiv.ofBijective
    (fun s => ⟨binaryWordCode s.val, by simpa only [s.property] using binaryWordCode_lt s.val⟩)
    (by
      constructor
      · intro s t h
        apply Subtype.ext
        exact binaryWordCode_injective_length (s.property.trans t.property.symm)
          (congrArg Fin.val h)
      · intro k
        obtain ⟨s, hs, hc⟩ := exists_binaryWordCode m k.val k.isLt
        exact ⟨⟨s, hs⟩, Fin.ext hc⟩)

end HordijkSteelThreshold
