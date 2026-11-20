module
public import AnalyticESC.Defs

@[expose] public section
namespace AnalyticESC
lemma block_add {N} (ω : Address N) (n k : ℕ) : block (n+k) ω = block k ω ++ block n (shift k ω) := by
  rw [add_comm n k]; unfold block; rw [List.ofFn_add]
  simp [pref,add_comm k]

lemma depth_pos {N n} {v w : Block N n} (h : v ≠ w) : 0 < n :=
  Nat.pos_of_ne_zero fun e => h (by subst n; exact Subsingleton.elim ..)

/-- Complete a block by repeating a letter beyond its end. -/
def pad {N} (d : Fin N) (a : Letters N) (n : ℕ) := a[n]?.getD d

lemma block_pad {N} (d : Fin N) (a : Letters N) {n} (h : a.length ≤ n) : block n (pad d a) = a ++ List.replicate (n-a.length) d := by
  apply List.ext_getElem (by simp [h]); intro j h1 h2
  simp [block,pref,pad,List.getElem_append]; split <;> simp_all

lemma block_pad_length {N} (d : Fin N) (a : Letters N) : block a.length (pad d a) = a := by simp [block_pad _ _ le_rfl]

lemma diff_blocks {N m} {v w : Address N} (h : block m v ≠ block m w) : ∃ n : ℕ, (n:ℕ∞) < m ∧ v n ≠ w n := by
  by_contra! H; apply h; exact congrArg List.ofFn (funext fun i => H i (by exact_mod_cast i.isLt))

lemma first_difference {N} {v w : Address N} {l : ℕ∞} (h : ∃ n : ℕ, (n:ℕ∞) < l ∧ v n ≠ w n) :
    ∃ m : ℕ, (m:ℕ∞) < l ∧ block m v = block m w ∧ v m ≠ w m := by
  obtain ⟨hl,hm⟩ := Nat.find_spec h
  refine ⟨Nat.find h,hl,congrArg List.ofFn (funext fun i => ?_),hm⟩
  exact not_ne_iff.mp fun he => Nat.find_min h i.isLt ⟨lt_trans (by exact_mod_cast i.isLt) hl,he⟩

end AnalyticESC
