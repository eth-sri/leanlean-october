module
public import ADR11.Coalescent.Factorization
@[expose] public section
namespace ADR11.Computation
open Finset

def decC (n c : ℕ) : Finset (Fin n) := univ.filter fun i => c.testBit i

def decF (n : ℕ) (l : List ℕ) : Family (Fin n) := (l.map (decC n)).toFinset

def flatMapO {α β : Type*} (f : α → Option (Multiset β)) (s : Multiset α) : Option (Multiset β) :=
  @Multiset.sum (WithBot (Multiset β)) _ (s.map f)

set_option backward.isDefEq.respectTransparency false in
theorem sum_flatMapO {α β : Type*} {f : α → Option (Multiset β)} {l : Multiset α} {M : Multiset β}
    (h : flatMapO f l = some M) (w : β → ℝ) (v : α → ℝ)
    (hv : ∀ a ∈ l, ∀ x, f a = some x → (x.map w).sum = v a) :
    (M.map w).sum = (l.map v).sum := by
  induction l using Multiset.induction generalizing M with
  | empty => cases h; rfl
  | cons a l ih =>
    rw [flatMapO, Multiset.map_cons, Multiset.sum_cons] at h
    obtain ⟨x, y, hx, hy, hM⟩ := WithBot.add_eq_coe.1 h
    subst hM
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_cons, Multiset.sum_cons]
    rw [hv a (by simp) x hx.symm, ih hy.symm (fun b hb => hv b (Multiset.mem_cons_of_mem hb))]

end ADR11.Computation
