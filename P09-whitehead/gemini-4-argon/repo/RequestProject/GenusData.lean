module

public import RequestProject.SurfaceReading
public import RequestProject.BlockSurfaceFilling

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb PresModel Cell

section

variable {α : Type} (a b : ℕ → α)

def sLet (k : ℕ) : α × Bool :=
  if k % 4 = 0 then (a (k / 4), true)
  else if k % 4 = 1 then (b (k / 4), true)
  else if k % 4 = 2 then (a (k / 4), false)
  else (b (k / 4), false)

def surfWord : ℕ → List (α × Bool)
  | 0 => []
  | n + 1 => surfWord n ++ [(a n, true), (b n, true), (a n, false), (b n, false)]

@[simp] theorem surfWord_length (n : ℕ) : (surfWord a b n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [surfWord, ih]; omega

theorem surfWord_getElem? (n k : ℕ) (hk : k < 4 * n) :
    (surfWord a b n)[k]? = some (sLet a b k) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge k (4 * n) with hlt | hge
      · rw [surfWord, List.getElem?_append_left (by rw [surfWord_length]; exact hlt)]
        exact ih hlt
      · rw [surfWord, List.getElem?_append_right (by rw [surfWord_length]; omega), surfWord_length]
        have hdiv : k / 4 = n := by omega
        have hk4 : k - 4 * n < 4 := by omega
        interval_cases h : (k - 4 * n)
        · have hmod : k % 4 = 0 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 1 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 2 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 3 := by omega
          simp [sLet, hmod, hdiv]

def genLw : ℕ × Bool → List (α × Bool) := fun x => if x.2 then [(b x.1, true)] else [(a x.1, true)]

def genPairs (n : ℕ) : List ((ℕ × Bool) × (ℕ × Bool)) :=
  (List.range n).map (fun h => ((h, false), (h, true)))

theorem commWord_append {ι G : Type} [Group G] (f : ι → G) (l l' : List (ι × ι)) :
    commWord f (l ++ l') = commWord f l * commWord f l' := by
  simp [commWord, List.prod_append]

theorem mk_surfWord (n : ℕ) :
    FreeGroup.mk (surfWord a b n)
      = commWord (fun x => FreeGroup.mk (genLw a b x)) (genPairs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show FreeGroup.mk (surfWord a b n ++
        [(a n, true), (b n, true), (a n, false), (b n, false)]) = _
      rw [← FreeGroup.mul_mk, ih, show genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] by
        simp [genPairs, List.range_succ], commWord_append]
      congr 1

end

variable {α : Type} (a b : ℕ → α) (q : ℕ) [NeZero q]

instance neZero_eight_mul : NeZero (8 * q) := ⟨by have := Nat.pos_of_neZero q; omega⟩

abbrev KVtx : Type := Option (Fin q × Bool)

abbrev IEdg : Type := Fin q × Bool × Bool

def gvc (p : Fin (8 * q)) : KVtx q :=
  if p.val % 2 = 0 then none
  else some (⟨p.val / 2 / 4, by omega⟩, decide (p.val / 2 % 4 % 2 = 1))

def gec (p : Fin (8 * q)) : IEdg q :=
  (⟨p.val / 2 / 4, by omega⟩, decide (p.val / 2 % 4 % 2 = 1),
    xor (decide (p.val % 2 = 1)) (decide (2 ≤ p.val / 2 % 4)))

def gvlab : KVtx q → Rose α
  | none => Rose.base
  | some (h, i) => Rose.mid (if i then b h.val else a h.val)

def gelb : IEdg q → Rose α := fun x => Rose.edg (if x.2.1 then b x.1.val else a x.1.val) x.2.2

omit [NeZero q] in
theorem genus_hM : 8 * q = 2 * (surfWord a b q).length := by
  rw [surfWord_length]; omega

omit [NeZero q] in
theorem genus_hvlab (p : Fin (8 * q)) :
    gvlab a b q (gvc q p) = vertLab (surfWord a b q) p.val := by
  have hlt := p.isLt
  set k := p.val
  by_cases hpar : k % 2 = 0
  · rw [gvc, if_pos hpar, vertLab_of_even hpar]; rfl
  · rw [gvc, if_neg hpar, vertLab_of_odd (by omega) (surfWord_getElem? a b q (k / 2) (by omega))]
    have hr : k / 2 % 4 = 0 ∨ k / 2 % 4 = 1 ∨ k / 2 % 4 = 2 ∨ k / 2 % 4 = 3 := by omega
    show Rose.mid (if (decide (k / 2 % 4 % 2 = 1) : Bool) then b (k / 2 / 4) else a (k / 2 / 4))
      = Rose.mid (sLet a b (k / 2)).1
    rcases hr with h | h | h | h <;> simp [sLet, h]

omit [NeZero q] in
theorem genus_helb (p : Fin (8 * q)) :
    gelb a b q (gec q p) = edgeLab (surfWord a b q) p.val := by
  have hlt := p.isLt
  set k := p.val
  rw [edgeLab_eq (surfWord_getElem? a b q (k / 2) (by omega))]
  have hr : k / 2 % 4 = 0 ∨ k / 2 % 4 = 1 ∨ k / 2 % 4 = 2 ∨ k / 2 % 4 = 3 := by omega
  have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
  show Rose.edg (if (decide (k / 2 % 4 % 2 = 1) : Bool) then b (k / 2 / 4) else a (k / 2 / 4))
      (xor (decide (k % 2 = 1)) (decide (2 ≤ k / 2 % 4)))
    = Rose.edg (sLet a b (k / 2)).1 (if k % 2 = 0 then !(sLet a b (k / 2)).2
        else (sLet a b (k / 2)).2)
  rcases hr with h | h | h | h <;> rcases hpar with h2 | h2 <;> simp [sLet, h, h2]

theorem genus_compat : Compat (gvc q) (gec q) := by
  have hstep (i j : Fin (8 * q)) (h1 : i.val / 2 / 4 = j.val / 2 / 4)
      (h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2) (hpar : i.val % 2 ≠ j.val % 2) :
      gvc q i = gvc q (j + 1) := by
    have hj := j.isLt
    have hsuccj : (j + 1).val = (j.val + 1) % (8 * q) := fin_succ_val j
    rcases Nat.lt_or_ge (i.val % 2) 1 with hI | hI
    · have hJ1 : (j + 1).val % 2 = 0 := by
        rw [hsuccj]
        rcases Nat.lt_or_ge (j.val + 1) (8 * q) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · rw [show j.val + 1 = 8 * q by omega, Nat.mod_self]
      rw [gvc, gvc, if_pos (by omega), if_pos hJ1]
    · have hJ1v : (j + 1).val = j.val + 1 := by rw [hsuccj, Nat.mod_eq_of_lt (by omega)]
      rw [gvc, gvc, if_neg (by omega), if_neg (by omega)]
      simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide]
      omega
  intro i j hij
  have h1 : i.val / 2 / 4 = j.val / 2 / 4 := congrArg Fin.val (congrArg Prod.fst hij)
  have h2 : (decide (i.val / 2 % 4 % 2 = 1) : Bool) = decide (j.val / 2 % 4 % 2 = 1) :=
    congrArg (fun x => x.2.1) hij
  have h3 : xor (decide (i.val % 2 = 1)) (decide (2 ≤ i.val / 2 % 4))
      = xor (decide (j.val % 2 = 1)) (decide (2 ≤ j.val / 2 % 4)) :=
    congrArg (fun x => x.2.2) hij
  have h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2 := by
    by_cases hA : i.val / 2 % 4 % 2 = 1 <;> by_cases hB : j.val / 2 % 4 % 2 = 1 <;>
      simp [hA, hB] at h2 ⊢ <;> omega
  by_cases hsame : i.val / 2 % 4 = j.val / 2 % 4
  · have hpar : i.val % 2 = j.val % 2 := by
      rw [hsame] at h3
      by_cases hA : i.val % 2 = 1 <;> by_cases hB : j.val % 2 = 1 <;>
        simp [hA, hB] at h3 ⊢ <;> omega
    cases Fin.ext (by omega : i.val = j.val)
    exact .inl ⟨rfl, rfl⟩
  · have hpar : i.val % 2 ≠ j.val % 2 := fun hp => by
      rw [hp] at h3
      by_cases hA : 2 ≤ i.val / 2 % 4 <;> by_cases hB : 2 ≤ j.val / 2 % 4 <;>
        simp [hA, hB] at h3 <;> omega
    exact .inr ⟨hstep i j h1 h2' hpar, (hstep j i h1.symm h2'.symm hpar.symm).symm⟩

end FiniteChains.Davis
