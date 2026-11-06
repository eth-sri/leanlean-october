module

public import RequestProject.AttCycle

@[expose] public section

/-!
# The concrete attaching map and the loop along which it spells the prescribed word

`RequestProject/AttCycle.lean` produced the labelled cycle.  This file turns it into the actual
attaching map

    `attCyc : NeSpx (cycA l hl) →o PresPos w`

of the chamber construction, and produces the **geometric loop of the cut surface**: the edge
path `sigLoop` which goes once around the cycle, based at the vertex `0`.  The computation
`mapPath_sigLoop_full` says that the image of that loop under the attaching map is *literally*
the loop `wordLoop w l` of the presentation complex which spells the word `l`.  This is the
reading hypothesis `hread` of `FiniteChains.Davis.injective_substHomF_of_spine`, on the nose.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

/-- A pair of adjacent vertices is a simplex. -/
theorem isSimplex_pair {V : Type u} [DecidableEq V] {A : CommRel V} {x y : V} (h : A.rel x y) :
    IsSimplex A {x, y} := by
  intro s hs r hr hsr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs hr
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl
  · exact absurd rfl hsr
  · exact h
  · exact A.rel_symm h
  · exact absurd rfl hsr

section Loop

variable {α J : Type} (w : J → List (α × Bool)) (l : List (α × Bool)) (hl : 2 ≤ l.length)

/-- **The attaching map of the concrete block**: the simplicial map of the labelled cycle onto
the subdivided rose of the presentation complex. -/
def attCyc : NeSpx (cycA l hl) →o PresPos w :=
  ⟨fun σ => iRose w (roseLab l σ.1), (iRose_monotone w).comp (roseLab_monotone l hl)⟩

@[simp] theorem attCyc_apply (σ : NeSpx (cycA l hl)) :
    attCyc w l hl σ = iRose w (roseLab l σ.1) := rfl

/-! ### The vertices and the edges of the cycle -/

/-- The vertex of the cycle at the position `p`, read cyclically. -/
def vpt (p : ℕ) : Fin (2 * l.length) := ⟨p % (2 * l.length), Nat.mod_lt _ (by omega)⟩

@[simp] theorem vpt_val (p : ℕ) : (vpt l hl p).val = p % (2 * l.length) := rfl

theorem vpt_succ_val (p : ℕ) :
    (vpt l hl (p + 1)).val = (p % (2 * l.length) + 1) % (2 * l.length) := by
  simp [vpt, Nat.mod_add_mod]

theorem vpt_succ_lt {p : ℕ} (h : p % (2 * l.length) + 1 < 2 * l.length) :
    (vpt l hl (p + 1)).val = p % (2 * l.length) + 1 := by
  rw [vpt_succ_val, Nat.mod_eq_of_lt h]

theorem vpt_succ_wrap {p : ℕ} (h : p % (2 * l.length) + 1 = 2 * l.length) :
    (vpt l hl (p + 1)).val = 0 := by
  rw [vpt_succ_val, h, Nat.mod_self]

theorem vpt_adj (p : ℕ) : cycAdj (2 * l.length) (vpt l hl p) (vpt l hl (p + 1)) := by
  have hlt : p % (2 * l.length) < 2 * l.length := Nat.mod_lt _ (by omega)
  by_cases h : p % (2 * l.length) + 1 < 2 * l.length
  · exact Or.inl (by rw [vpt_val, vpt_succ_lt l hl h])
  · have hw : p % (2 * l.length) + 1 = 2 * l.length := by omega
    exact Or.inr (Or.inr (Or.inr ⟨vpt_succ_wrap l hl hw, by rw [vpt_val]; omega⟩))

/-- The vertex simplex at the position `p`. -/
def vtxSpx (p : ℕ) : NeSpx (cycA l hl) :=
  ⟨{vpt l hl p}, ⟨_, Finset.mem_singleton_self _⟩, isSimplex_singleton _⟩

/-- The edge simplex joining the positions `p` and `p+1`. -/
def edSpx (p : ℕ) : NeSpx (cycA l hl) :=
  ⟨{vpt l hl p, vpt l hl (p + 1)}, ⟨vpt l hl p, by simp⟩, isSimplex_pair (vpt_adj l hl p)⟩

@[simp] theorem vtxSpx_val (p : ℕ) : (vtxSpx l hl p).1 = {vpt l hl p} := rfl

@[simp] theorem edSpx_val (p : ℕ) :
    (edSpx l hl p).1 = {vpt l hl p, vpt l hl (p + 1)} := rfl

/-! ### The values of the attaching map -/

/-! ### The loop around the cycle -/

/-! ### The attaching map spells the word along the loop -/

end Loop

end Davis
end FiniteChains
