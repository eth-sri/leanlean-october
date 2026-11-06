import Mathlib.Tactic

import Mathlib

/-!
# The chain map induced by a collapse

`RequestProject/Collapse.lean` proves the combinatorial half of Lemma 3.3 (ii) of the paper:
the three-cells of the truncated complex `M_q` disappear under elementary collapses, leaving
a two-dimensional spine.  Two further steps of the block argument are chain level statements
about that collapse:

* Lemma 3.3 (iii) — *the inclusion sends `[Σ_q]` to zero in `H₂(M_q)`* — is used by the
  capping argument in the form: the cellular chain of the cut surface **is the zero chain of
  the spine**;
* Lemma 3.3 (i) — *the cone model `C_q` is aspherical* — is used in the form: in the
  collapsed complex every two-cycle is a multiple of the boundary of the single remaining
  three-cell.

Both follow from the chain map of the collapse, which is what this file builds, over an
arbitrary ring of coefficients `R` (for the second application `R` is the group ring of the
fundamental group and the chains are those of the universal cover).

An elementary collapse removes a top cell `t` together with a free face `f` of it, and
induces on chains the Whitehead retraction

  `retr t f x = x - (x f)·(d t f)⁻¹·(d t)`,

where `d t` is the cellular boundary of `t` and `d t f` is a unit.  It kills the
`f`-coordinate, it kills `d t`, and it fixes the boundary of every top cell which does not
contain `f` — and a top cell removed later than `t` does not contain `f`, precisely because
`f` was free for `t` at the moment of the collapse.  Composing the retractions of a whole
collapse therefore gives a map `cmap` which

* kills the boundary of every collapsed top cell (`CollapseChain.cmap_bdry_eq_zero`), hence
  kills every combination of such boundaries (`CollapseChain.cmap_sum_eq_zero`),
* vanishes on every collapsed face (`CollapseChain.cmap_apply_eq_zero`), so its values are
  genuinely chains of the spine, and
* fixes every chain of the spine (`CollapseChain.cmap_of_forall_eq_zero`).

Consequently a two-chain which bounds becomes the zero chain of the spine
(`CollapseChain.cmap_eq_zero_of_isBoundary`) — the step "in a two-complex a homologically
zero two-cycle is the zero cellular chain" of the paper's proof of (B3) — and, if all
three-cells but one are collapsed away, every two-cycle of the spine is a multiple of the
boundary of the surviving three-cell
(`CollapseChain.exists_mul_bdry_of_cycles_bound`), which is the asphericity hypothesis of the
cone model in the form in which (B3) uses it.
-/

namespace FiniteChains.CollapseChain


variable {T F R : Type*} [Ring R]

/-- The Whitehead retraction of an elementary collapse removing the top cell `t` across its
free face `f`: subtract the multiple of the boundary `d t` which kills the `f`-coordinate. -/
noncomputable def retr (d : T → F → R) (t : T) (f : F) (x : F → R)  :=
  fun g => x g - x f * Ring.inverse (d t f) * d t g

/-- The chain map of a sequence of elementary collapses: the composite of the retractions of
its steps, each step being recorded as the removed top cell together with the face it is
collapsed across. -/
noncomputable def cmap (d : T → F → R) : List (T × F) → (F → R) → (F → R)
  | [], x => x
  | (t, f) :: l, x => cmap d l (retr d t f x)

/-- The hypotheses under which a list of (top cell, face) pairs is a sequence of elementary
collapses on the chain level: the face is a *unit* face of the cell it is collapsed across,
and it is *free*, i.e. no cell removed later meets it. -/
def IsChainCollapse (d : T → F → R) : List (T × F) → Prop
  | [] => True
  | (t, f) :: l => IsUnit (d t f) ∧ (∀ p ∈ l, d p.1 f = 0) ∧ IsChainCollapse d l

variable {d : T → F → R}

@[simp] theorem retr_zero (t : T) (f : F) : retr d t f 0 = 0 := by
  funext g; simp [retr]

theorem retr_add (t : T) (f : F) (x y : F → R) :
    retr d t f (x + y) = retr d t f x + retr d t f y := by
  funext g
  simp [retr, add_mul]
  abel

theorem retr_leftMul (a : R) (t : T) (f : F) (x : F → R) :
    retr d t f (fun g => a * x g) = fun g => a * retr d t f x g := by
  funext g
  simp [retr, mul_sub, mul_assoc]

variable (l : List (T × F))
@[simp] theorem cmap_zero  : cmap d l 0 = 0 := by
  induction l <;> simp_all [cmap]

theorem cmap_add  (x y : F → R) :
    cmap d l (x + y) = cmap d l x + cmap d l y := by
  induction l generalizing x y <;> simp_all [cmap, retr_add]

theorem cmap_leftMul  (a : R) (x : F → R) :
    cmap d l (fun g => a * x g) = fun g => a * cmap d l x g := by
  induction l generalizing x <;> aesop (add simp [cmap, retr_leftMul])

/-- The retraction of an elementary collapse kills the boundary of the cell it removes. -/
theorem retr_self {t : T} {f : F} (h : IsUnit (d t f)) : retr d t f (d t) = 0 := by
  funext g
  simp [retr, Ring.mul_inverse_cancel _ h]

/-- The retraction of an elementary collapse fixes the boundary of a cell which does not
meet the face it is collapsed across. -/
theorem retr_of_notMem {t t' : T} {f : F} (h : d t' f = 0) : retr d t f (d t') = d t' := by
  funext g; simp [retr, h]

variable {l : List (T × F)}
  (hl : IsChainCollapse d l)
include hl in
/-- **The chain map of a collapse kills the boundary of every collapsed cell.** -/
theorem cmap_bdry_eq_zero   :
    ∀ p ∈ l, cmap d l (d p.1) = 0 := by
  induction l with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      obtain ⟨hunit, hfree, hrest⟩ := hl
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hrl
      · simp_all [cmap, retr_self]
      · simp_all only [cmap, retr_of_notMem]

/-- The chain map of a collapse, applied to a combination of boundaries of top cells. -/
theorem cmap_sum  [DecidableEq T] (s : Finset T) (c : T → R) :
    cmap d l (fun g => ∑ t ∈ s, c t * d t g) = fun g => ∑ t ∈ s, c t * cmap d l (d t) g := by
  classical
  induction s using Finset.induction with
  | empty =>
      classical solve_by_elim (transparency := .default) [FiniteChains.CollapseChain.cmap_zero]
  | insert t s ht ih =>
      have hsplit : (fun g => ∑ u ∈ insert t s, c u * d u g)
          = (fun g => c t * d t g) + (fun g => ∑ u ∈ s, c u * d u g) := by
        aesop
      rw [hsplit, cmap_add, cmap_leftMul, ih]
      funext g
      simp only [Pi.add_apply]
      rw [Finset.sum_insert ht]

include hl in
/-- **The chain map of a collapse kills every combination of boundaries of collapsed
cells.** -/
theorem cmap_sum_eq_zero   [DecidableEq T]
    (s : Finset T) (c : T → R) (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l) :
    cmap d l (fun g => ∑ t ∈ s, c t * d t g) = 0 := by
  rw [cmap_sum]
  funext g
  refine Finset.sum_eq_zero fun t htt => ?_
  obtain ⟨f, hf⟩ := hs t htt
  rw [cmap_bdry_eq_zero hl (t, f) hf]
  simp

/-- **The chain map of a collapse fixes the chains of the spine**: a chain which already
vanishes on every collapsed face is left unchanged. -/
theorem cmap_of_forall_eq_zero  (x : F → R) (hx : ∀ p ∈ l, x p.2 = 0) :
    cmap d l x = x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      have hf  := hx (t, f) List.mem_cons_self
      have hretr : retr d t f x = x := by
        funext g; simp [retr, hf]
      show cmap d l (retr d t f x) = x
      rw [hretr]
      exact ih x fun q hq => hx q (List.mem_cons_of_mem _ hq)

include hl in
/-- **A boundary collapses to the zero chain of the spine.**  If every top cell is collapsed
away, then the cellular chain obtained from a boundary is zero: this is the step "in a
two-complex a homologically zero two-cycle is the zero cellular chain". -/
theorem cmap_eq_zero_of_isBoundary  
    [DecidableEq T] {s : Finset T} {c : T → R} (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l)
    {x : F → R} (hx : ∀ g, x g = ∑ t ∈ s, c t * d t g) :
    cmap d l x = 0 := by
  have hxe  := funext hx
  rw [hxe]
  exact cmap_sum_eq_zero hl s c hs

/-! ### The surviving three-cell -/

/-! ### Chain complexes presented by linear maps -/

end FiniteChains.CollapseChain

