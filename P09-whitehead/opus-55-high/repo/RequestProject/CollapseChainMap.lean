import Mathlib
noncomputable section


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
def retr (d : T → F → R) (t : T) (f : F) (x : F → R) : F → R :=
  fun g => x g - x f * Ring.inverse (d t f) * d t g

/-- The chain map of a sequence of elementary collapses: the composite of the retractions of
its steps, each step being recorded as the removed top cell together with the face it is
collapsed across. -/
def cmap (d : T → F → R) : List (T × F) → (F → R) → (F → R)
  | [], x => x
  | (t, f) :: l, x => cmap d l (retr d t f x)

/-- The hypotheses under which a list of (top cell, face) pairs is a sequence of elementary
collapses on the chain level: the face is a *unit* face of the cell it is collapsed across,
and it is *free*, i.e. no cell removed later meets it. -/
def IsChainCollapse (d : T → F → R) : List (T × F) → Prop
  | [] => True
  | (t, f) :: l => IsUnit (d t f) ∧ (∀ p ∈ l, d p.1 f = 0) ∧ IsChainCollapse d l

variable {d : T → F → R}

@[simp] theorem retr_zero t f : retr d t f 0 = 0 := by
  funext g; simp [retr]

theorem retr_add t f x y :
    retr d t f (x + y) = retr d t f x + retr d t f y := by
  grind [retr, Pi.add_apply, add_mul]

theorem retr_leftMul a t f x :
    retr d t f (a * x ·) = fun g => a * retr d t f x g := by
  grind [retr, mul_sub, mul_assoc]

@[simp] theorem cmap_zero l : cmap d l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [cmap, ih]

theorem cmap_add l x y :
    cmap d l (x + y) = cmap d l x + cmap d l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons p l ih => simp [cmap, retr_add, ih]

theorem cmap_leftMul l a x :
    cmap d l (a * x ·) = fun g => a * cmap d l x g := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      cases' p with t f
      show cmap d l (retr d t f fun g => a * x g) = fun g => a * cmap d l (retr d t f x) g
      rw [retr_leftMul, ih]

/-- The retraction of an elementary collapse kills the boundary of the cell it removes. -/
theorem retr_self (h : IsUnit (d t f)) : retr d t f (d t) = 0 := by
  funext g
  simp [retr, Ring.mul_inverse_cancel _ h]

/-- The retraction of an elementary collapse fixes the boundary of a cell which does not
meet the face it is collapsed across. -/
theorem retr_of_notMem {t t'} {f} (h : d t' f = 0) : retr d t f (d t') = d t' := by
  funext g; simp [retr, h]

/-- **The chain map of a collapse kills the boundary of every collapsed cell.** -/
theorem cmap_bdry_eq_zero (hl : IsChainCollapse d l) :
    ∀ p ∈ l, cmap d l (d p.1) = 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
      cases' p with t f
      obtain ⟨hunit, hfree, hrest⟩ := hl
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hrl
      · show cmap d l (retr d t f (d t)) = 0
        rw [retr_self hunit, cmap_zero]
      · show cmap d l (retr d t f (d r.1)) = 0
        rw [retr_of_notMem (hfree r hrl)]
        tauto

/-- The chain map of a collapse, applied to a combination of boundaries of top cells. -/
theorem cmap_sum (l : List (T × F)) [DecidableEq T] s (c : T → R) :
    cmap d l (∑ t ∈ s, c t * d t ·) = fun g => ∑ t ∈ s, c t * cmap d l (d t) g := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hz : (∑ t ∈ (∅), c t * d t ·) = (0) := by
        rfl
      simp_all
  | insert t s ht ih =>
      have hsplit : (∑ u ∈ insert t s, c u * d u ·)
          = (c t * d t ·) + (∑ u ∈ s, c u * d u ·) := by
        aesop
      rw [hsplit, cmap_add, cmap_leftMul, ih]
      aesop

/-- **The chain map of a collapse kills every combination of boundaries of collapsed
cells.** -/
theorem cmap_sum_eq_zero {l : List (T × F)} (hl : IsChainCollapse d l) [DecidableEq T]
    s (c : T → R) (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l) :
    cmap d l (∑ t ∈ s, c t * d t ·) = 0 := by
  classical
  rw [cmap_sum]
  funext g
  refine Finset.sum_eq_zero fun t htt => ?_
  cases' hs t htt with f hf
  rw [cmap_bdry_eq_zero hl _ hf]
  simp

/-- **The chain map of a collapse fixes the chains of the spine**: a chain which already
vanishes on every collapsed face is left unchanged. -/
theorem cmap_of_forall_eq_zero x (hx : ∀ p ∈ l, x p.2 = 0) :
    cmap d l x = x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      cases' p with t f
      have hf : x f = 0 := by simp_all
      have hretr : retr d t f x = x := by
        funext g; simp [retr, hf]
      show cmap d l (retr d t f x) = x
      aesop

/-- **A boundary collapses to the zero chain of the spine.**  If every top cell is collapsed
away, then the cellular chain obtained from a boundary is zero: this is the step "in a
two-complex a homologically zero two-cycle is the zero cellular chain". -/
theorem cmap_eq_zero_of_isBoundary {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] {s} {c : T → R} (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l)
    {x} (hx : ∀ g, x g = ∑ t ∈ s, c t * d t g) :
    cmap d l x = 0 := by
  have hxe := funext hx
  rw [hxe]
  exact cmap_sum_eq_zero hl s c hs

/-! ### The surviving three-cell -/

/-! ### Chain complexes presented by linear maps -/
