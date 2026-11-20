module
public import CoxeterGrowth.Family

/-!
# From normal forms to Coxeter spheres

The reflections of `TriangleNF` satisfy the relations of the given Coxeter matrix,
so they act on normal forms via `CoxeterSystem.lift`. In the other direction, read
a code as an explicit product of alternating words. The orbit of the empty form
and the reading map are inverse and preserve length (`sphere_eq`). The growth
identity and the family comparisons then transfer from the finite count.
-/

@[expose] public section

namespace TriangleGrowth

open PowerSeries Function CoxeterSystem

variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
  (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

/-- Mathlib's alternating word ends with `i`. Taking its inverse reads it
starting with `i`, since the simple generators are involutions. -/
def block (i j : Fin 3) (k : ℕ) := (cs.wordProd (alternatingWord j i k))⁻¹

def tail : Fin 3 → Fin 3 → List ℕ → W
  | _, _, [] => 1
  | i, j, k :: r => block cs i 2 k * tail j i r

def read (i j : Fin 3) (v : Raw) :=
  (if v.1 then cs.simple 2 else 1) * tail cs i j (v.2.1 :: v.2.2)

attribute [local simp] read tail block alternatingWord wordProd_append wordProd_cons
  Involutive.toPerm move

variable {P Q : Label}

@[simp] theorem read_swap (i j) (v : NF P Q) : read cs i j (chart v) = read cs j i v := by
  rcases v with ⟨⟨e, t⟩, h⟩
  fun_cases shift t <;> simp [chart, swap, shift]
  grind [ValidTail]

theorem read_move (i j) (v : NF P Q) (hM : M i 2 = P) :
    read cs i j (a v) = cs.simple i * read cs i j v := by
  obtain ⟨⟨e, k, r⟩, h⟩ := v
  cases e
  · rcases k with _ | _ | k <;> simp [a, mul_assoc]
  · by_cases H : k + 2 < P
    · simp [a, H, mul_assoc]
    · have := M.symmetric 2 i
      -- At the wrap the two alternating words have lengths summing to 2p.
      have wrap : block cs i 2 (k + 2) = block cs 2 i ((2 * P.val - k - 3) + 1) := by
        unfold block
        rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub 2 i _ (by grind)]
        congr 3
        grind
      simpa [a, H, mul_assoc] using congrArg (· * tail cs j i r) wrap.symm

scoped notation:max "aₙ " cs:arg n:arg => Nat.card {w // CoxeterSystem.length cs w = n}
scoped notation:max "growth " cs:arg => PowerSeries.mk fun n => (aₙ cs n : ℤ)

variable {p q p' q' : ℕ}
variable (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q') (hne : (p, q) ≠ (2, 2))
  (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (h01' : M' 0 1 = 0)

include hp hq h01 h02 h12
/-- The orbit of the empty form identifies each Coxeter sphere with the finite
set of admissible codes of that length. -/
theorem sphere_eq (n : ℕ) : aₙ cs n = count p q n := by
  let Form := NF ⟨p, hp⟩ ⟨q, hq⟩
  have liftable : M.IsLiftable (@gen ⟨p, hp⟩ ⟨q, hq⟩) := by
    intro i j
    -- Reversing the pair inverts the product. The infinite label has exponent zero.
    wlog h : i ≤ j generalizing i j
    · simpa [← inv_pow, M.symmetric j i] using congrArg Inv.inv (this j i (by omega))
    fin_cases i, j <;> norm_num at * <;> simp_all <;> first | exact ac_rel | exact bc_rel
  let z : Form := ⟨(false, 0, []), by grind [ValidTail]⟩
  let ev (w : W) := cs.lift ⟨_, liftable⟩ w z
  have evs (i w) : ev (cs.simple i * w) = gen i (ev w) := by simp [ev]
  let π (v : Form) := read cs 0 1 v
  have pi_s (i) (v : Form) : π (gen i v) = cs.simple i * π v := by
    fin_cases i
    · exact read_move cs 0 1 v h02
    · change read cs 0 1 (chart (a (chart v))) = _
      rw [read_swap, read_move cs 1 0 _ h12, read_swap]
      rfl
    · cases H : v.val.1 <;> simp [gen, π, c, H]
  -- Reading a group word's form recovers its product. Each letter adds at most
  -- one to the rank, so use a shortest word for the upper bound.
  have fromWord (w) : π (ev w) = w ∧ len (ev w) ≤ cs.length w := by
    obtain ⟨l, h, rfl⟩ := cs.exists_isReduced w
    rw [h.eq]
    clear h
    induction l with
    | nil => simp [ev, π, z, len]
    | cons i l ih =>
      simp [evs, pi_s, ih.1]
      grind [len_gen]
  -- Conversely strip a letter by descent, use the certificate at the shorter
  -- form, then put the letter back using equivariance and the square relation.
  have fromForm (v : Form) : ev (π v) = v ∧ cs.length (π v) ≤ len v := by
    induction v using (measure (fun v : Form => len v)).wf.induction with
    | h v ih =>
      obtain hz | ⟨i, h⟩ := descent v
      · obtain rfl : v = z := Subtype.ext hz
        simp [π, z, ev]
      · have := ih _ h
        have sq : gen i (gen i v) = v := Equiv.congr_fun (gen_sq i) v
        have := cs.length_simple_mul (π (gen i v)) i
        grind
  -- Restrict the equivalence to length n; the two rank bounds give equality.
  let e : W ≃ Form := ⟨ev, π, fun w => (fromWord w).1, fun v => (fromForm v).1⟩
  rw [count, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr ((e.subtypeEquiv (q := fun v : Form => v.val ∈ forms p q n) ?_).trans
    (Equiv.subtypeSubtypeEquivSubtype fun hv => ((mem_forms _).1 hv).1))
  intro w
  simp [e]
  grind

local notation "count_eq" => sphere_eq cs hp hq h01 h02 h12

/-- **(1) The growth series of the triangle Coxeter group `(p, q, ∞)`.** -/
theorem growth_series : growth cs * (1 - S₊ p X * S₊ q X) = (1 + X) * Rₓ p * Rₓ q := by
  simpa only [count_eq] using forms_series p q

include hpp hqq h01' in
/-- **(12) Monotonicity** in `(p, q)`: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n : ℕ) : aₙ cs n ≤ aₙ cs' n := by
  rw [count_eq, sphere_eq cs' (hp.trans hpp) (hq.trans hqq) h01' h02' h12']
  exact count_mono hpp hqq n

include h01' in
/-- **(13) Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n : ℕ) : aₙ cs n = aₙ cs' n := by
  rw [count_eq, sphere_eq cs' hq hp h01' h02' h12', count_symm p q]

include hne in
/-- **(14) The plastic number bounds the whole family from below**: for every hyperbolic
`(p, q, ∞)`, `2ρⁿ ≤ a(n)` for `n ≥ 2`. -/
theorem sphere_ge_plastic (ρ : ℝ) (hρ : 1 < ρ) (hc : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (aₙ cs (n + 2) : ℝ) := by
  rw [count_eq]
  apply (bounds23 ρ hρ hc n).1.trans
  apply Nat.cast_le.mpr
  by_cases h : 3 ≤ q
  · exact count_mono hp h _
  · rw [count_symm 2 3]
    exact count_mono (by grind) hq _

/-- **(16) Growth rate of every member**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate (τ : ℝ) (hτ : 1 < τ) (heq : G p q τ = 1) :
    RootLimit (n ↦ aₙ cs n) τ := by
  simpa only [count_eq] using count_limit hp hq (zero_lt_one.trans hτ) heq

end TriangleGrowth
