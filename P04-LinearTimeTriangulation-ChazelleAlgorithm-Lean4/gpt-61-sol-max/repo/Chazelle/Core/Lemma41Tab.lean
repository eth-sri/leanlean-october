module

public import Chazelle.Core.Lemma41Cost1
public import Chazelle.Core.SpecPhases

/-!
# WP-J, part 22: where the grade table lives

The context `gradeCtx O` holds when the grade table is robust below the allocator `A`.  A robust
fact pins memory values, so every cell the table facts pin lies below `A` (`addr_lt`, `ptr_lt`,
`bound2_lt`, `bound3_lt`, `nfWithin_lt`).  `tab_lt` collects the cells Lemma 4.1 reads:
the header, the setup tables, the halving table and the entries of the grades below `m h`.
-/

namespace Chazelle.Core.L41

open Machine Chazelle

@[expose] public section

variable {A : ℕ} {m : ℕ → ℕ} {Φ : (ℕ → ℕ) → Prop}

section
variable (h : Robust A m Φ)
include h
/-- A pinned cell lies below the bound. -/
theorem addr_lt {x v : ℕ}
    (hΦ : ∀ m', (∀ a, a < A → m' a = m a) → Φ m' → m' x = v) : x < A := by
  by_contra hx
  let m' : ℕ → ℕ := fun a => if a = x then v + 1 else m a
  have he : ∀ a, a < A → m' a = m a := fun a ha => by grind
  have := hΦ m' he (h m' he)
  grind

/-- A cell bounded by a constant lies below the bound. -/
theorem le_lt {x v : ℕ}
    (hΦ : ∀ m', (∀ a, a < A → m' a = m a) → Φ m' → m' x ≤ v) : x < A := by
  by_contra hx
  let m' : ℕ → ℕ := fun a => if a = x then v + 1 else m a
  have he : ∀ a, a < A → m' a = m a := fun a ha => by grind
  have := hΦ m' he (h m' he)
  grind

/-- A pointer to a pinned cell lies below the bound. -/
theorem ptr_lt {p y v : ℕ}
    (hΦ : ∀ m', (∀ a, a < A → m' a = m a) → Φ m' → m' (m' p + y) = v) : p < A := by
  by_contra hp
  let V := p + A + 1
  let m' : ℕ → ℕ := fun a => if a = p then V else if a = V + y then v + 1 else m a
  have he : ∀ a, a < A → m' a = m a := fun a ha => by
    grind
  have := hΦ m' he (h m' he)
  grind

/-- One level of indirection before a bounded address. -/
theorem bound2_lt {p u : ℕ}
    (hΦ : ∀ m', (∀ a, a < A → m' a = m a) → Φ m' → m' (m' p + u) < A) : p < A := by
  by_contra hp
  let V := p + A + 1
  let m' : ℕ → ℕ := fun a => if a = p then V else if a = V + u then A else m a
  have he : ∀ a, a < A → m' a = m a := fun a ha => by
    grind
  have := hΦ m' he (h m' he)
  grind

/-- Two levels of indirection before a bounded address. -/
theorem bound3_lt {p u w : ℕ}
    (hΦ : ∀ m', (∀ a, a < A → m' a = m a) → Φ m' → m' (m' (m' p + u) + w) < A) : p < A := by
  by_contra hp
  let V := p + A + 1
  let V2 := V + u + 1
  let m' : ℕ → ℕ := fun a =>
    if a = p then V else if a = V + u then V2 else if a = V2 + w then A else m a
  have he : ∀ a, a < A → m' a = m a := fun a ha => by
    grind
  have := hΦ m' he (h m' he)
  grind


end

/-- A robust normal form lies below the bound. -/
theorem nfWithin_lt {f : ℕ} {N : NF} (hN : NFWithin m f A N) : f < A := by
  by_contra hf
  let m' : ℕ → ℕ := fun a => if a = f then m f + 1 else m a
  have he : ∀ a, a < A → m' a = m a := fun a ha => by grind
  have h1 := (hN m' he).1
  have h2 := hN.holds.1
  grind

/-- **The cells of the grade table lie below the bound.** -/
theorem tab_lt {O : OracleIface} {P : Polygon} {h : ℕ}
    (hR : Robust A m fun m' => GradeRaw O P m' h A) (hn : 2 ≤ P.n) (hΛ : 1 ≤ m h) :
    h < A ∧ h + 1 < A ∧ h + 2 < A ∧ h + 3 < A ∧
    m (m (h + 1)) = P.n ∧ m (m (h + 1) + 1) = topGrade P.n ∧ m (h + 1) + 1 < A ∧
    (∀ i, i ≤ topGrade P.n + 1 → m (m (h + 1) + 2 + i) = 2 ^ i ∧
      m (m (h + 1) + topGrade P.n + 4 + i) = Cost.ceilBeta i ∧
      m (h + 1) + 2 + i < A ∧ m (h + 1) + topGrade P.n + 4 + i < A) ∧
    (∀ y, y ≤ P.n → m (m (h + 3) + y) = y / 2 ∧ m (h + 3) + y < A) ∧
    (∀ g i, g < m h → i < gradeCount P.n g →
      m (h + 2) + g < A ∧ m (m (h + 2) + g) + 3 * i + 2 < A ∧
      m (m (m (m (h + 2) + g) + 3 * i + 2) + 2) = gradeGran g ∧
      m (m (m (h + 2) + g) + 3 * i + 2) + 2 < A) := by
  have hG := hR.holds
  -- the header
  have h0 : h < A := le_lt hR (x := h) (v := topGrade P.n + 1) fun m' _ hm' => hm'.1
  have h1 : h + 1 < A := ptr_lt hR (p := h + 1) (y := 0) (v := P.n) fun m' _ hm' => hm'.2.1.1
  have h3 : h + 3 < A := ptr_lt hR (p := h + 3) (y := 2) (v := 1) fun m' _ hm' => by
    have := hm'.2.2.1 2 hn; omega
  have h2 : h + 2 < A := bound3_lt hR (p := h + 2) (u := 0) (w := 3 * 0) fun m' he hm' => by
    obtain ⟨-, -, -, -, hwf, -⟩ := hm'.2.2.2 0 0 (by simp_all +arith)
      (by unfold gradeCount; omega)
    have := hwf.1; omega
  refine ⟨h0, h1, h2, h3, hG.2.1.1, hG.2.1.2.1, ?_, fun i hi => ?_, fun y hy => ?_,
    fun g i hg hi => ?_⟩
  · exact addr_lt hR (v := topGrade P.n) fun m' he hm' => by
      have := hm'.2.1.2.1; simp_all
  · obtain ⟨a1, a2⟩ := hG.2.1.2.2.1 i hi
    refine ⟨a1, a2, addr_lt hR (v := 2 ^ i) fun m' he hm' => ?_,
      addr_lt hR (v := Cost.ceilBeta i) fun m' he hm' => ?_⟩
    · have := (hm'.2.1.2.2.1 i hi).1; simp_all
    · have := (hm'.2.1.2.2.1 i hi).2
      simp_all
  · refine ⟨hG.2.2.1 y hy, addr_lt hR (v := y / 2) fun m' he hm' => ?_⟩
    have := hm'.2.2.1 y hy; simp_all
  · have hgi : ∀ m' : ℕ → ℕ, (∀ a, a < A → m' a = m a) → g < m' h := fun m' he => by simp_all
    have hT : m (h + 2) + g < A := bound2_lt hR (p := m (h + 2) + g) (u := 3 * i)
      fun m' he hm' => by
        obtain ⟨-, -, -, -, hwf, -⟩ := hm'.2.2.2 g i (hgi m' he) hi
        have := hwf.1; grind
    have hO : m (m (h + 2) + g) + 3 * i + 2 < A := ptr_lt hR (y := 2) (v := gradeGran g)
      fun m' he hm' => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e3⟩ := hm'.2.2.2 g i (hgi m' he) hi
        grind
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e3⟩ := hG.2.2.2 g i hg hi
    refine ⟨hT, hO, e3, addr_lt hR (v := gradeGran g) fun m' he hm' => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e4⟩ := hm'.2.2.2 g i (hgi m' he) hi
    grind

end

end Chazelle.Core.L41
