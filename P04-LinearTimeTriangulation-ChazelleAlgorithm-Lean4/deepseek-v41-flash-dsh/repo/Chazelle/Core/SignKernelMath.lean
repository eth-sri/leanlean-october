module

public import Chazelle.Golf

public import Chazelle.Core.ShearGood
public import Chazelle.Core.SpecKernels

/-!
# The sign kernel, part 1: the mathematics of the lexicographic sign rules (WP-A)

The machine reads the input `P`, never the geometry polygon `Q = Qof P = shear ε₀ P`
(`ε₀ = epsOf P` is not computable).  Every test of `SignKernelSpec` is a sign condition on a
rational function of the shear parameter; by stability (`StableAt`, part of `GoodShear`) its
truth value at `ε₀` is its eventual truth value as `ε → 0⁺`, which is decided by the
**lexicographic sign** of a coefficient list computable exactly from `P`.

* `pe L ε = L₀ + ε (L₁ + ε (L₂ + …))`: the polynomial with coefficient list `L`;
  `lexPos L` (the lowest nonzero coefficient is positive), `lexNeg L`, `allZero L`;
  `lex_trichotomy`, and `lex_ev`: eventually, `lexPos L → 0 < pe L ε` etc.
* `Rep`: a symbolic point in homogeneous form `x = (x₀ + ε x₁) / (d₀ + ε d₁)`,
  `y = y₀ + ε y₁`, with eventually positive denominator; `symRep P s` computes it from `P`
  (with the case split on the sign of the denominator that the RAM kernel makes) and
  `symRep_spec` proves it correct eventually.
* `xPoly`, `yPoly`, `dPoly`, `testPoly`: the coefficient lists of the four tests
  (`dPoly` is `det · d_a d_b d_c`).
* `signTest_iff_lexPos` (tests `0, 1, 2`) and `signTest_iff_allZero` (test `3`): the truth value
  of a sign test in `Qof P` is the lexicographic sign of `testPoly`.
-/

namespace Chazelle.Core

namespace SignK

@[expose] public section

open Set Filter Topology

/-! ## Polynomials by coefficient lists and their eventual sign -/

/-- The polynomial with coefficient list `L`, evaluated at `ε` (Horner form). -/
def pe : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: L, ε => c + ε * pe L ε

/-- The lowest nonzero coefficient exists and is positive. -/
def lexPos : List ℝ → Prop
  | [] => False
  | c :: L => 0 < c ∨ (c = 0 ∧ lexPos L)

/-- The lowest nonzero coefficient exists and is negative. -/
def lexNeg : List ℝ → Prop
  | [] => False
  | c :: L => c < 0 ∨ (c = 0 ∧ lexNeg L)

/-- All coefficients vanish. -/
def allZero : List ℝ → Prop
  | [] => True
  | c :: L => c = 0 ∧ allZero L

/-- Every coefficient list is lexicographically positive, zero or negative. -/
theorem lex_trichotomy (L : List ℝ) : lexPos L ∨ allZero L ∨ lexNeg L := by
  induction L with
  | nil => exact Or.inr (Or.inl trivial)
  | cons c L ih =>
    rcases lt_trichotomy c 0 with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases ih with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨h, h'⟩))
    · exact Or.inl (Or.inl h)

/-- A coefficient polynomial is continuous. -/
theorem continuous_pe (L : List ℝ) : Continuous (pe L) := by
  induction L with
  | nil => exact continuous_const
  | cons c L ih => exact continuous_const.add (continuous_id.mul ih)

/-- `pe (c :: L) 0 = c`. -/
theorem pe_cons_zero (c : ℝ) (L : List ℝ) : pe (c :: L) 0 = c := by
  Θ pe

/-- The zero coefficient list gives the zero function. -/
theorem pe_of_allZero {L : List ℝ} (h : allZero L) (ε : ℝ) : pe L ε = 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    obtain ⟨h1, h2⟩ := h
    Θ pe, h1, ih h2

/-- A lexicographically positive list gives an eventually positive function. -/
theorem pe_pos_of_lexPos {L : List ℝ} (h : lexPos L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < pe L ε := by
  induction L with
  | nil => exact h.elim
  | cons c L ih =>
    rcases h with h | ⟨h1, h2⟩
    · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (0 : ℝ) < pe (c :: L) ε :=
        continuous_const.continuousAt.eventually_lt (continuous_pe (c :: L)).continuousAt
          (by rw [pe_cons_zero]; exact h)
      exact nhdsWithin_le_nhds hc
    · filter_upwards [ih h2, self_mem_nhdsWithin] with ε hε hε0
      ϴ pe, h1, zero_add
      exact mul_pos hε0 hε

/-- A lexicographically negative list gives an eventually negative function. -/
theorem pe_neg_of_lexNeg {L : List ℝ} (h : lexNeg L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), pe L ε < 0 := by
  induction L with
  | nil => exact h.elim
  | cons c L ih =>
    rcases h with h | ⟨h1, h2⟩
    · have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), pe (c :: L) ε < (0 : ℝ) :=
        (continuous_pe (c :: L)).continuousAt.eventually_lt continuous_const.continuousAt
          (by rw [pe_cons_zero]; exact h)
      exact nhdsWithin_le_nhds hc
    · filter_upwards [ih h2, self_mem_nhdsWithin] with ε hε hε0
      ϴ pe, h1, zero_add
      exact mul_neg_of_pos_of_neg hε0 hε

/-- **Eventual sign of a coefficient polynomial**: for all small `ε > 0` the sign of `pe L ε`
is the lexicographic sign of `L`. -/
theorem lex_ev (L : List ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (lexPos L → 0 < pe L ε) ∧ (lexNeg L → pe L ε < 0) ∧
      (allZero L → pe L ε = 0) := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lexPos L → 0 < pe L ε := by
    by_cases h : lexPos L
    · exact (pe_pos_of_lexPos h).mono fun ε hε _ => hε
    · exact Eventually.of_forall fun ε h' => (h h').elim
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), lexNeg L → pe L ε < 0 := by
    by_cases h : lexNeg L
    · exact (pe_neg_of_lexNeg h).mono fun ε hε _ => hε
    · exact Eventually.of_forall fun ε h' => (h h').elim
  filter_upwards [h1, h2] with ε e1 e2
  exact ⟨e1, e2, fun h => pe_of_allZero h ε⟩

/-- At a point where the eventual sign rules hold, positivity is lexicographic positivity. -/
theorem pos_iff_lexPos {L : List ℝ} {ε : ℝ}
    (h : (lexPos L → 0 < pe L ε) ∧ (lexNeg L → pe L ε < 0) ∧ (allZero L → pe L ε = 0)) :
    0 < pe L ε ↔ lexPos L := by
  refine ⟨fun hp => ?_, h.1⟩
  rcases lex_trichotomy L with h' | h' | h'
  · exact h'
  · rw [h.2.2 h'] at hp; exact (lt_irrefl 0 hp).elim
  · exact (lt_asymm hp (h.2.1 h')).elim

/-- At a point where the eventual sign rules hold, vanishing is `allZero`. -/
theorem zero_iff_allZero {L : List ℝ} {ε : ℝ}
    (h : (lexPos L → 0 < pe L ε) ∧ (lexNeg L → pe L ε < 0) ∧ (allZero L → pe L ε = 0)) :
    pe L ε = 0 ↔ allZero L := by
  refine ⟨fun hp => ?_, h.2.2⟩
  rcases lex_trichotomy L with h' | h' | h'
  · exact ((h.1 h').ne' hp).elim
  · exact h'
  · exact ((h.2.1 h').ne hp).elim

/-! ## Homogeneous representation of symbolic points -/

/-- A symbolic point as a function of the shear parameter: abscissa
`(x0 + ε x1) / (d0 + ε d1)`, ordinate `y0 + ε y1`. -/
structure Rep where
  /-- Constant coefficient of the abscissa numerator. -/
  x0 : ℝ
  /-- Linear coefficient of the abscissa numerator. -/
  x1 : ℝ
  /-- Constant coefficient of the denominator. -/
  d0 : ℝ
  /-- Linear coefficient of the denominator. -/
  d1 : ℝ
  /-- Constant coefficient of the ordinate. -/
  y0 : ℝ
  /-- Linear coefficient of the ordinate. -/
  y1 : ℝ

/-- Negate numerator and denominator (the machine computes `0 - v`). -/
def Rep.neg (r : Rep) : Rep := ⟨0 - r.x0, 0 - r.x1, 0 - r.d0, 0 - r.d1, r.y0, r.y1⟩

/-- The representation of the point of the segment from `u` to `w` at the height of `v`
(sheared): denominator `dy + ε dx` normalised to have a positive lowest coefficient, the
abscissa `u.1` itself when the segment is degenerate (`dx = dy = 0`). -/
noncomputable def edgeRep (u w v : Point) : Rep :=
  if w.2 - u.2 < 0 then
    Rep.neg ⟨u.1 * (w.2 - u.2) + (v.2 - u.2) * (w.1 - u.1),
      u.1 * (w.1 - u.1) + (v.1 - u.1) * (w.1 - u.1), w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else if 0 < w.2 - u.2 then
    ⟨u.1 * (w.2 - u.2) + (v.2 - u.2) * (w.1 - u.1),
      u.1 * (w.1 - u.1) + (v.1 - u.1) * (w.1 - u.1), w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else if w.1 - u.1 < 0 then
    Rep.neg ⟨u.1 * (w.2 - u.2) + (v.2 - u.2) * (w.1 - u.1),
      u.1 * (w.1 - u.1) + (v.1 - u.1) * (w.1 - u.1), w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else if 0 < w.1 - u.1 then
    ⟨u.1 * (w.2 - u.2) + (v.2 - u.2) * (w.1 - u.1),
      u.1 * (w.1 - u.1) + (v.1 - u.1) * (w.1 - u.1), w.2 - u.2, w.1 - u.1, v.2, v.1⟩
  else ⟨u.1, 0, 1, 0, v.2, v.1⟩

/-- The representation of a symbolic point of `shear ε P`, computed from `P`. -/
noncomputable def symRep (P : Polygon) : SymPt → Rep
  | .vtx i => ⟨(P.vtx i).1, 0, 1, 0, (P.vtx i).2, (P.vtx i).1⟩
  | .onEdge e h => edgeRep (P.vtx e) (P.vtx ((e + 1) % P.n)) (P.vtx h)

/-- The representation is correct at `ε`. -/
def RepOK (r : Rep) (p : Point) (ε : ℝ) : Prop :=
  0 < r.d0 + ε * r.d1 ∧ r.x0 + ε * r.x1 = p.1 * (r.d0 + ε * r.d1) ∧ p.2 = r.y0 + ε * r.y1

/-- The abscissa of the sheared segment point, multiplied by the denominator. -/
theorem edge_x_mul (u w v : Point) (ε : ℝ) (hne : (w.2 - u.2) + ε * (w.1 - u.1) ≠ 0) :
    (u.1 + ((v.2 + ε * v.1) - (u.2 + ε * u.1)) *
        ((w.1 - u.1) / ((w.2 + ε * w.1) - (u.2 + ε * u.1)))) *
      ((w.2 - u.2) + ε * (w.1 - u.1)) =
    u.1 * (w.2 - u.2) + (v.2 - u.2) * (w.1 - u.1) +
      ε * (u.1 * (w.1 - u.1) + (v.1 - u.1) * (w.1 - u.1)) := by
  have e : (w.2 + ε * w.1) - (u.2 + ε * u.1) = (w.2 - u.2) + ε * (w.1 - u.1) := ⋆
  Ξ e
  field_simp
  ring

/-- **Correctness of `edgeRep`**: for all small `ε > 0` it represents the point of the
sheared segment at the sheared height of `v`. -/
theorem edgeRep_spec (u w v : Point) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RepOK (edgeRep u w v)
      (u.1 + ((v.2 + ε * v.1) - (u.2 + ε * u.1)) *
        ((w.1 - u.1) / ((w.2 + ε * w.1) - (u.2 + ε * u.1))), v.2 + ε * v.1) ε := by
  have hcont : Continuous fun ε : ℝ => (w.2 - u.2) + ε * (w.1 - u.1) := by fun_prop
  unfold edgeRep
  by_cases h1 : w.2 - u.2 < 0
  · ϴ h1, ↓reduceIte
    have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (w.2 - u.2) + ε * (w.1 - u.1) < 0 :=
      hcont.continuousAt.eventually_lt continuous_const.continuousAt (by simpa using h1)
    filter_upwards [nhdsWithin_le_nhds hc] with ε hε
    have := edge_x_mul u w v ε hε.ne
    refine ⟨by dsimp only [Rep.neg]; linarith, ?_, rfl⟩
    dsimp only [Rep.neg]
    linear_combination this
  ϴ h1, ↓reduceIte
  by_cases h2 : 0 < w.2 - u.2
  · ϴ h2, ↓reduceIte
    have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), (0 : ℝ) < (w.2 - u.2) + ε * (w.1 - u.1) :=
      continuous_const.continuousAt.eventually_lt hcont.continuousAt (by simpa using h2)
    filter_upwards [nhdsWithin_le_nhds hc] with ε hε
    have := edge_x_mul u w v ε hε.ne'
    refine ⟨hε, ?_, rfl⟩
    dsimp only
    linear_combination (-1 : ℝ) * this
  ϴ h2, ↓reduceIte
  have h0 : w.2 - u.2 = 0 := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
  by_cases h3 : w.1 - u.1 < 0
  · ϴ h3, ↓reduceIte
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hlt : (w.2 - u.2) + ε * (w.1 - u.1) < 0 := by
      rw [h0, zero_add]; exact mul_neg_of_pos_of_neg hε h3
    have := edge_x_mul u w v ε hlt.ne
    refine ⟨by dsimp only [Rep.neg]; linarith, ?_, rfl⟩
    dsimp only [Rep.neg]
    linear_combination this
  ϴ h3, ↓reduceIte
  by_cases h4 : 0 < w.1 - u.1
  · ϴ h4, ↓reduceIte
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hlt : 0 < (w.2 - u.2) + ε * (w.1 - u.1) := by rw [h0, zero_add]; exact mul_pos hε h4
    have := edge_x_mul u w v ε hlt.ne'
    refine ⟨hlt, ?_, rfl⟩
    dsimp only
    linear_combination (-1 : ℝ) * this
  ϴ h4, ↓reduceIte
  have h5 : w.1 - u.1 = 0 := le_antisymm (not_lt.1 h4) (not_lt.1 h3)
  refine Eventually.of_forall fun ε => ⟨⊛, ?_, rfl⟩
  dsimp only
  Ξ h5
  simp

/-- **Correctness of `symRep`**: for all small `ε > 0`, `symRep P s` represents the symbolic
point `s` of `shear ε P`. -/
theorem symRep_spec (P : Polygon) (s : SymPt) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RepOK (symRep P s) (s.eval (shear ε P)) ε := by
  cases s with
  | vtx i =>
    refine Eventually.of_forall fun ε => ⟨by simp [symRep], ?_, ?_⟩ <;>
      simp [symRep, SymPt.eval, shear_vtx, shearPt]
  | onEdge e h =>
    have := edgeRep_spec (P.vtx e) (P.vtx ((e + 1) % P.n)) (P.vtx h)
    refine this.mono fun ε hε => ?_
    have hev : SymPt.eval (shear ε P) (.onEdge e h) =
        ((P.vtx e).1 + (((P.vtx h).2 + ε * (P.vtx h).1) - ((P.vtx e).2 + ε * (P.vtx e).1)) *
          (((P.vtx ((e + 1) % P.n)).1 - (P.vtx e).1) /
            (((P.vtx ((e + 1) % P.n)).2 + ε * (P.vtx ((e + 1) % P.n)).1) -
              ((P.vtx e).2 + ε * (P.vtx e).1))), (P.vtx h).2 + ε * (P.vtx h).1) := by
      simp only [SymPt.eval, edgeXAt, Visibility.edgeX, Visibility.xAt, shear_vtx, shear_n,
        shearPt]
    rw [hev]
    exact hε

/-! ## The coefficient lists of the tests -/

/-- Abscissa order `a.1 < b.1`: `x_b d_a - x_a d_b` (padded to five coefficients). -/
def xPoly (a b : Rep) : List ℝ :=
  [b.x0 * a.d0 - a.x0 * b.d0, b.x0 * a.d1 + b.x1 * a.d0 - a.x0 * b.d1 - a.x1 * b.d0,
    b.x1 * a.d1 - a.x1 * b.d1, 0, 0]

/-- Ordinate order `a.2 < b.2`: `y_b - y_a`. -/
def yPoly (a b : Rep) : List ℝ := [b.y0 - a.y0, b.y1 - a.y1, 0, 0, 0]

/-- The orientation determinant times `d_a d_b d_c`:
`(x_b d_a - x_a d_b) d_c (y_c - y_a) - (x_c d_a - x_a d_c) d_b (y_b - y_a)`, coefficients
of the product of `A = x_b d_a - x_a d_b`, `B = d_c (y_c - y_a)`, `C = x_c d_a - x_a d_c`,
`E = d_b (y_b - y_a)`. -/
def dPoly (a b c : Rep) : List ℝ :=
  let A0 := b.x0 * a.d0 - a.x0 * b.d0
  let A1 := b.x0 * a.d1 + b.x1 * a.d0 - a.x0 * b.d1 - a.x1 * b.d0
  let A2 := b.x1 * a.d1 - a.x1 * b.d1
  let C0 := c.x0 * a.d0 - a.x0 * c.d0
  let C1 := c.x0 * a.d1 + c.x1 * a.d0 - a.x0 * c.d1 - a.x1 * c.d0
  let C2 := c.x1 * a.d1 - a.x1 * c.d1
  let B0 := c.d0 * (c.y0 - a.y0)
  let B1 := c.d0 * (c.y1 - a.y1) + c.d1 * (c.y0 - a.y0)
  let B2 := c.d1 * (c.y1 - a.y1)
  let E0 := b.d0 * (b.y0 - a.y0)
  let E1 := b.d0 * (b.y1 - a.y1) + b.d1 * (b.y0 - a.y0)
  let E2 := b.d1 * (b.y1 - a.y1)
  [A0 * B0 - C0 * E0,
    A0 * B1 + A1 * B0 - C0 * E1 - C1 * E0,
    A0 * B2 + A1 * B1 + A2 * B0 - C0 * E2 - C1 * E1 - C2 * E0,
    A1 * B2 + A2 * B1 - C1 * E2 - C2 * E1,
    A2 * B2 - C2 * E2]

/-- The coefficient list of test `op`. -/
def testPoly (op : ℕ) (a b c : Rep) : List ℝ :=
  match op with
  | 0 => xPoly a b
  | 1 => yPoly a b
  | _ => dPoly a b c

/-- The value of `pe` on a five-coefficient list. -/
theorem pe_five (c0 c1 c2 c3 c4 ε : ℝ) :
    pe [c0, c1, c2, c3, c4] ε = c0 + ε * c1 + ε ^ 2 * c2 + ε ^ 3 * c3 + ε ^ 4 * c4 := by
  ϴ pe
  ring

/-- Where the representations are correct, `xPoly` is `(x_b - x_a) d_a d_b`. -/
theorem pe_xPoly {a b : Rep} {p q : Point} {ε : ℝ} (ha : RepOK a p ε) (hb : RepOK b q ε) :
    pe (xPoly a b) ε = (q.1 - p.1) * ((a.d0 + ε * a.d1) * (b.d0 + ε * b.d1)) := by
  have e : pe (xPoly a b) ε =
      (b.x0 + ε * b.x1) * (a.d0 + ε * a.d1) - (a.x0 + ε * a.x1) * (b.d0 + ε * b.d1) := by
    rw [xPoly, pe_five]; ring
  Ξ e, ha.2.1, hb.2.1
  ring

/-- Where the representations are correct, `yPoly` is `y_b - y_a`. -/
theorem pe_yPoly {a b : Rep} {p q : Point} {ε : ℝ} (ha : RepOK a p ε) (hb : RepOK b q ε) :
    pe (yPoly a b) ε = q.2 - p.2 := by
  Ξ yPoly, pe_five, ha.2.2, hb.2.2
  ring

/-- Where the representations are correct, `dPoly` is `det · d_a d_b d_c`. -/
theorem pe_dPoly {a b c : Rep} {p q r : Point} {ε : ℝ} (ha : RepOK a p ε) (hb : RepOK b q ε)
    (hc : RepOK c r ε) :
    pe (dPoly a b c) ε =
      det p q r * ((a.d0 + ε * a.d1) * (b.d0 + ε * b.d1) * (c.d0 + ε * c.d1)) := by
  have e : pe (dPoly a b c) ε =
      ((b.x0 + ε * b.x1) * (a.d0 + ε * a.d1) - (a.x0 + ε * a.x1) * (b.d0 + ε * b.d1)) *
          ((c.d0 + ε * c.d1) * ((c.y0 + ε * c.y1) - (a.y0 + ε * a.y1))) -
        ((c.x0 + ε * c.x1) * (a.d0 + ε * a.d1) - (a.x0 + ε * a.x1) * (c.d0 + ε * c.d1)) *
          ((b.d0 + ε * b.d1) * ((b.y0 + ε * b.y1) - (a.y0 + ε * a.y1))) := by
    rw [dPoly, pe_five]; ring
  Ξ e, ha.2.1, hb.2.1, hc.2.1, ← ha.2.2, ← hb.2.2, ← hc.2.2
  ϴ det
  ring

/-! ## From the eventual value to the value at `epsOf P` -/

/-- A test has the same truth value on two triples with the same sign facts. -/
theorem signTest_congr {a b d a' b' d' : Point} (h : SignFacts a b d = SignFacts a' b' d')
    (op : ℕ) : SignTest op a b d ↔ SignTest op a' b' d' := by
  simp only [SignFacts, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  match op with
  | 0 => exact Iff.of_eq h1
  | 1 => exact Iff.of_eq h2
  | 2 => exact Iff.of_eq h3
  | _ + 3 => exact Iff.of_eq h4

/-- Positivity of `pe (testPoly op …)` at a point where the representations are correct is the
test `op` for `op < 3`, and vanishing is test `3`. -/
theorem signTest_iff_pe {a b c : Rep} {p q r : Point} {ε : ℝ} (ha : RepOK a p ε)
    (hb : RepOK b q ε) (hc : RepOK c r ε) (op : ℕ) :
    (op < 3 → (SignTest op p q r ↔ 0 < pe (testPoly op a b c) ε)) ∧
      (op = 3 → (SignTest op p q r ↔ pe (testPoly op a b c) ε = 0)) := by
  have hab := mul_pos ha.1 hb.1
  have habc := mul_pos hab hc.1
  refine ⟨fun hop => ?_, fun hop => ?_⟩
  · match op, hop with
    | 0, _ =>
      ϴ SignTest, testPoly
      Ξ pe_xPoly ha hb, mul_pos_iff_of_pos_right hab, sub_pos
    | 1, _ =>
      ϴ SignTest, testPoly
      Ξ pe_yPoly ha hb, sub_pos
    | 2, _ =>
      ϴ SignTest, testPoly
      Ξ pe_dPoly ha hb hc, mul_pos_iff_of_pos_right habc
  · subst hop
    ϴ SignTest, testPoly
    Ξ pe_dPoly ha hb hc, mul_eq_zero, or_iff_left habc.ne'

/-- **The sign tests in `Qof P` are lexicographic sign conditions** on coefficient lists
computed from `P` (tests `0, 1, 2`: positivity). -/
theorem signTest_iff_lex (P : Polygon) (hG : ∃ ε, GoodShear P ε) (s₁ s₂ s₃ : SymPt)
    (h₁ : s₁.Lt P.n) (h₂ : s₂.Lt P.n) (h₃ : s₃.Lt P.n) (op : ℕ) :
    (op < 3 → (SignTest op (s₁.eval (Qof P)) (s₂.eval (Qof P)) (s₃.eval (Qof P)) ↔
      lexPos (testPoly op (symRep P s₁) (symRep P s₂) (symRep P s₃)))) ∧
    (op = 3 → (SignTest op (s₁.eval (Qof P)) (s₂.eval (Qof P)) (s₃.eval (Qof P)) ↔
      allZero (testPoly op (symRep P s₁) (symRep P s₂) (symRep P s₃)))) := by
  obtain ⟨hε0, -, -, hstab⟩ := goodShear_epsOf hG
  set L := testPoly op (symRep P s₁) (symRep P s₂) (symRep P s₃)
  have hev := ((symRep_spec P s₁).and (symRep_spec P s₂)).and ((symRep_spec P s₃).and (lex_ev L))
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hδ0 : (0 : ℝ) < δ := hδ
  set ε' := min (δ / 2) (epsOf P)
  have hε'0 : 0 < ε' := lt_min (⟡) hε0
  have hε'δ : ε' < δ := lt_of_le_of_lt (min_le_left _ _) (⟡)
  obtain ⟨⟨r1, r2⟩, r3, hl⟩ := hsub (show ε' ∈ Ioo 0 δ from ⟨hε'0, hε'δ⟩)
  have hSF := hstab ε' hε'0 (min_le_right _ _) s₁ s₂ s₃ h₁ h₂ h₃
  have hT := signTest_congr hSF op
  have hP := signTest_iff_pe r1 r2 r3 op
  refine ⟨fun hop => ?_, fun hop => ?_⟩
  · exact (hT.trans (hP.1 hop)).trans (pos_iff_lexPos hl)
  · exact (hT.trans (hP.2 hop)).trans (zero_iff_allZero hl)

end

end SignK

end Chazelle.Core
