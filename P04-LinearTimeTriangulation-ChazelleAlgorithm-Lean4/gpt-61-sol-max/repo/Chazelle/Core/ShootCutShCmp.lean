module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutShPt

/-!
# WP-G, part 41: comparing abscissae and ordinates of point records

Bits computed from point records (`AbsRec`, `HRec`) with at most one sign-kernel test:

* `xLess a b dst`: the abscissa of the record at `a` is below the one at `b` (for a **weak**
  record `AbsRecW`, whose symbolic kind allows `|x| ≤ R`, provided the two abscissae differ or
  both records are strict);
* `hLess a b dst T`: the ordinate at `a` is below the one at `b` (slots `T … T + 5`);
* `hEq a b dst`: the ordinates are equal (distinct heights of `Q`: equal vertices).

The constant register `K1 = 140401` holds `1`.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-- The register holding `1`. -/
def K1 : ℕ := 140401

/-- **A weak abscissa record**: like `AbsRec`, but the symbolic kind allows `|x| ≤ R`. -/
def AbsRecW (P : Polygon) (c : Config) (r : ℕ) (x R : ℝ) : Prop :=
  0 < R ∧ ((c.nreg r = 0 ∧ x = -R) ∨ (c.nreg r = 2 ∧ x = R) ∨
    (c.nreg r = 1 ∧ |x| ≤ R ∧ ∃ s : SymPt, SymPtIn c (r + 1) s ∧ s.Lt P.n ∧ (s.eval (Qof P)).1 = x))

section
variable {P : Polygon} {c : Config} {r : ℕ} {x R : ℝ}
include P c r x R
theorem AbsRec.weak (h : AbsRec P c r x R) :
    AbsRecW P c r x R := by
  obtain ⟨hR, h⟩ := h
  core_grind

section
variable (h : AbsRecW P c r x R)
include h
theorem AbsRecW.kind :
    c.nreg r ≤ 2 := by
  rcases h.2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

theorem AbsRecW.bounds :
    -R ≤ x ∧ x ≤ R := by
  obtain ⟨hR, h⟩ := h
  grind



end

end

/-- A weak record describes one abscissa once the registers are fixed. -/
theorem AbsRecW.copy {P : Polygon} {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRecW P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) (h3 : c'.nreg (r' + 3) = c.nreg (r + 3)) :
    AbsRecW P c' r' x R := by
  obtain ⟨hR, hk⟩ := h
  refine ⟨hR, ?_⟩
  rcases hk with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, hx, s, hs, hl, he⟩
  · simp_all
  · simp_all
  · refine Or.inr (Or.inr ⟨h0.trans k, hx, s, ?_, hl, he⟩)
    
    
    
    
    exact NFLoc.symPtIn_copy hs h1 (by omega) (by omega)

/-! ## Abscissae -/

/-- **The bit `x_a < x_b`.** -/
def xLess (a b dst : ℕ) : Stmt :=
  .ifLtN a K1 (.ifLtN b K1 (.instr (.constN dst 0)) (.instr (.constN dst 1)))
    (.ifLtN K1 a (.instr (.constN dst 0))
      (.ifLtN b K1 (.instr (.constN dst 0))
        (.ifLtN K1 b (.instr (.constN dst 1)) (kbit (a + 1) (b + 1) (a + 1) 0 dst))))

variable {P : Polygon} {W : ℕ}

theorem bit_const (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) (dst v : ℕ) (hv : v ≤ 1)
    {p : Prop} (hp : v = 1 ↔ p) :
    BitIs ({ c with nreg := upd c.nreg dst v } : Config) dst p ∧
      Exec P W (.instr (.constN dst v)) c { c with nreg := upd c.nreg dst v } 1 :=
  ⟨⟨by simp; omega, by simp_all⟩, Exec.constN hw dst v (by omega)⟩

theorem xLess_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b dst : ℕ} (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hdst : 10500 ≤ dst) (h1 : c.nreg K1 = 1)
    {xa xb R : ℝ} (hA : AbsRecW P c a xa R) (hB : AbsRecW P c b xb R)
    (hok : xa ≠ xb ∨ ((c.nreg a = 1 → |xa| < R) ∧ (c.nreg b = 1 → |xb| < R))) :
    ∃ c' k, Exec P W (xLess a b dst) c c' k ∧ k ≤ 250 ∧ BitIs c' dst (xa < xb) ∧
      FrameB (Bkb dst) c c' := by
  have hR := hA.1
  have kA := hA.kind
  have kB := hB.kind
  have bA := hA.bounds
  have bB := hB.bounds
  have fr : ∀ v, FrameB (Bkb dst) c ({ c with nreg := upd c.nreg dst v } : Config) := fun v =>
    ⟨fun r hr => by
      simp_all [Bkb, Bool.or_eq_false_iff, beq_eq_false_iff_ne] <;> omega_nf, fun _ _ => rfl, rfl, rfl, rfl⟩
  unfold xLess
  by_cases a0 : c.nreg a < c.nreg K1
  · 
    have hxa : xa = -R := by
      rcases hA.2 with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    by_cases b0 : c.nreg b < c.nreg K1
    · have hxb : xb = -R := by
        rcases hB.2 with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
      obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 0 (by norm_num)
        (p := xa < xb) (by simp_all)
      exact ⟨_, _, .ifLtN_true a0 (.ifLtN_true b0 ex), by norm_num, bt, fr 0⟩
    · have hlt : xa < xb := by
        rcases hB.2 with ⟨h', _⟩ | ⟨_, h⟩ | ⟨_, hx, s, -, -, -⟩
        all_goals grind
      obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 1 le_rfl (p := xa < xb)
        ⟨fun _ => hlt, fun _ => rfl⟩
      exact ⟨_, _, .ifLtN_true a0 (.ifLtN_false b0 ex), by norm_num, bt, fr 1⟩
  by_cases a2 : c.nreg K1 < c.nreg a
  · have hxa : xa = R := by
      rcases hA.2 with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 0 (by norm_num) (p := xa < xb)
      ⟨fun h => absurd h (by norm_num), fun h => by grind⟩
    exact ⟨_, _, .ifLtN_false a0 (.ifLtN_true a2 ex), by norm_num, bt, fr 0⟩
  
  obtain ⟨-, hxa, sa, isa, lsa, vsa⟩ : c.nreg a = 1 ∧ |xa| ≤ R ∧ ∃ s : SymPt, SymPtIn c (a + 1) s ∧
      s.Lt P.n ∧ (s.eval (Qof P)).1 = xa := by
    rcases hA.2 with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  by_cases b0 : c.nreg b < c.nreg K1
  · have hxb : xb = -R := by
      rcases hB.2 with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 0 (by norm_num) (p := xa < xb)
      ⟨fun h => absurd h (by norm_num), fun h => by grind⟩
    exact ⟨_, _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_true b0 ex)), by norm_num, bt, fr 0⟩
  by_cases b2 : c.nreg K1 < c.nreg b
  · have hxb : xb = R := by
      rcases hB.2 with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    have hlt : xa < xb := by
      grind
    obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 1 le_rfl (p := xa < xb)
      ⟨fun _ => hlt, fun _ => rfl⟩
    exact ⟨_, _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_false b0 (.ifLtN_true b2 ex))),
      by norm_num, bt, fr 1⟩
  obtain ⟨-, -, sb, isb, lsb, vsb⟩ : c.nreg b = 1 ∧ |xb| ≤ R ∧ ∃ s : SymPt, SymPtIn c (b + 1) s ∧
      s.Lt P.n ∧ (s.eval (Qof P)).1 = xb := by
    rcases hB.2 with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  obtain ⟨c', k, ex, hk, f, b₁, t⟩ := kbit_exec (op := 0) (dst := dst) hG hW c hw (by omega)
    (by omega) (by omega) hdst (by norm_num) lsa lsb lsa isa isb isa
  refine ⟨c', _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_false b0 (.ifLtN_false b2 ex))),
    by omega, ⟨b₁, ?_⟩, f⟩
  rw [t]; show (sa.eval (Qof P)).1 < (sb.eval (Qof P)).1 ↔ _; simp_all

/-! ## Ordinates -/

/-- **An ordinate record with a slot** at `r`: kind `0` (`-R`), `2` (`R`), or `1` and, at `r + 1`,
the symbolic vertex (`0`, index) of `Q` at height `y`, `|y| < R`. -/
def HRecS (P : Polygon) (c : Config) (r : ℕ) (y R : ℝ) : Prop :=
  (c.nreg r = 0 ∧ y = -R) ∨ (c.nreg r = 2 ∧ y = R) ∨
    (c.nreg r = 1 ∧ |y| < R ∧ c.nreg (r + 1) = 0 ∧ c.nreg (r + 2) < P.n ∧
      y = ((Qof P).vtx (c.nreg (r + 2))).2)

section
variable {c : Config} {r : ℕ} {y R : ℝ}
theorem HRecS.kind (h : HRecS P c r y R) : c.nreg r ≤ 2 := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

theorem HRecS.bounds (hR : 0 < R) (h : HRecS P c r y R) :
    -R ≤ y ∧ y ≤ R := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, hy, -⟩
  all_goals grind


end

theorem HRecS.copy {c c' : Config} {r r' : ℕ} {y R : ℝ} (h : HRecS P c r y R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) : HRecS P c' r' y R := by
  core_grind

/-- **The bit `y_a < y_b`.** -/
def hLess (a b dst : ℕ) : Stmt :=
  .ifLtN a K1 (.ifLtN b K1 (.instr (.constN dst 0)) (.instr (.constN dst 1)))
    (.ifLtN K1 a (.instr (.constN dst 0))
      (.ifLtN b K1 (.instr (.constN dst 0))
        (.ifLtN K1 b (.instr (.constN dst 1)) (kbit (a + 1) (b + 1) (a + 1) 1 dst))))

theorem hLess_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b dst : ℕ} (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hdst : 10500 ≤ dst) (h1 : c.nreg K1 = 1)
    {ya yb R : ℝ} (hR : 0 < R) (hA : HRecS P c a ya R) (hB : HRecS P c b yb R) :
    ∃ c' k, Exec P W (hLess a b dst) c c' k ∧ k ≤ 250 ∧ BitIs c' dst (ya < yb) ∧
      FrameB (Bkb dst) c c' := by
  have kA := hA.kind
  have kB := hB.kind
  have bA := hA.bounds hR
  have bB := hB.bounds hR
  have fr : ∀ v, FrameB (Bkb dst) c ({ c with nreg := upd c.nreg dst v } : Config) := fun v =>
    ⟨fun r hr => by
      simp_all [Bkb, Bool.or_eq_false_iff, beq_eq_false_iff_ne] <;> omega_nf, fun _ _ => rfl, rfl, rfl, rfl⟩
  unfold hLess
  by_cases a0 : c.nreg a < c.nreg K1
  · have hya : ya = -R := by
      rcases hA with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    by_cases b0 : c.nreg b < c.nreg K1
    · have hyb : yb = -R := by
        rcases hB with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
      obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 0 (by norm_num)
        (p := ya < yb) (by simp_all)
      exact ⟨_, _, .ifLtN_true a0 (.ifLtN_true b0 ex), by norm_num, bt, fr 0⟩
    · have hlt : ya < yb := by
        rcases hB with ⟨h', _⟩ | ⟨_, h⟩ | ⟨_, hy, -⟩
        all_goals grind
      obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 1 le_rfl (p := ya < yb)
        ⟨fun _ => hlt, fun _ => rfl⟩
      exact ⟨_, _, .ifLtN_true a0 (.ifLtN_false b0 ex), by norm_num, bt, fr 1⟩
  by_cases a2 : c.nreg K1 < c.nreg a
  · have hya : ya = R := by
      rcases hA with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 0 (by norm_num) (p := ya < yb)
      ⟨fun h => absurd h (by norm_num), fun h => by grind⟩
    exact ⟨_, _, .ifLtN_false a0 (.ifLtN_true a2 ex), by norm_num, bt, fr 0⟩
  obtain ⟨-, hya, za, la, vya⟩ : c.nreg a = 1 ∧ |ya| < R ∧ c.nreg (a + 1) = 0 ∧
      c.nreg (a + 2) < P.n ∧ ya = ((Qof P).vtx (c.nreg (a + 2))).2 := by
    rcases hA with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  by_cases b0 : c.nreg b < c.nreg K1
  · have hyb : yb = -R := by
      rcases hB with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 0 (by norm_num) (p := ya < yb)
      ⟨fun h => absurd h (by norm_num), fun h => by grind⟩
    exact ⟨_, _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_true b0 ex)), by norm_num, bt, fr 0⟩
  by_cases b2 : c.nreg K1 < c.nreg b
  · have hyb : yb = R := by
      rcases hB with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    obtain ⟨bt, ex⟩ := bit_const (P := P) c hw (by omega) dst 1 le_rfl (p := ya < yb)
      ⟨fun _ => by grind, fun _ => rfl⟩
    exact ⟨_, _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_false b0 (.ifLtN_true b2 ex))),
      by norm_num, bt, fr 1⟩
  obtain ⟨-, -, zb, lb, vyb⟩ : c.nreg b = 1 ∧ |yb| < R ∧ c.nreg (b + 1) = 0 ∧
      c.nreg (b + 2) < P.n ∧ yb = ((Qof P).vtx (c.nreg (b + 2))).2 := by
    rcases hB with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  have isa : SymPtIn c (a + 1) (.vtx (c.nreg (a + 2))) := ⟨za, rfl⟩
  have isb : SymPtIn c (b + 1) (.vtx (c.nreg (b + 2))) := ⟨zb, rfl⟩
  obtain ⟨c', k, ex, hk, f, b₁, t⟩ := kbit_exec (op := 1) (dst := dst) hG hW c hw (by omega)
    (by omega) (by omega) hdst (by norm_num) (show (SymPt.vtx _).Lt P.n from la)
    (show (SymPt.vtx _).Lt P.n from lb) (show (SymPt.vtx _).Lt P.n from la) isa isb isa
  refine ⟨c', _, .ifLtN_false a0 (.ifLtN_false a2 (.ifLtN_false b0 (.ifLtN_false b2 ex))),
    by omega, ⟨b₁, ?_⟩, f⟩
  rw [t, vya, vyb]; rfl

/-- **The bit `y_a = y_b`.** -/
def hEq (a b dst : ℕ) : Stmt :=
  .ifLtN a b (.instr (.constN dst 0))
    (.ifLtN b a (.instr (.constN dst 0))
      (.ifLtN a K1 (.instr (.constN dst 1))
        (.ifLtN K1 a (.instr (.constN dst 1))
          (.ifLtN (a + 2) (b + 2) (.instr (.constN dst 0))
            (.ifLtN (b + 2) (a + 2) (.instr (.constN dst 0)) (.instr (.constN dst 1)))))))

theorem hEq_exec (hG : GoodEnv P) (hW : 1 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b dst : ℕ} (h1 : c.nreg K1 = 1) {ya yb R : ℝ} (hR : 0 < R) (hA : HRecS P c a ya R)
    (hB : HRecS P c b yb R) :
    ∃ c' k, Exec P W (hEq a b dst) c c' k ∧ k ≤ 20 ∧ BitIs c' dst (ya = yb) ∧
      c' = { c with nreg := upd c.nreg dst (c'.nreg dst) } := by
  
  have kB := hB.kind
  have hD := distinct_Qof hG
  have hQn : (Qof P).n = P.n := shear_n _ _
  have fin : ∀ v, v ≤ 1 → (v = 1 ↔ ya = yb) → ∃ c₂, Exec P W (.instr (.constN dst v)) c c₂ 1 ∧
      BitIs c₂ dst (ya = yb) ∧ c₂ = { c with nreg := upd c.nreg dst (c₂.nreg dst) } :=
    fun v hv hp => ⟨_, Exec.constN hw dst v (by omega), (bit_const (P := P) c hw hW dst v hv hp).1,
      by simp⟩
  -- different kinds: different ordinates
  have kdiff : c.nreg a ≠ c.nreg b → ya ≠ yb := fun hk he => by
    grind [Chazelle.Core.GoodEnv, Chazelle.WordsBounded, Chazelle.Core.ShootCut.HRecS, Chazelle.Core.DistinctHeights, Chazelle.Core.SweepPrim.BitIs]
  by_cases t1 : c.nreg a < c.nreg b
  · obtain ⟨c₂, e, bt, h⟩ := fin 0 (by norm_num) ⟨fun h => absurd h (by norm_num),
      fun h => absurd h (kdiff (by omega))⟩
    exact ⟨c₂, _, .ifLtN_true t1 e, by norm_num, bt, h⟩
  by_cases t2 : c.nreg b < c.nreg a
  · obtain ⟨c₂, e, bt, h⟩ := fin 0 (by norm_num) ⟨fun h => absurd h (by norm_num),
      fun h => absurd h (kdiff (by omega))⟩
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_true t2 e), by norm_num, bt, h⟩
  
  by_cases t3 : c.nreg a < c.nreg K1
  · have hya : ya = -R := by
      rcases hA with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    have hyb : yb = -R := by
      rcases hB with ⟨_, h⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> [exact h; omega; omega]
    obtain ⟨c₂, e, bt, h⟩ := fin 1 le_rfl ⟨fun _ => by simp_all, fun _ => rfl⟩
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true t3 e)), by norm_num, bt, h⟩
  by_cases t4 : c.nreg K1 < c.nreg a
  · have hya : ya = R := by
      rcases hA with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    have hyb : yb = R := by
      rcases hB with ⟨h', _⟩ | ⟨_, h⟩ | ⟨h', _⟩ <;> [omega; exact h; omega]
    obtain ⟨c₂, e, bt, h⟩ := fin 1 le_rfl ⟨fun _ => by simp_all, fun _ => rfl⟩
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_true t4 e))),
      by norm_num, bt, h⟩
  obtain ⟨-, -, -, la, vya⟩ : c.nreg a = 1 ∧ |ya| < R ∧ c.nreg (a + 1) = 0 ∧
      c.nreg (a + 2) < P.n ∧ ya = ((Qof P).vtx (c.nreg (a + 2))).2 := by
    rcases hA with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  obtain ⟨-, -, -, lb, vyb⟩ : c.nreg b = 1 ∧ |yb| < R ∧ c.nreg (b + 1) = 0 ∧
      c.nreg (b + 2) < P.n ∧ yb = ((Qof P).vtx (c.nreg (b + 2))).2 := by
    rcases hB with ⟨h', _⟩ | ⟨h', _⟩ | h <;> [omega; omega; exact h]
  have hiff : ya = yb ↔ c.nreg (a + 2) = c.nreg (b + 2) := by
    rw [vya, vyb]
    constructor
    · intro he
      by_contra hne
      exact hD _ _ (by omega) (by omega) hne he
    grind
  by_cases t5 : c.nreg (a + 2) < c.nreg (b + 2)
  · obtain ⟨c₂, e, bt, h⟩ := fin 0 (by norm_num) ⟨fun h => absurd h (by norm_num),
      fun h => by grind⟩
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_false t4
      (.ifLtN_true t5 e)))), by norm_num, bt, h⟩
  by_cases t6 : c.nreg (b + 2) < c.nreg (a + 2)
  · obtain ⟨c₂, e, bt, h⟩ := fin 0 (by norm_num) ⟨fun h => absurd h (by norm_num),
      fun h => by grind⟩
    exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_false t4
      (.ifLtN_false t5 (.ifLtN_true t6 e))))), by norm_num, bt, h⟩
  obtain ⟨c₂, e, bt, h⟩ := fin 1 le_rfl ⟨fun _ => hiff.2 (by omega), fun _ => rfl⟩
  exact ⟨c₂, _, .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 (.ifLtN_false t4
    (.ifLtN_false t5 (.ifLtN_false t6 e))))), by norm_num, bt, h⟩

end

end ShootCut

end Chazelle.Core
