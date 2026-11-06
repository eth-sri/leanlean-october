module

public import Chazelle.Core.UpPhase8

/-!
# WP-J up phase, part 9: the invariants of the grade table

* `UpEntry`: an entry `(descriptor, NF, oracle)` of chain `(g, i)`, with the descriptor on the
  common whole host `hp` (`NodeOK` of Lemma 4.1 for every chain with the right fields);
* `UpTab`: the grade record at `h` (a strengthening of `GradeRaw`: all descriptors on `hp`),
  `upTab_gradeRaw`;
* `Cells`: the linked list of the cells `[desc, NF, oracle, prev]` of the chains of the current
  grade written so far.
-/

namespace Chazelle.Core.Up

open Machine Chazelle Chazelle.Core.L41

@[expose] public section

/-- The chain `(g, i)` of `Q`. -/
noncomputable def gChain (P : Polygon) (g i : ℕ) (hn : 2 ≤ P.n) (hi : i < gradeCount P.n g) : Chain :=
  ⟨Qof P, gradeStart g i, gradeLen P.n g i, gradeLen_pos hn hi, by
    have := gradeLen_fit hn hi; have hQn : (Qof P).n = P.n := shear_n _ _; omega⟩

/-- **An entry of chain `(g, i)`**: descriptor `d`, normal form `f`, oracle `o`. -/
def UpEntry (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (A hp g i d f o : ℕ) : Prop :=
  (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
    NodeOK P m A hp d f C (gradeGran g)) ∧
  O.At P m o ∧ m o = d ∧ m (o + 1) = f ∧ m (o + 2) = gradeGran g

/-- The address of entry `(g, i)` of the grade record at `h`. -/
abbrev rowE (m : ℕ → ℕ) (h g i : ℕ) : ℕ := m (m (h + 2) + g) + 3 * i

/-- **The grade record at `h`** with all descriptors on the whole host at `hp`. -/
def UpTab (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (h hp A : ℕ) : Prop :=
  m h ≤ topGrade P.n + 1 ∧ SetupAt m (m (h + 1)) P.n (m (h + 1) + 2 * topGrade P.n + 6) ∧
    (∀ x, x ≤ P.n → m (m (h + 3) + x) = x / 2) ∧ HostAt m hp (Host.whole P.n) ∧
    hp + 7 ≤ A ∧
    (h + 4 ≤ A ∧ m (h + 1) + 2 * topGrade P.n + 6 ≤ A ∧ m (h + 3) + P.n + 1 ≤ A) ∧
    m (h + 2) + m h ≤ A ∧
    (∀ g, g < m h → m (m (h + 2) + g) + 3 * gradeCount P.n g ≤ A) ∧
    ∀ g i, g < m h → i < gradeCount P.n g →
      UpEntry O P m A hp g i (m (rowE m h g i)) (m (rowE m h g i + 1)) (m (rowE m h g i + 2))

/-- **The cells of the current grade**: `Cells … x i` for the cell `x` of chain `i - 1` (and the
cells of the chains before it by the back links). -/
def Cells (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (A hp g : ℕ) : ℕ → ℕ → Prop
  | _, 0 => True
  | x, i + 1 => x + 4 ≤ A ∧ UpEntry O P m A hp g i (m x) (m (x + 1)) (m (x + 2)) ∧
      Cells O P m A hp g (m (x + 3)) i

section proofs

variable {O : OracleIface} {P : Polygon}

theorem UpEntry.mono {m : ℕ → ℕ} {A A' hp g i d f o : ℕ} (h : UpEntry O P m A hp g i d f o)
    (hA : A ≤ A') : UpEntry O P m A' hp g i d f o :=
  ⟨fun C h1 h2 h3 => (h.1 C h1 h2 h3).mono hA, h.2⟩

theorem UpTab.mono {m : ℕ → ℕ} {h hp A A' : ℕ} (hT : UpTab O P m h hp A) (hA : A ≤ A') :
    UpTab O P m h hp A' := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨h7, h7b, h7c⟩, h8, h9, h6⟩ := hT
  exact ⟨h1, h2, h3, h4, by omega, ⟨by omega, by omega, by omega⟩, by omega,
    fun g hg => by have := h9 g hg; omega,
    fun g i hg hi => (h6 g i hg hi).mono hA⟩

theorem Cells.mono {m : ℕ → ℕ} {A A' hp g : ℕ} (hA : A ≤ A') :
    ∀ {x i : ℕ}, Cells O P m A hp g x i → Cells O P m A' hp g x i
  | _, 0, _ => trivial
  | _, _ + 1, ⟨h1, h2, h3⟩ => ⟨by omega, h2.mono hA, Cells.mono hA h3⟩

/-- A robust fact implies its consequences, for a larger bound. -/
theorem robust_of {A A' : ℕ} {m : ℕ → ℕ} {Φ Ψ : (ℕ → ℕ) → Prop} (h : Robust A m Φ)
    (hA : A ≤ A') (hΦ : ∀ m', Φ m' → Ψ m') : Robust A' m Ψ :=
  fun m' hm' => hΦ m' (h m' fun a ha => hm' a (by omega))

/-- The chain of a table entry: its descriptor is on the whole host. -/
theorem chainWF_of_node {m : ℕ → ℕ} {A hp d f γ : ℕ} {C : Chain} (hn : 1 ≤ P.n)
    (hN : NodeOK P m A hp d f C γ) (hH : HostAt m hp (Host.whole P.n)) :
    ChainWF P A m d := by
  obtain ⟨hd, -, hdh, hd5, hhp, hfit, -⟩ := hN
  have hQn : (Qof P).n = P.n := shear_n _ _
  refine ⟨hd5, fun H C' hC => ?_⟩
  have hH' : H = Host.whole P.n := hostAt_unique hC.1 (by rwa [hdh])
  subst hH'
  refine ⟨by simp [Host.whole], hostWF_whole hn, by rw [hdh]; simp [Host.whole]; omega, ?_⟩
  have hs : C'.s = C.s := hC.2.2.1.symm.trans hd.2.2.1
  have hP : C'.P = Qof P := by
    rw [hC.2.1]; have := L41.poly_whole (Qof P) (by omega); rwa [hQn] at this
  rw [hs, hP, hQn]; have := C.one_le; omega

/-- **`UpTab` gives the raw grade table.** -/
theorem upTab_gradeRaw {m : ℕ → ℕ} {h hp A : ℕ} (hn : 2 ≤ P.n) (hT : UpTab O P m h hp A) :
    GradeRaw O P m h A := by
  obtain ⟨h1, h2, h3, hH, -, -, -, -, hE⟩ := hT
  refine ⟨h1, h2, h3, fun g i hg hi => ?_⟩
  obtain ⟨hN, hAt, e0, e1, e2⟩ := hE g i hg hi
  have hNo := hN (gChain P g i hn hi) rfl rfl rfl
  have hwf := chainWF_of_node (by omega) hNo hH
  obtain ⟨hd, -, -, -, -, -, N, hNW, hc⟩ := hNo
  exact ⟨Host.whole P.n, gChain P g i hn hi, N, hd, hwf, rfl, by simp [Host.whole],
    hostWF_whole (by omega), rfl, rfl, hNW, hc, hAt, e0, e1, e2⟩

/-- **The grade context holds** at a robust `UpTab`. -/
theorem holds_of_upTab {m : ℕ → ℕ} {h hp A : ℕ} (hn : 2 ≤ P.n)
    (hR : Robust A m fun m' => UpTab O P m' h hp A) : (gradeCtx O).holds P m h A :=
  fun m' hm' => upTab_gradeRaw hn (hR m' hm')

end proofs

end

end Chazelle.Core.Up
