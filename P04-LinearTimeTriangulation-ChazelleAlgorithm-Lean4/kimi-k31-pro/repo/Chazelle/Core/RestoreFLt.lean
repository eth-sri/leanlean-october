module

public import Chazelle.Core.RestoreFKey
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# WP-E, the search on the RAM (`FindOK`), part 8: key comparisons into registers

* `cmpM r a b d e`: `r := [key x < key y]`, `r + 1 := [key y < key x]` for the positions
  `x = (a, b)`, `y = (d, e)` of the host model (`fKey`);
* `cmpA r a b d e`: the same for the chain model of the piece chain whose descriptor address is
  in `81133` (`keyCmp`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

/-- **Host key comparison** into `r`, `r + 1`. -/
def cmpM (r a b d e : ℕ) : Stmt :=
  .seq (fKey a b d e) (Stmt.block [.copyN r 50210, .copyN (r + 1) 50211])

/-- The setup of a comparison in the piece's chain model. -/
def cmpAL : List Instr := [.copyN 83020 81133, .constN 83022 0]

/-- **Piece-chain key comparison** into `r`, `r + 1`. -/
def cmpA (r a b d e : ℕ) : Stmt :=
  .seq (Stmt.block cmpAL) (.seq (keyCmp a b d e)
    (Stmt.block [.copyN r 50210, .copyN (r + 1) 50211]))

variable {E : FEnv} {c₀ c : Config}

/-- The output registers of a comparison: band `bRestore`, scratch, not a key register. -/
def CmpR (r : ℕ) : Prop := 81028 ≤ r ∧ r + 1 < 83000

theorem copy2 {c₁ : Config} {r : ℕ} (hr : CmpR r) (hI₁ : FInv E.W c₀ c₁) {B : Finset ℕ}
    (hB : dBands ⊆ B) :
    FRS B E.P E.W c₀ (Stmt.block [.copyN r 50210, .copyN (r + 1) 50211]) c₁ 2 (fun c' =>
      c'.nreg r = c₁.nreg 50210 ∧ c'.nreg (r + 1) = c₁.nreg 50211 ∧
      ∀ q, q ≠ r → q ≠ r + 1 → c'.nreg q = c₁.nreg q) := by
  unfold CmpR at hr
  have ok : okB E.W c₁.nmem [.copyN r 50210, .copyN (r + 1) 50211] c₁.nreg := by
    simp only [okB, okI]
    exact ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), Or.inl (Or.inl ⟨by omega, by omega⟩), trivial⟩
  refine (FRS.block hB _ hI₁ ok).mono (by simp) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c₁.nmem [.copyN r 50210, .copyN (r + 1) 50211] c₁.nreg q :=
    fun q => by rw [h']
  refine ⟨by rw [e']; simp [regB, regI, upd], by rw [e']; simp [regB, regI, upd,
      show (50211 : ℕ) ≠ r by omega], fun q h1 h2 => by rw [e']; simp [regB, regI, upd, h1, h2]⟩

/-- **Host key comparison** as a run step of the search. -/
theorem cmpM_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r a b d e : ℕ} (hr : CmpR r) (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e)
    (hx : PosG E.M (Qof E.P) E.P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : PosG E.M (Qof E.P) E.P.n ⟨c.nreg d, c.nreg e⟩)
    (hroom : c.nreg ALLOC + 11022 ≤ E.W) :
    FRS B E.P E.W c₀ (cmpM r a b d e) c 11022 (fun c' =>
      BitIs c' r (E.M.key (Qof E.P) ⟨c.nreg a, c.nreg b⟩ <
        E.M.key (Qof E.P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' (r + 1) (E.M.key (Qof E.P) ⟨c.nreg d, c.nreg e⟩ <
        E.M.key (Qof E.P) ⟨c.nreg a, c.nreg b⟩) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r → q ≠ r + 1 → c'.nreg q = c.nreg q) := by
  refine FRS.seq (K₂ := 2) (fKey_fs hE hB hI ha hb hd he hka hkb hkd hke hx hy
    (by omega)) (fun c₁ hI₁ _ ⟨b1, b2, f1⟩ => ?_)
  refine (copy2 hr hI₁ hB).mono le_rfl (fun c' ⟨v1, v2, f2⟩ => ⟨b1.of_eq v1, b2.of_eq v2,
    fun q h1 h2 h3 h4 h5 => by rw [f2 q h4 h5, f1 q h1 h2 h3]⟩)

/-- **Piece-chain key comparison** as a run step of the search. -/
theorem cmpA_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r a b d e : ℕ} (hr : CmpR r) (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e) {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c.nreg ALLOC) c.nmem (c.nreg 81133))
    (hC : ChainDescAt c.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hx : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg d, c.nreg e⟩)
    (hroom : c.nreg ALLOC + 11010 ≤ E.W) :
    FRS B E.P E.W c₀ (cmpA r a b d e) c 11010 (fun c' =>
      BitIs c' r ((chainModel Cα).key (Qof E.P) ⟨c.nreg a, c.nreg b⟩ <
        (chainModel Cα).key (Qof E.P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' (r + 1) ((chainModel Cα).key (Qof E.P) ⟨c.nreg d, c.nreg e⟩ <
        (chainModel Cα).key (Qof E.P) ⟨c.nreg a, c.nreg b⟩) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r → q ≠ r + 1 → c'.nreg q = c.nreg q) := by
  have ok : okB E.W c.nmem cmpAL c.nreg := by
    simp only [cmpAL, okB, okI]
    refine ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
      ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by omega⟩, trivial⟩
  refine FRS.seq (K₂ := 11008) (FRS.block hB _ hI ok) (fun c₁ hI₁ hA₁ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem cmpAL c.nreg q := fun q => by rw [h₁]
  have m₁ : c₁.nmem = c.nmem := by rw [h₁]
  have r20 : c₁.nreg 83020 = c.nreg 81133 := by rw [e₁]; simp [cmpAL, regB, regI, upd]
  have r22 : c₁.nreg 83022 = 0 := by rw [e₁]; simp [cmpAL, regB, regI, upd]
  have f₁ : ∀ q, q ≠ 83020 → q ≠ 83022 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₁]; simp [cmpAL, regB, regI, upd, h1, h2]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by ufo ALLOC)
    (by ufo ALLOC)
  have kf : ∀ q, ¬ KeyW q → c₁.nreg q = c.nreg q := fun q hq => by
    unfold KeyW at hq; exact f₁ q (by omega) (by omega)
  have hx₁ : PosOK Cα (Qof E.P) E.P.n ⟨c₁.nreg a, c₁.nreg b⟩ := by
    rwx [kf a hka, kf b hkb]
  have hy₁ : PosOK Cα (Qof E.P) E.P.n ⟨c₁.nreg d, c₁.nreg e⟩ := by
    rwx [kf d hkd, kf e hke]
  obtain ⟨c₂, k₂, ex, hk, b1, b2, hf⟩ := keyCmp_exec ha hb hd he hI₁.hw hE.hG hE.hWh
    (by rwx [m₁, r20, hA₁']) (by rwx [m₁, r20]) r22 hx₁ hy₁ hWm
    (by rwo [hA₁'])
  have h8 : ∀ q, 80000 ≤ q → q < 90000 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    hf.1 q (by rw [band8 h1 h2]; simp [primBands, bRestore, bSign, bLocate])
      (by ufo ALLOC)
  refine FRS.seq (K₂ := 2) (FRS.prim (Q := fun c' => c' = c₂) hB hI₁ ex hf le_rfl (by omega) rfl)
    (fun c₃ hI₃ _ h₃ => ?_)
  subst h₃
  rw [kf a hka, kf b hkb, kf d hkd, kf e hke] at b1 b2
  refine (copy2 hr hI₃ hB).mono le_rfl (fun c' ⟨v1, v2, f2⟩ => ⟨b1.of_eq v1, b2.of_eq v2,
    fun q h1 h2 h3 h4 h5 => by rw [f2 q h4 h5, h8 q h1 h2, kf q h3]⟩)

end

end Restore

end Chazelle.Core
