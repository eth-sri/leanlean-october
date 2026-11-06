module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFTest
public import Chazelle.Core.RestoreTDisp
public import Chazelle.Core.RestoreTSetup

/-!
# WP-E, the search on the RAM (`FindOK`), part 4: comparing keys of the host walk

`fKey a b d e`: set the registers the key primitives read (`83020` the chain descriptor address
`MD + 1`, `83021` the model header word, `83022 = 0`, `83023 = 1`, `83000 = MD`), then run the
test's dispatcher `gKey`: bits `50210` (`key x < key y`) and `50211` (`key y < key x`) for the
positions `x = (a, b)`, `y = (d, e)` of the host model.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

/-- The setup of a key comparison. -/
def fKeySetL : List Instr := [.addN 83020 81000 81012, .loadN 83021 81000, .constN 83022 0,
  .constN 83023 1, .copyN 83000 81000]

/-- **A key comparison** of the host positions `(a, b)` and `(d, e)`. -/
def fKey (a b d e : ℕ) : Stmt := .seq (Stmt.block fKeySetL) (gKey a b d e)

theorem fKeySet_eff (m f : ℕ → ℕ) :
    regB m fKeySetL f 83020 = f 81000 + f 81012 ∧ regB m fKeySetL f 83021 = m (f 81000) ∧
      regB m fKeySetL f 83022 = 0 ∧ regB m fKeySetL f 83023 = 1 ∧
      regB m fKeySetL f 83000 = f 81000 ∧
      ∀ q, q ≠ 83000 → q ≠ 83020 → q ≠ 83021 → q ≠ 83022 → q ≠ 83023 →
        regB m fKeySetL f q = f q := by
  simp_all [fKeySetL, regB, regI, upd, List.mem_cons, List.not_mem_nil, or_false, dstI] <;> omega_nf

variable {E : FEnv} {c₀ c : Config}

/-- The registers a key comparison writes in band `bRestore`. -/
def KeyW (q : ℕ) : Prop := q = 83000 ∨ (83020 ≤ q ∧ q ≤ 83023)

/-- **A key comparison** as a run step of the search. -/
theorem fKey_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {a b d e : ℕ} (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e)
    (hx : PosG E.M (Qof E.P) E.P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : PosG E.M (Qof E.P) E.P.n ⟨c.nreg d, c.nreg e⟩)
    (hroom : c.nreg ALLOC + 11020 ≤ E.W) :
    FRS B E.P E.W c₀ (fKey a b d e) c 11020 (fun c' =>
      BitIs c' 50210 (E.M.key (Qof E.P) ⟨c.nreg a, c.nreg b⟩ <
        E.M.key (Qof E.P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' 50211 (E.M.key (Qof E.P) ⟨c.nreg d, c.nreg e⟩ <
        E.M.key (Qof E.P) ⟨c.nreg a, c.nreg b⟩) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → c'.nreg q = c.nreg q) := by
  have hag := hI.agree hE
  have hA := hI.allocA hE
  obtain ⟨hMD, hwf⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
  have hwfc := hwf.mono hA
  have i0 : c.nreg 81000 = E.MD := by rw [hI.hin _ (by omega_nf), hE.i0]
  have k1 : c.nreg 81012 = 1 := by rw [hI.hin _ (by omega_nf), hE.k1]
  
  have hMD6 : E.MD + 6 ≤ c.nreg ALLOC := le_trans hwf.1 hA
  have ok : okB E.W c.nmem fKeySetL c.nreg := by
    simp_all [fKeySetL, okB, okI, FScr, FOut] <;> omega_nf
  refine (FRS.seq (K₂ := 11010) (FRS.block hB fKeySetL hI ok) (fun c₁ hI₁ _ h₁ => ?_)).mono
    (by simp [fKeySetL]) (fun _ h => h)
  obtain ⟨s20, s21, s22, s23, s00, sfr⟩ := fKeySet_eff c.nmem c.nreg
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem fKeySetL c.nreg q := fun q => by rw [h₁]
  have m₁ : c₁.nmem = c.nmem := by rw [h₁]
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := by
    grind [ALLOC]
  have f₁ : ∀ q, ¬ KeyW q → c₁.nreg q = c.nreg q := fun q hq => by
    unfold KeyW at hq
    grind
  have r20 : c₁.nreg 83020 = E.MD + 1 := by ram_grind
  have r21 : c₁.nreg 83021 = c.nmem E.MD := by ram_grind
  have r22 : c₁.nreg 83022 = 0 := by rw [e₁, s22]
  have r23 : c₁.nreg 83023 = 1 := by rw [e₁, s23]
  have r00 : c₁.nreg 83000 = E.MD := by ram_grind
  have hx₁ : PosG E.M (Qof E.P) E.P.n ⟨c₁.nreg a, c₁.nreg b⟩ := by ram_grind
  have hy₁ : PosG E.M (Qof E.P) E.P.n ⟨c₁.nreg d, c₁.nreg e⟩ := by ram_grind
  rw [← f₁ a hka, ← f₁ b hkb, ← f₁ d hkd, ← f₁ e hke]
  have hfin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → c'.nreg q = c.nreg q := fun c' h q h1 h2 hq =>
    (h q h1 h2).trans (f₁ q hq)
  rcases hMD with ⟨h0, H, C, hC, hM⟩ | ⟨h1, hbit, hM⟩
  · -- a chain model
    have hx' : PosOK C (Qof E.P) E.P.n ⟨c₁.nreg a, c₁.nreg b⟩ := by
      rw [hM] at hx₁; exact ⟨hx₁.1, hx₁.2.1, hx₁.2.2 C rfl⟩
    have hy' : PosOK C (Qof E.P) E.P.n ⟨c₁.nreg d, c₁.nreg e⟩ := by
      rw [hM] at hy₁; exact ⟨hy₁.1, hy₁.2.1, hy₁.2.2 C rfl⟩
    have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 83020) (Qof E.P) H C := by ram_grind
    have hwf₁ : ChainWF E.P (c₁.nreg ALLOC) c₁.nmem (c₁.nreg 83020) := by
      rw [m₁, r20, hA₁]; exact hwfc.2 h0
    obtain ⟨c', k, ex, hk, b1, b2, hf⟩ := keyCmp_exec ha hb hd he hI₁.hw hE.hG hE.hWh hwf₁ hC₁
      r22 hx' hy' (walk_le_W hE.hMD hE.hwf hE.hWh hM) (by omega)
    have h8 : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c₁.nreg q := fun q h1 h2 =>
      hf.1 q (by rw [band8 h1 h2]; simp [primBands, bRestore, bSign, bLocate])
        (by omega_nf)
    refine FRS.prim hB hI₁ (.ifLtN_true (by omega) ex) hf (by omega) (by omega)
      ⟨by ram_grind, by ram_grind, hfin c' h8⟩
  · -- the interior model
    have hn := interior_n (P := E.P)
    have hD : c₁.nreg 83000 + 1 ≤ E.W := by omega
    have hmd : c₁.nmem (c₁.nreg 83000 + 1) = c.nmem (E.MD + 1) := by rw [m₁, r00]
    rw [hM] at hx₁ hy₁
    obtain ⟨c', k, ex, hk, b1, b2⟩ := iKey_exec (P := E.P) (a := a) (b := b) (d := d) (e := e)
      hE.hG (by have := hE.hWh; grind [hostWords]) hI₁.hw hbit hmd hD
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          grind [InR])
      hx₁.2.1 hy₁.2.1 (by rw [← hn]; exact hx₁.1) (by rw [← hn]; exact hy₁.1)
    have hfr : FrameB Bik c₁ c' := exec_frameB ex (wr_iKey a b d e)
    have hf := frame_of_frameB hfr Bik_band k
    have h8 : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c₁.nreg q := fun q h1 h2 =>
      hf.1 q (by rw [band8 h1 h2]; simp [primBands, bRestore, bSign, bLocate])
        (by omega_nf)
    refine FRS.prim hB hI₁ (.ifLtN_false (by omega) ex) hf (by omega)
      (by omega) ⟨by ram_grind, by ram_grind, hfin c' h8⟩

end

end Restore

end Chazelle.Core
