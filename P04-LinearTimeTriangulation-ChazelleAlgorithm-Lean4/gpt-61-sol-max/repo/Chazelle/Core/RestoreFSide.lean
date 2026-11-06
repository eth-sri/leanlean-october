module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFBits
public import Chazelle.Core.RestoreFRef
public import Chazelle.Core.ShotListFrame

/-!
# WP-E, the search on the RAM (`FindOK`), part 18: the side of the witness and the child

In the piece chain's keys (`cmpA`): `81106 := [κ(u) ∈ (kA, kB)]` for the witness vertex
`(81183, 0)` and the chord ends `A = (81153, 81155)`, `B = (81154, 81155)`;
`81107 := [kS = kA ∨ kS ∈ (kA, kB)]` for the reference arc start `S = (81108, 81109)`; then
`81150 := lo` (`81118`) if the two bits agree, else `hi` (`81119`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- A chain descriptor below the search's base allocator stays readable. -/
theorem chain_keep {P : Polygon} {A : ℕ} {m m' : ℕ → ℕ} {D : ℕ} {H : Host} {Cα : Chain}
    (hwf : ChainWF P A m D) (hC : ChainDescAt m D (Qof P) H Cα) (he : ∀ a, a < A → m' a = m a)
    {A' : ℕ} (hA : A ≤ A') : ChainDescAt m' D (Qof P) H Cα ∧ ChainWF P A' m' D := by
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H Cα hC
  have h5 := hwf.1
  exact ⟨ShotList.chainDescAt_copy hC hEb he (fun j hj => he _ (by omega)),
    ShotList.chainWF_copy hwf hC he (fun j hj => he _ (by omega)) (by omega) hA⟩

/-- **Piece-chain comparison** with the descriptor fixed below the base allocator. -/
theorem cmpA_fs₀ (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r a b d e : ℕ} (hr : CmpR r) (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e) {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c.nreg 81133))
    (hC : ChainDescAt c₀.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hx : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg d, c.nreg e⟩)
    (hroom : c.nreg ALLOC + 11010 ≤ E.W) :
    FRS B E.P E.W c₀ (cmpA r a b d e) c 11010 (fun c' =>
      BitIs c' r ((chainModel Cα).key (Qof E.P) ⟨c.nreg a, c.nreg b⟩ <
        (chainModel Cα).key (Qof E.P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' (r + 1) ((chainModel Cα).key (Qof E.P) ⟨c.nreg d, c.nreg e⟩ <
        (chainModel Cα).key (Qof E.P) ⟨c.nreg a, c.nreg b⟩) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r → q ≠ r + 1 → c'.nreg q = c.nreg q) := by
  obtain ⟨hC', hwf'⟩ := chain_keep hwf hC (fun a ha => hI.hm a ha) hI.hA
  exact cmpA_fs hE hB hI hr ha hb hd he hka hkb hkd hke hwf' hC' hWm hx hy hroom

/-- The side computations and the choice. -/
def sideCh : Stmt :=
  .seq (cmpA 81100 81153 81155 81154 81155) (.seq (cmpA 81102 81153 81155 81183 81011)
    (.seq (cmpA 81104 81183 81011 81154 81155) (.seq (side3 81106 81100 81102 81104)
      (.seq (cmpA 81110 81153 81155 81108 81109) (.seq (cmpA 81112 81108 81109 81154 81155)
        (.seq (side3 81107 81100 81110 81112) (.seq (eqor 81107 81110 81111)
          (.seq (xnorR 81114 81106 81107)
            (.ifLtN 81011 81114 (Stmt.block [.copyN 81150 81118])
              (Stmt.block [.copyN 81150 81119]))))))))))

/-- The cost bound of `sideCh`. -/
def scK : ℕ := 5 * 11010 + 40

/-- The registers `sideCh` writes. -/
def ScW (q : ℕ) : Prop := KeyW q ∨ (81100 ≤ q ∧ q ≤ 81114) ∨ q = 81150

theorem sideCh_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c.nreg 81133))
    (hC : ChainDescAt c₀.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hpA : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg 81153, c.nreg 81155⟩)
    (hpB : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg 81154, c.nreg 81155⟩)
    (hpU : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg 81183, 0⟩)
    (hpS : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg 81108, c.nreg 81109⟩)
    (hroom : c.nreg ALLOC + scK ≤ E.W) :
    FRS B E.P E.W c₀ sideCh c scK (fun c' =>
      let k := fun (x : WPos) => (chainModel Cα).key (Qof E.P) x
      let kA := k ⟨c.nreg 81153, c.nreg 81155⟩
      let kB := k ⟨c.nreg 81154, c.nreg 81155⟩
      let kU := k ⟨c.nreg 81183, 0⟩
      let kS := k ⟨c.nreg 81108, c.nreg 81109⟩
      ((sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) → c'.nreg 81150 = c.nreg 81118) ∧
      (¬ (sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) →
        c'.nreg 81150 = c.nreg 81119) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ ScW q → c'.nreg q = c.nreg q) := by
  have nk : ∀ q, 81000 ≤ q → q < 82000 → ¬ KeyW q := fun q h1 h2 h => by omega_nf
  have ir : ∀ q, 81000 ≤ q → q < 82000 → InR q := fun q h1 h2 => ⟨by omega, by omega⟩
  -- the registers read
  let Rd : ℕ → Prop := fun q => q = 81108 ∨ q = 81109 ∨ q = 81118 ∨ q = 81119 ∨ q = 81133 ∨
    q = 81153 ∨ q = 81154 ∨ q = 81155 ∨ q = 81183
  have keep : ∀ (c₁ c₂ : Config) (r : ℕ), (∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r →
      q ≠ r + 1 → c₂.nreg q = c₁.nreg q) → 81100 ≤ r →
      (r + 1 ≤ 81107 ∨ (81110 ≤ r ∧ r + 1 ≤ 81114)) → ∀ q, Rd q → c₂.nreg q = c₁.nreg q := by
    intro c₁ c₂ r f h1 h2 q hq
    simp only [Rd] at hq
    exact f q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega)
  have keepb : ∀ (c₁ c₂ : Config) (r : ℕ), BitFr r c₁ c₂ → 81100 ≤ r → r ≤ 81114 →
      r ≠ 81108 → r ≠ 81109 → ∀ q, Rd q → c₂.nreg q = c₁.nreg q := by
    intro c₁ c₂ r f h1 h2 h3 h4 q hq
    simp only [Rd] at hq
    exact f q (by omega)
  have mA := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show PosOK Cα (Qof E.P) E.P.n ⟨c'.nreg 81153, c'.nreg 81155⟩ by
      grind
  have mB := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show PosOK Cα (Qof E.P) E.P.n ⟨c'.nreg 81154, c'.nreg 81155⟩ by
      grind
  have mU := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) (hI' : FInv E.W c₀ c') =>
    show PosOK Cα (Qof E.P) E.P.n ⟨c'.nreg 81183, c'.nreg 81011⟩ by
      rw [h 81183 (by simp [Rd]), k0_of hE hI']; exact hpU
  have mS := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show PosOK Cα (Qof E.P) E.P.n ⟨c'.nreg 81108, c'.nreg 81109⟩ by
      grind
  have mD := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show c'.nreg 81133 = c.nreg 81133 from h 81133 (by simp [Rd])
  have hAW : c.nreg ALLOC + scK ≤ E.W := hroom
  unfold scK at hAW
  -- the comparisons
  have r0 : ∀ q, Rd q → c.nreg q = c.nreg q := fun _ _ => rfl
  refine (FRS.seq (K₂ := 4 * 11010 + 40) (cmpA_fs₀ hE hB hI (r := 81100) ⟨by norm_num, by norm_num⟩
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num)) hwf hC hWm
    (mA c r0) (mB c r0) (by omega)) (fun c₁ hI₁ hA₁ ⟨b0, _, f₁⟩ => ?_)).mono
    (by omega_nf) (fun _ h => h)
  have p1 := keep c c₁ 81100 f₁ (by norm_num) (by norm_num)
  refine (FRS.seq (K₂ := 3 * 11010 + 40) (cmpA_fs₀ hE hB hI₁ (r := 81102) ⟨by norm_num, by norm_num⟩
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (by rw [mD c₁ p1]; exact hwf) (by rw [mD c₁ p1]; exact hC) hWm
    (mA c₁ p1) (mU c₁ p1 hI₁) (by omega)) (fun c₂ hI₂ hA₂ ⟨b2, _, f₂⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have p2 : ∀ q, Rd q → c₂.nreg q = c.nreg q := fun q hq => by
    rw [keep c₁ c₂ 81102 f₂ (by norm_num) (by norm_num) q hq,
      p1 q hq]
  refine (FRS.seq (K₂ := 2 * 11010 + 40) (cmpA_fs₀ hE hB hI₂ (r := 81104) ⟨by norm_num, by norm_num⟩
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (by rw [mD c₂ p2]; exact hwf) (by rw [mD c₂ p2]; exact hC) hWm
    (mU c₂ p2 hI₂) (mB c₂ p2) (by omega)) (fun c₃ hI₃ hA₃ ⟨b4, _, f₃⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have p3 : ∀ q, Rd q → c₃.nreg q = c.nreg q := fun q hq => by
    rw [keep c₂ c₃ 81104 f₃ (by norm_num) (by norm_num) q hq,
      p2 q hq]
  -- the bits in `c₃`
  have b0₃ : BitIs c₃ 81100 _ := b0.of_eq (by
    rw [f₃ _ (by norm_num) (by norm_num) (nk _ (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num), f₂ _ (by norm_num) (by norm_num) (nk _ (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)])
  have b2₃ : BitIs c₃ 81102 _ := b2.of_eq (f₃ _ (by norm_num) (by norm_num)
    (nk _ (by norm_num) (by norm_num)) (by norm_num) (by norm_num))
  refine (FRS.seq (K₂ := 2 * 11010 + 32) (side3_fs hE hB hI₃ (r := 81106) ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) b0₃ b2₃ b4)
    (fun c₄ hI₄ hA₄ ⟨b6, f₄⟩ => ?_)).mono (by omega) (fun _ h => h)
  have p4 : ∀ q, Rd q → c₄.nreg q = c.nreg q := fun q hq => by
    rw [keepb c₃ c₄ 81106 f₄ (by norm_num) (by norm_num) (by norm_num) (by norm_num) q hq, p3 q hq]
  refine (FRS.seq (K₂ := 11010 + 32) (cmpA_fs₀ hE hB hI₄ (r := 81110) ⟨by norm_num, by norm_num⟩
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (by rw [mD c₄ p4]; exact hwf) (by rw [mD c₄ p4]; exact hC) hWm
    (mA c₄ p4) (mS c₄ p4) (by omega)) (fun c₅ hI₅ hA₅ ⟨b10, b11, f₅⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have p5 : ∀ q, Rd q → c₅.nreg q = c.nreg q := fun q hq => by
    rw [keep c₄ c₅ 81110 f₅ (by norm_num) (by norm_num) q hq,
      p4 q hq]
  refine (FRS.seq (K₂ := 32) (cmpA_fs₀ hE hB hI₅ (r := 81112) ⟨by norm_num, by norm_num⟩
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (ir _ (by norm_num) (by norm_num)) (ir _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (nk _ (by norm_num) (by norm_num)) (nk _ (by norm_num) (by norm_num))
    (by rw [mD c₅ p5]; exact hwf) (by rw [mD c₅ p5]; exact hC) hWm
    (mS c₅ p5) (mB c₅ p5) (by omega)) (fun c₆ hI₆ hA₆ ⟨b12, _, f₆⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have p6 : ∀ q, Rd q → c₆.nreg q = c.nreg q := fun q hq => by
    rw [keep c₅ c₆ 81112 f₆ (by norm_num) (by norm_num) q hq,
      p5 q hq]
  have g6 : ∀ q, 81100 ≤ q → q ≤ 81111 → c₆.nreg q = c₅.nreg q := fun q h1 h2 =>
    f₆ q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega)
  have g5 : ∀ q, 81100 ≤ q → q ≤ 81107 → c₅.nreg q = c₄.nreg q := fun q h1 h2 =>
    f₅ q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega)
  have b0₆ : BitIs c₆ 81100 _ := b0₃.of_eq (by
    rw [g6 _ (by norm_num) (by norm_num), g5 _ (by norm_num) (by norm_num), f₄ _ (by norm_num)])
  have b10₆ : BitIs c₆ 81110 _ := b10.of_eq (g6 _ (by norm_num) (by norm_num))
  have b11₆ : BitIs c₆ 81111 _ := b11.of_eq (g6 _ (by norm_num) (by norm_num))
  refine (FRS.seq (K₂ := 19) (side3_fs hE hB hI₆ (r := 81107) ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) b0₆ b10₆ b12)
    (fun c₇ hI₇ hA₇ ⟨b7, f₇⟩ => ?_)).mono (by omega) (fun _ h => h)
  refine (FRS.seq (K₂ := 14) (eqor_fs hE hB hI₇ (r := 81107) ⟨by norm_num, by norm_num⟩ b7
    (b10₆.of_eq (f₇ _ (by norm_num))) (b11₆.of_eq (f₇ _ (by norm_num))))
    (fun c₈ hI₈ hA₈ ⟨b7', f₈⟩ => ?_)).mono (by omega) (fun _ h => h)
  have b6₈ : BitIs c₈ 81106 _ := b6.of_eq (by
    rw [f₈ _ (by norm_num), f₇ _ (by norm_num), g6 _ (by norm_num) (by norm_num),
      g5 _ (by norm_num) (by norm_num)])
  refine (FRS.seq (K₂ := 3) (xnorR_fs hE hB hI₈ (r := 81114) ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) b6₈ b7') (fun c₉ hI₉ hA₉ ⟨b14, f₉⟩ => ?_)).mono (by omega)
    (fun _ h => h)
  have p9 : ∀ q, Rd q → c₉.nreg q = c.nreg q := fun q hq => by
    rw [keepb c₈ c₉ 81114 f₉ (by norm_num) (by norm_num) (by norm_num) (by norm_num) q hq,
      keepb c₇ c₈ 81107 f₈ (by norm_num) (by norm_num) (by norm_num) (by norm_num) q hq,
      keepb c₆ c₇ 81107 f₇ (by norm_num) (by norm_num) (by norm_num) (by norm_num) q hq, p6 q hq]
  -- rewrite the bits in `c`'s terms
  have z1 := k0_of hE hI₁
  have z2 := k0_of hE hI₂
  simp only [p1 81153 (by simp [Rd]), p1 81155 (by simp [Rd]), p1 81183 (by simp [Rd]), z1] at b2
  simp only [p2 81154 (by simp [Rd]), p2 81155 (by simp [Rd]), p2 81183 (by simp [Rd]), z2] at b4
  simp only [p4 81153 (by simp [Rd]), p4 81155 (by simp [Rd]), p4 81108 (by simp [Rd]),
    p4 81109 (by simp [Rd])] at b10 b11
  simp only [p5 81154 (by simp [Rd]), p5 81155 (by simp [Rd]), p5 81108 (by simp [Rd]),
    p5 81109 (by simp [Rd])] at b12
  -- the frame
  have frA : ∀ (c₁ c₂ : Config) (r : ℕ), (∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r →
      q ≠ r + 1 → c₂.nreg q = c₁.nreg q) → 81100 ≤ r → r + 1 ≤ 81114 → ∀ q, 80000 ≤ q →
      q < 90000 → ¬ KeyW q → ¬ (81100 ≤ q ∧ q ≤ 81114) → c₂.nreg q = c₁.nreg q :=
    fun c₁ c₂ r h h1 h2 q a b hk hr => h q a b hk (by omega) (by omega)
  have frB : ∀ (c₁ c₂ : Config) (r : ℕ), BitFr r c₁ c₂ → 81100 ≤ r → r ≤ 81114 → ∀ q, 80000 ≤ q →
      q < 90000 → ¬ KeyW q → ¬ (81100 ≤ q ∧ q ≤ 81114) → c₂.nreg q = c₁.nreg q :=
    fun c₁ c₂ r h h1 h2 q _ _ _ hr => h q (by omega)
  have F9 : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → ¬ (81100 ≤ q ∧ q ≤ 81114) →
      c₉.nreg q = c.nreg q := fun q a b hk hr => by
    rw [frB c₈ c₉ 81114 f₉ (by norm_num) (by norm_num) q a b hk hr,
      frB c₇ c₈ 81107 f₈ (by norm_num) (by norm_num) q a b hk hr,
      frB c₆ c₇ 81107 f₇ (by norm_num) (by norm_num) q a b hk hr,
      frA c₅ c₆ 81112 f₆ (by norm_num) (by norm_num) q a b hk hr,
      frA c₄ c₅ 81110 f₅ (by norm_num) (by norm_num) q a b hk hr,
      frB c₃ c₄ 81106 f₄ (by norm_num) (by norm_num) q a b hk hr,
      frA c₂ c₃ 81104 f₃ (by norm_num) (by norm_num) q a b hk hr,
      frA c₁ c₂ 81102 f₂ (by norm_num) (by norm_num) q a b hk hr,
      frA c c₁ 81100 f₁ (by norm_num) (by norm_num) q a b hk hr]
  -- the decision bit
  rw [p1 81153 (by simp [Rd]), p1 81155 (by simp [Rd]), p1 81183 (by simp [Rd]), z1,
    p2 81183 (by simp [Rd]), z2, p2 81154 (by simp [Rd]), p2 81155 (by simp [Rd]),
    p4 81153 (by simp [Rd]), p4 81155 (by simp [Rd]), p4 81108 (by simp [Rd]),
    p4 81109 (by simp [Rd]), p5 81108 (by simp [Rd]), p5 81109 (by simp [Rd]),
    p5 81154 (by simp [Rd]), p5 81155 (by simp [Rd])] at b14
  set kA := (chainModel Cα).key (Qof E.P) ⟨c.nreg 81153, c.nreg 81155⟩ with hkA
  set kB := (chainModel Cα).key (Qof E.P) ⟨c.nreg 81154, c.nreg 81155⟩ with hkB
  set kU := (chainModel Cα).key (Qof E.P) ⟨c.nreg 81183, 0⟩ with hkU
  set kS := (chainModel Cα).key (Qof E.P) ⟨c.nreg 81108, c.nreg 81109⟩ with hkS
  have hY : ((kA < kB ∧ (kA < kS ∧ kS < kB)) ∨ (¬ kA < kB ∧ (kA < kS ∨ kS < kB))) ∨
      (¬ kA < kS ∧ ¬ kS < kA) ↔ (kS = kA ∨ sideInArc kA kB kS) := by
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inr ((sideInArc_iff' _ _ _).2 h)
      · exact Or.inl (le_antisymm (not_lt.1 h1) (not_lt.1 h2))
    · rintro (h | h)
      · right; rw [h]; exact ⟨lt_irrefl _, lt_irrefl _⟩
      · exact Or.inl ((sideInArc_iff' _ _ _).1 h)
  have hiff : c₉.nreg 81114 = 1 ↔ (sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) :=
    b14.2.trans (iff_congr (sideInArc_iff' _ _ _).symm hY)
  have k0₉ := k0_of hE hI₉
  have fin : ∀ c' : Config, (∀ q, q ≠ 81150 → c'.nreg q = c₉.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ ScW q → c'.nreg q = c.nreg q := fun c' h q a b hq => by
    rw [h q (fun e => hq (Or.inr (Or.inr e))), F9 q a b (fun e => hq (Or.inl e))
      (fun e => hq (Or.inr (Or.inl e)))]
  by_cases a1 : c₉.nreg 81011 < c₉.nreg 81114
  · have hb : c₉.nreg 81114 = 1 := by have := b14.1; omega
    have ok : okB E.W c₉.nmem [.copyN 81150 81118] c₉.nreg := by
      simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
    refine (FRS.ifT a1 (FRS.block hB _ hI₉ ok)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₉.nmem [.copyN 81150 81118] c₉.nreg q := fun q => by rw [h']
    have v : c'.nreg 81150 = c.nreg 81118 := by
      rw [e']; simp [regB, regI, upd]; exact p9 81118 (by simp [Rd])
    exact ⟨fun _ => v, fun h => absurd (hiff.1 hb) h,
      fin c' (fun q hq => by rw [e']; simp [regB, regI, upd, hq])⟩
  · 
    have ok : okB E.W c₉.nmem [.copyN 81150 81119] c₉.nreg := by
      simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
    refine (FRS.ifF a1 (FRS.block hB _ hI₉ ok)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₉.nmem [.copyN 81150 81119] c₉.nreg q := fun q => by rw [h']
    have v : c'.nreg 81150 = c.nreg 81119 := by
      rw [e']; simp [regB, regI, upd]; exact p9 81119 (by simp [Rd])
    exact ⟨fun h => absurd (hiff.2 h) (by omega), fun _ => v,
      fin c' (fun q hq => by rw [e']; simp [regB, regI, upd, hq])⟩

end

end Restore

end Chazelle.Core
