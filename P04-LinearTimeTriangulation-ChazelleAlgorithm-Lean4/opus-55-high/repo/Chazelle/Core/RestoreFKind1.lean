module

public import Chazelle.MacT
public import Chazelle.Core.RestoreFNode
public import Chazelle.Core.RestoreFEndP
public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.DownPhaseOracleArc
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.GranInitL3

section
set_option hygiene false
local macro "zqsx" : tactic => `(tactic| (simp only [okB, okI, FScr, FOut]; norm_num))
local macro "zqta" : tactic => `(tactic| (refine ⟨?_, fun q hq => by zvmwg; zumyf; simp_all⟩; zvmwg; zumxt))
local macro "zqtb" : tactic => `(tactic| refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨?_, f₁⟩)).mono by_omega ztb)
local macro "zqtc" : tactic => `(tactic| rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega])
local macro "zqtd" : tactic => `(tactic| refine (FRS.ifF a ztpyk).mono by_simp zthi)
local macro "zqte" : tactic => `(tactic| (refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩))
local macro "zqtf" : tactic => `(tactic| intro reg ai bi aj bj dX regα T hD hJa hJr)
local macro "zqtg" : tactic => `(tactic| (have n17 : ztuoj := by zunic))
local macro "zqth" : tactic => `(tactic| refine (FRS.block hB _ hI ok).mono by_rfl zthi)
set_option hygiene true

/-!
# WP-E, the search on the RAM (`FindOK`), part 23: a kind-1 piece

The piece record at `81080` (seven words: the ends, the kind, the chain descriptor `Dα`, the
normal-form handle `Bα`).  Read the chain (`s`, `m`, top index, side bit), decide the direction
of the piece's walk (one height-vertex test of its first vertex), compute `g' = 6 + tpos J` and
the stretch lengths `L₁`, `L₂`; test the piece ends and the junction; descend each stretch.
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs NFLoc

/-- The reads of the piece and its chain. -/
def k1L : List Instr :=
  [.loadN 81089 81080, .addN 81090 81080 81015, .loadN 81133 81090, .addN 81090 81090 81012,
    .loadN 81134 81090, .addN 81090 81133 81012, .loadN 81082 81090, .addN 81090 81090 81012,
    .loadN 81081 81090, .addN 81090 81090 81012, .loadN 81083 81090, .addN 81090 81090 81012,
    .loadN 81084 81090]
variable {E : FEnv} {c₀ c : Config}
theorem k1Load_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hPR : c.nreg 81080 + 6 < c₀.nreg ALLOC) {Hs : Host} {Cα : Chain}
    (hCD : ChainDescAt c₀.nmem ztyiz zti Hs Cα)
    (hwf : ChainWF E.P ztdq c₀.nmem ztyiz) :
    FRS B E.P E.W c₀ ztvdl c 13 (fun c' =>
      c'.nreg 81089 = c₀.nmem ztcuw ∧
      c'.nreg 81133 = c₀.nmem ztczb ∧ c'.nreg 81134 = c₀.nmem ztlla ∧
      c'.nreg 81082 = Cα.s ∧ c'.nreg 81081 = Cα.m ∧ c'.nreg 81083 = Cα.topIdx ∧
      (c'.nreg 81084 = 1 ↔ Cα.sideBeta = true) ∧
      ∀ q, q ≠ 81081 → q ≠ 81082 → q ≠ 81083 → q ≠ 81084 → q ≠ 81089 → q ≠ 81090 →
        q ≠ 81133 → q ≠ 81134 → c'.nreg q = c.nreg q) := by
  zubnp
  zuki
  zugmr
  zumbo
  zuwl
  zuhr
  have m5 : c.nmem _ = c₀.nmem ztczb := hm _ by_omega
  have ea : ∀ j, j ≤ 4 → c.nmem _ =
      c₀.nmem (c₀.nmem ztczb + j) := fun j hj => hm _ by_omega
  have ok : okB E.W c.nmem k1L c.nreg := by
    simp only [k1L, okB, okI, regI, upd, FScr, FOut, k5, k1]
    grind
  zqth
  have e' : ∀ q, c'.nreg q = regB c.nmem k1L c.nreg q := by_simp_all
  obtain ⟨-, -, h1, h2, h3, h4⟩ := hCD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q a1 a2 a3 a4 a5 a6 a7 a8 => ?_⟩
  · zvmwg; simp [k1L, regB, regI, upd]; grind
  · zvmwg; simp [k1L, regB, regI, upd, k5]; exact m5
  · zvmwg; simp [k1L, regB, regI, upd, k5, k1]; simp_all
  · zvmwg; simp [k1L, regB, regI, upd, k5, k1, m5]; simp_all
  · zuts

  · zuts

  · zuts

  · zuczs
    simp only [k1L, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zubzs

/-- The direction: `J = 0` (`81085`) if the first vertex of the piece is at the height of the
chain's first vertex, else `J = m`. -/
def k1Dir : Stmt :=
  .seq (Stmt.block [.copyN 81060 81089, .constN 81061 0]) (.seq ztvqi
    (.seq (Stmt.block [.copyN 81085 81081]) (ifEq 81062 81082 (Stmt.block [.constN 81085 0]))))
theorem k1Dir_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hs : c.nreg 81089 < E.M.W.n) (hset : VSet E (c.nreg 81089))
    (hroom : c.nreg ALLOC + hvK + 9 ≤ E.W) :
    FRS B E.P E.W c₀ k1Dir c ztobh (fun c' => ∃ h, h < E.P.n ∧
      ((Qof E.P).vtx h).2 = (E.M.pos zti ⟨c.nreg 81089, 0⟩).2 ∧
      c'.nreg 81085 = (if h = c.nreg 81082 then 0 else c.nreg 81081) ∧
      ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
        q ≠ 81085 → c'.nreg q = c.nreg q) := by
  have ok1 : okB E.W c.nmem [.copyN 81060 81089, .constN 81061 0] c.nreg := by
    zqsx
  refine FRS.seq (K₂ := hvK + 7) ztbbr ztiy |>.mono
    by_rfl ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81060 81089, .constN 81061 0] c.nreg q :=
    by simp_all
  have v60 : c₁.nreg 81060 = c.nreg 81089 := by_tauto
  have f₁ : zthpe := fun q a b => by
    zubei
  zudhe
  refine FRS.seq (K₂ := 7) (fHv_fs hE hB hI₁ (a := 81060) by_norm_num by_norm_num by_norm_num
    by_norm_num by_omega (by rw [v60]; tauto) by_omega)
    (fun c₂ hI₂ hA₂ ⟨hh, hy, f₂⟩ => ?_)
  rw [v60] at hy
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
      c₂.nreg q = c.nreg q := by_simp_all
  have ok3 : okB E.W c₂.nmem [.copyN 81085 81081] c₂.nreg := by
    zqsx
  refine FRS.seq (K₂ := 5) ztgdu ztcnf |>.mono
    by_simp ztb
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.copyN 81085 81081] c₂.nreg q := fun q => by zunbh
  have v85 : c₃.nreg 81085 = c.nreg 81081 := by
    zuexl
    grind
  have f₃ : ∀ q, q ≠ 81085 → c₃.nreg q = c₂.nreg q := fun q h => by
    zublu
  have u62 : c₃.nreg 81062 = c₂.nreg 81062 := by_grind
  have u82 : c₃.nreg 81082 = c.nreg 81082 := by
    grind
  have fin : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
      q ≠ 81085 → c₃.nreg q = c.nreg q := by_grind
  by_cases he : c₃.nreg 81062 = c₃.nreg 81082
  · have okz : okB E.W c₃.nmem [.constN 81085 0] c₃.nreg := by
      zqsx
    refine FRS.ifEq_eq he ((FRS.block hB _ hI₃ okz).mono by_simp zthi)
    have e' : ∀ q, c'.nreg q = regB c₃.nmem [.constN 81085 0] c₃.nreg q := fun q => by zvmxl
    refine ⟨c₂.nreg 81062, hh, hy, ?_, fun q a b h1 h2 h3 h4 h5 => ?_⟩
    · rw [u62, u82] at he; rw [e', ite_eq_left he]; rfl
    · zvmwg; simp [regB, regI, upd, h5]; grind
  · refine FRS.ifEq_ne hI₃ he ⟨c₂.nreg 81062, hh, hy, ?_, fin⟩
    grind

/-- The tour offset, the stretch lengths. -/
def k1Pos : Stmt :=
  .seq (Stmt.block [.addN 81091 81081 81081, .subN 81092 81091 81083])
    (.seq (ifEq 81084 81012 (Stmt.block [.copyN 81092 81083]))
      (.seq (Stmt.block [.addN 81086 81085 81091, .subN 81086 81086 81092])
        (.seq (.ifLtN 81086 81091 .skip (Stmt.block [.subN 81086 81086 81091]))
          (.seq (Stmt.block [.addN 81093 81086 81081])
            (.ifLtN 81091 81093 (Stmt.block [.subN 81087 81091 81086, .subN 81088 81081 81087])
              (Stmt.block [.copyN 81087 81081, .constN 81088 0]))))))
theorem k1Pos_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {Cα : Chain} (hm : c.nreg 81081 = Cα.m) (ht : c.nreg 81083 = Cα.topIdx)
    (hb : c.nreg 81084 = 1 ↔ Cα.sideBeta = true) (hJ : c.nreg 81085 ≤ Cα.m)
    (hW : 4 * Cα.m ≤ E.W) :
    FRS B E.P E.W c₀ k1Pos c 18 (fun c' =>
      c'.nreg 81086 = WalkEmbed.tpos Cα zteqy ∧ c'.nreg 81091 = 2 * Cα.m ∧
      (WalkEmbed.tpos Cα zteqy + Cα.m ≤ 2 * Cα.m →
        c'.nreg 81087 = Cα.m ∧ c'.nreg 81088 = 0) ∧
      (2 * Cα.m < WalkEmbed.tpos Cα zteqy + Cα.m →
        c'.nreg 81087 = 2 * Cα.m - WalkEmbed.tpos Cα zteqy ∧
        c'.nreg 81088 = Cα.m - (2 * Cα.m - WalkEmbed.tpos Cα zteqy)) ∧
      ∀ q, q ≠ 81086 → q ≠ 81087 → q ≠ 81088 → q ≠ 81091 → q ≠ 81092 → q ≠ 81093 →
        c'.nreg q = c.nreg q) := by
  have htop := Cα.topIdx_le
  zumbe
  have hbS := WalkEmbed.bS_le Cα
  have hbSd : WalkEmbed.bS Cα = if Cα.sideBeta then Cα.topIdx else 2 * Cα.m - Cα.topIdx := rfl
  -- 2m and 2m - top
  have ok1 : okB E.W c.nmem [.addN 81091 81081 81081, .subN 81092 81091 81083] c.nreg := by
    simp only [okB, okI, FScr, FOut, hm]; grind
  refine FRS.seq (K₂ := 16) ztbbr ztiy |>.mono
    by_simp ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.addN 81091 81081 81081, .subN 81092 81091 81083]
      c.nreg q := by_simp_all
  have v91 : c₁.nreg 81091 = 2 * Cα.m := by zumwx; simp [regB, regI, upd, hm]; ring
  have v92 : c₁.nreg 81092 = 2 * Cα.m - Cα.topIdx := by
    zumwx; simp [regB, regI, upd, hm, ht]; omega
  have f₁ : ∀ q, q ≠ 81091 → q ≠ 81092 → c₁.nreg q = c.nreg q := fun q a b => by
    zubei
  zubrc
  -- bS
  refine FRS.seq (K₁ := 5) (K₂ := 11) (Q₁ := fun c' => c'.nreg 81092 = WalkEmbed.bS Cα ∧
      ∀ q, q ≠ 81092 → c'.nreg q = c₁.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v92', f₂⟩ => ?_) |>.mono
    by_omega ztb
  · by_cases hβ : c₁.nreg 81084 = c₁.nreg 81012
    · have okc : okB E.W c₁.nmem [.copyN 81092 81083] c₁.nreg := by
        zqsx
      refine FRS.ifEq_eq hβ ((FRS.block hB _ hI₁ okc).mono by_simp zthi)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.copyN 81092 81083] c₁.nreg q := by_simp_all
      rw [k1₁, f₁ _ by_norm_num by_norm_num] at hβ
      zqte
      zvmwg; zumxd
      simp_all
    · refine FRS.ifEq_ne hI₁ hβ ztdiv
      simp_all
  -- J + 2m - bS, mod 2m
  have w85 : c₂.nreg 81085 = c.nreg 81085 := by
    simp_all
  have w91 : c₂.nreg 81091 = 2 * Cα.m := by_simp_all
  have ok3 : okB E.W c₂.nmem [.addN 81086 81085 81091, .subN 81086 81086 81092] c₂.nreg := by
    simp only [okB, okI, FScr, FOut, w85, w91]; grind
  refine FRS.seq (K₂ := 9) ztgdu ztcnf |>.mono
    by_simp ztb
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.addN 81086 81085 81091, .subN 81086 81086 81092]
      c₂.nreg q := by_simp_all
  have v86 : c₃.nreg 81086 = c.nreg 81085 + 2 * Cα.m - WalkEmbed.bS Cα := by
    zumzv; simp [regB, regI, upd, w85, w91, v92']
  have f₃ : ∀ q, q ≠ 81086 → c₃.nreg q = c₂.nreg q := fun q h => by
    zublu
  have x91 : c₃.nreg 81091 = 2 * Cα.m := by_grind
  refine FRS.seq (K₁ := 3) (K₂ := 5) (Q₁ := fun c' =>
      c'.nreg 81086 = WalkEmbed.tpos Cα zteqy ∧ ∀ q, q ≠ 81086 → c'.nreg q = c₃.nreg q)
    ?_ (fun c₄ hI₄ hA₄ ⟨v86', f₄⟩ => ?_) |>.mono by_omega ztb
  · unfold WalkEmbed.tpos
    by_cases a : c₃.nreg 81086 < c₃.nreg 81091
    · refine (FRS.ifT a (FRS.skip (K := 0) hI₃ ztdiv)).mono by_omega
        ztb
      rw [v86, x91] at a; rw [v86, Nat.mod_eq_of_lt a]
    · have okm : okB E.W c₃.nmem [.subN 81086 81086 81091] c₃.nreg := by
        zqsx
      zuhio
      have e' : ∀ q, c'.nreg q = regB c₃.nmem [.subN 81086 81086 81091] c₃.nreg q := fun q => by
        zuczu
      zqte
      zujn
      rw [v86, x91] at *
      zqtc
  -- L₁, L₂
  have tl := WalkEmbed.tpos_lt Cα zteqy
  have y81 : ztusx := by
    grind
  have y91 : c₄.nreg 81091 = 2 * Cα.m := by_grind
  have ok5 : okB E.W c₄.nmem [.addN 81093 81086 81081] c₄.nreg := by
    simp only [okB, okI, FScr, FOut, v86', y81]; grind
  refine FRS.seq (K₂ := 4) ztpyo zthgv |>.mono
    by_simp ztb
  have e₅ : ∀ q, c₅.nreg q = regB c₄.nmem [.addN 81093 81086 81081] c₄.nreg q := fun q => by
    zueyl
  have v93 : c₅.nreg 81093 = WalkEmbed.tpos Cα zteqy + Cα.m := by
    zunkr; simp [regB, regI, upd, v86', y81]
  have f₅ : ∀ q, q ≠ 81093 → c₅.nreg q = c₄.nreg q := fun q h => by
    zunkr; zundx
  have z86 : c₅.nreg 81086 = WalkEmbed.tpos Cα zteqy := by_grind
  have z81 : c₅.nreg 81081 = Cα.m := by_grind
  have z91 : c₅.nreg 81091 = 2 * Cα.m := by_grind
  have fr : ∀ q, q ≠ 81086 → q ≠ 81087 → q ≠ 81088 → q ≠ 81091 → q ≠ 81092 → q ≠ 81093 →
      c₅.nreg q = c.nreg q := by_grind
  by_cases a : c₅.nreg 81091 < c₅.nreg 81093
  · have oka : okB E.W c₅.nmem [.subN 81087 81091 81086, .subN 81088 81081 81087] c₅.nreg := by
      zqsx
    refine (FRS.ifT a ztpyp).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₅.nmem [.subN 81087 81091 81086, .subN 81088 81081 81087]
        c₅.nreg q := fun q => by zvmxl
    zuinh
    refine ⟨by zvmwg; tauto, by zvmwg; tauto,
      by grind, fun _ => ⟨by zvmwg; simp [regB, regI, upd, z91, z86],
        by zvmwg; simp [regB, regI, upd, z91, z86, z81]⟩,
      fun q a1 a2 a3 a4 a5 a6 => by zvmwg; zunmo; grind⟩
  · have okb : okB E.W c₅.nmem [.copyN 81087 81081, .constN 81088 0] c₅.nreg := by
      zqsx
    refine (FRS.ifF a (FRS.block hB _ hI₅ okb)).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₅.nmem [.copyN 81087 81081, .constN 81088 0] c₅.nreg q :=
      fun q => by zvmxl
    zuinh
    refine ⟨by zvmwg; tauto, by zvmwg; tauto,
      fun _ => ⟨by zvmwg; tauto, by zvmwg; rfl⟩,
      by omega,
      fun q a1 a2 a3 a4 a5 a6 => by zvmwg; zunmo; grind⟩

/-- Test the host vertex `(s + x) mod n` (`s` in `81089`, offset in register `x`). -/
def vOff (x : ℕ) (sT : Stmt) : Stmt :=
  .seq (Stmt.block [.addN 81071 81089 x])
    ztffa

/-- The cost bound of `vOff`. -/
def voK (E : FEnv) : ℕ := tvK E + 8
theorem vOff_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {x : ℕ}
    (_hx : x ≠ 81071) (hs : c.nreg 81089 < E.M.W.n) (hxn : c.nreg x < E.M.W.n)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + voK E ≤ E.W) :
    FRS B E.P E.W c₀ (vOff x E.sT) c (voK E) (fun c' => FWin E c' ∧
      ztegm ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        VSet E ztbaaj → ∀ σb, σb ≤ 1 →
        GoodAt E reg ztbaaj σb → c'.nreg 81007 = 1)) := by
  zqtg
  have ok1 : okB E.W c.nmem [.addN 81071 81089 x] c.nreg := by
    zubzx
  refine FRS.seq (K₂ := tvK E + 7) ztbbr ztiy |>.mono
    (by simp [voK]; omega) ztb
  zuhph
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.addN 81071 81089 x] c.nreg q := by_simp_all
  have v71 : c₁.nreg 81071 = c.nreg 81089 + c.nreg x := by_tauto
  have f₁ : ztkoi := fun q h => by
    zukq
  zufxb
  refine FRS.seq (K₁ := 3) (K₂ := tvK E + 4) (Q₁ := fun c' =>
      c'.nreg 81071 = ztjse % E.M.W.n ∧
      ∀ q, q ≠ 81071 → c'.nreg q = c.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v₂, f₂⟩ => ?_) |>.mono
    by_omega ztb
  · zuhrw
    · zqtb
      rw [v71, n17₁] at a; rw [v71, Nat.mod_eq_of_lt a]
    · have okm : ztlyp := by
        zqsx
      zqtd
      have e' : zthpd :=
        by simp_all
      zqta
      rw [v71, n17₁] at *
      zqtc
  have hv2 : zturj := by rw [v₂]; exact Nat.mod_lt _ by_omega
  zuizq
  refine (vTest_fs hE hB hBT hI₂ hw₂ hv2 (by unfold voK at hroom; omega)).mono le_rfl
    (fun c' ⟨w', fr', m', g'⟩ => ⟨w', fun q a b h1 h2 => by_grind,
      fun h => m' by_simp_all, fun reg hr hch hs σb hσb hg => ?_⟩)
  zueec

/-- The registers of the first stretch: `(s, 6 + tpos, L₁)`. -/
def str1L : List Instr :=
  [.copyN 81130 81089, .addN 81131 81086 81015, .addN 81131 81131 81012, .copyN 81132 81087,
    .addN 81135 81131 81087]
theorem str1_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hW : c.nreg 81086 + 6 + c.nreg 81087 ≤ E.W) :
    FRS B E.P E.W c₀ ztvdp c 5 (fun c' =>
      c'.nreg 81130 = c.nreg 81089 ∧ c'.nreg 81131 = 6 + c.nreg 81086 ∧
      c'.nreg 81132 = c.nreg 81087 ∧ c'.nreg 81135 = 6 + c.nreg 81086 + c.nreg 81087 ∧
      ∀ q, q ≠ 81130 → q ≠ 81131 → q ≠ 81132 → q ≠ 81135 → c'.nreg q = c.nreg q) := by
  zuwl
  zuhr
  have ok : okB E.W c.nmem str1L c.nreg := by
    simp only [str1L, okB, okI, regI, upd, FScr, FOut, k5, k1]; grind
  zqth
  have e' : ∀ q, c'.nreg q = regB c.nmem str1L c.nreg q := by_simp_all
  refine ⟨by_tauto, by zvmwg; zuniw; ring,
    by tauto, by zvmwg; zuniw; ring,
    fun q a b d e => by zvmwg; simp [str1L, regB, regI, upd, a, b, d, e]⟩

/-- The registers of the second stretch: `((s + L₁) mod n, 6, L₂)`. -/
def str2 : Stmt :=
  .seq (Stmt.block [.addN 81130 81089 81087])
    (.seq (.ifLtN 81130 81017 .skip (Stmt.block [.subN 81130 81130 81017]))
      (Stmt.block [.constN 81131 6, .copyN 81132 81088, .addN 81135 81131 81088]))
theorem str2_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hs : c.nreg 81089 < E.M.W.n) (hL : c.nreg 81087 < E.M.W.n) (hnW : 2 * E.M.W.n ≤ E.W)
    (hW : 6 + c.nreg 81088 ≤ E.W) :
    FRS B E.P E.W c₀ str2 c 7 (fun c' =>
      c'.nreg 81130 = ztqif % E.M.W.n ∧ c'.nreg 81131 = 6 ∧
      c'.nreg 81132 = c.nreg 81088 ∧ c'.nreg 81135 = 6 + c.nreg 81088 ∧
      ∀ q, q ≠ 81130 → q ≠ 81131 → q ≠ 81132 → q ≠ 81135 → c'.nreg q = c.nreg q) := by
  zqtg
  have ok1 : okB E.W c.nmem [.addN 81130 81089 81087] c.nreg := by
    zubzx
  refine FRS.seq (K₂ := 6) ztbbr ztiy |>.mono
    by_simp ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.addN 81130 81089 81087] c.nreg q := by_simp_all
  have v30 : c₁.nreg 81130 = c.nreg 81089 + c.nreg 81087 := by_tauto
  have f₁ : ∀ q, q ≠ 81130 → c₁.nreg q = c.nreg q := fun q h => by
    zukq
  zufxb
  refine FRS.seq (K₁ := 3) (K₂ := 3) (Q₁ := fun c' =>
      c'.nreg 81130 = ztqif % E.M.W.n ∧
      ∀ q, q ≠ 81130 → c'.nreg q = c.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v₂, f₂⟩ => ?_)
  · by_cases a : c₁.nreg 81130 < c₁.nreg 81017
    · zqtb
      rw [v30, n17₁] at a; rw [v30, Nat.mod_eq_of_lt a]
    · have okm : okB E.W c₁.nmem [.subN 81130 81130 81017] c₁.nreg := by
        zqsx
      zqtd
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN 81130 81130 81017] c₁.nreg q :=
        by simp_all
      zqta
      rw [v30, n17₁] at *
      zqtc
  have y88 : c₂.nreg 81088 = c.nreg 81088 := by_simp_all
  have ok3 : okB E.W c₂.nmem [.constN 81131 6, .copyN 81132 81088, .addN 81135 81131 81088]
      c₂.nreg := by
    simp only [okB, okI, regI, upd, FScr, FOut, y88]; grind
  zucpc
  have e' : ∀ q, c'.nreg q = regB c₂.nmem [.constN 81131 6, .copyN 81132 81088,
      .addN 81135 81131 81088] c₂.nreg q := by_simp_all
  refine ⟨by zvmwg; tauto, by_tauto,
    by zvmwg; tauto, by zvmwg; simp [regB, regI, upd, y88],
    fun q a b d e => by zvmwg; simp [regB, regI, upd, b, d, e]; simp_all⟩

/-- The vertex tests of a kind-1 piece: its ends and the junction of its stretches. -/
def k1Tests (sT : Stmt) : Stmt :=
  .seq (vOff 81011 sT) (.seq (vOff 81081 sT) (.ifLtN 81011 81088 (vOff 81087 sT) .skip))

/-- **A kind-1 piece.** -/
def k1S (sT : Stmt) : Stmt :=
  .seq ztvdl (.seq k1Dir (.seq k1Pos (.seq (k1Tests sT) (.seq ztvdp
    (.seq ztvpa (.ifLtN 81011 81088 (.seq str2 ztvpa) .skip))))))

/-- The cost bound of a kind-1 piece. -/
noncomputable def k1K (E : FEnv) (Cα : Chain) (N : NF) : ℕ :=
  13 + (hvK + 9 + (18 + (voK E + (voK E + (ztrye + (5 +
    (descK E Cα N zthgk + ztdss)))))))

/-- The registers a kind-1 piece writes. -/
def K1W (q : ℕ) : Prop := DescW q ∨ ztnhw ∨ ztnhz

/-- The completeness of a stretch `(g, g', L)` of a kind-1 piece (from the piece's start `c`). -/
def SComp (E : FEnv) (c₀ c : Config) (Cα : Chain) (N : NF) (g g' L f : ℕ) : Prop :=
  ∀ (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ),
    DescGood E c₀ Cα N g g' L reg ai bi aj bj dX regα T →
    aj = E.M.key zti ztke →
    ztceg → f = 1
theorem kind1_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hPR : c.nreg 81080 + 6 < c₀.nreg ALLOC) {Hs : Host} {Cα : Chain} {N : NF} {γ' : ℕ}
    (hCD : ChainDescAt c₀.nmem ztyiz zti Hs Cα)
    (hwf : ChainWF E.P ztdq c₀.nmem ztyiz)
    (hNW : NFWithin c₀.nmem (c₀.nmem ztlla) ztdq N)
    (hcan : IsCanonicalNF ztbdc zti N γ' 4) (hQ : Cα.P = Qof E.P)
    (hdir : (∀ d, d ≤ Cα.m → E.M.W.vtx ztxfq = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m →
        E.M.W.vtx ztxfq = Cα.vertex ztclf))
    (hs : c₀.nmem ztcuw < E.M.W.n) (hmn : Cα.m < E.M.W.n)
    (hVs : VSet E ztzeg)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hnW : 2 * E.M.W.n ≤ E.W) (h2α : 2 * ztgb ≤ E.W)
    (hWa : ∀ r, r < N.nRegions → 2 * ztgb + (N.region r).arcs.length ≤ E.W)
    (hdW : decDepth 4 N.nChords + 1 ≤ E.W)
    (hroom : c.nreg ALLOC + k1K E Cα N ≤ E.W) :
    FRS B E.P E.W c₀ (k1S E.sT) c (k1K E Cα N) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c'.nreg q = c.nreg q) ∧
      ztfn ∧
      ∃ J, (∀ d, d ≤ Cα.m → E.M.W.vtx ztxfq =
          WalkEmbed.tourV Cα J d) ∧
        (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
          (v = c₀.nmem ztcuw ∨ v = (c₀.nmem ztcuw + Cα.m) % E.M.W.n ∨
            (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m ∧
              v = ztzli % E.M.W.n)) →
          VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → c'.nreg 81007 = 1) ∧
        (WalkEmbed.tpos Cα J + Cα.m ≤ 2 * Cα.m →
          SComp E c₀ c Cα N ztzeg ztgct Cα.m
            ztdzf) ∧
        (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m →
          SComp E c₀ c Cα N ztzeg ztgct
            ztbpf ztdzf ∧
          SComp E c₀ c Cα N (ztzli %
            E.M.W.n) 6 (Cα.m - (2 * Cα.m - WalkEmbed.tpos Cα J)) (c'.nreg 81007))) := by
  have hDH : DistinctHeights _ := ShootCut.goodEnv_distinct hE.hG
  zunx
  zumbe
  have hsP : Cα.s < (Qof E.P).n := by
    have := (hwf.2 Hs Cα hCD).2.2.2; simp_all
  set s₀ := c₀.nmem ztcuw with hs₀
  set Dα := c₀.nmem ztczb with hDα
  set Bα := c₀.nmem ztlla with hBα
  have hWm : 2 * Cα.m + 7 ≤ E.W := by_omega
  have k1U := fun q (h : ¬ K1W q) => h
  -- the reads
  refine FRS.seq (K₂ := k1K E Cα N - 13) (k1Load_fs hE hB hI hPR hCD hwf)
    (fun c₁ hI₁ hA₁ ⟨l89, l33, l34, l82, l81, l83, l84, f₁⟩ => ?_) |>.mono
    ztjrc ztb
  -- the direction
  refine FRS.seq (K₁ := hvK + 9) (K₂ := k1K E Cα N - 13 - ztobh)
    (k1Dir_fs hE hB hI₁ by_omega by_grind
      ztcmo)
    (fun c₂ hI₂ hA₂ ⟨h, hh, hy, d85, f₂⟩ => ?_) |>.mono ztjrc ztb
  rw [l82, l81] at d85
  rw [l89] at hy
  have hV := dir_correct hDH hQ ztgfs hsP hs
    (by rw [hy]; show (Chazelle.Chain.sidePt E.M.W s₀ 0).2 = _
        rw [Chazelle.Chain.sidePt_zero]) hdir
  set J := if h = Cα.s then 0 else Cα.m with hJdef
  have hJm : J ≤ Cα.m := by rw [hJdef]; split_ifs <;> omega
  have r₂ : ∀ q, 80000 ≤ q → q < 90000 → ¬ (81060 ≤ q ∧ q ≤ 81064) → q ≠ 81085 →
      c₂.nreg q = c₁.nreg q := fun q a b h1 h2 => f₂ q a b by_omega by_omega by_omega
        by_omega h2
  have q81 : c₂.nreg 81081 = Cα.m := by_grind
  have q83 : c₂.nreg 81083 = Cα.topIdx := by
    grind
  have q84 : c₂.nreg 81084 = c₁.nreg 81084 := by_grind
  -- the offsets
  refine FRS.seq (K₁ := 18) (K₂ := k1K E Cα N - 13 - ztobh - 18)
    (k1Pos_fs hE hB hI₂ q81 q83 (by rw [q84]; omega) by_omega by_omega)
    (fun c₃ hI₃ hA₃ ⟨p86, p91, pa, pb, f₃⟩ => ?_) |>.mono ztjrc ztb
  rw [d85] at p86 pa pb
  set tp := WalkEmbed.tpos Cα J with htp
  have htp2 := WalkEmbed.tpos_lt Cα J
  -- the lengths
  obtain ⟨L₁, L₂, hL₁, hL₂, hcase⟩ : ∃ L₁ L₂, c₃.nreg 81087 = L₁ ∧ c₃.nreg 81088 = L₂ ∧
      ((tp + Cα.m ≤ 2 * Cα.m ∧ L₁ = Cα.m ∧ L₂ = 0) ∨
        (2 * Cα.m < tp + Cα.m ∧ L₁ = 2 * Cα.m - tp ∧ L₂ = Cα.m - ztptm)) := by
    by_cases hc : tp + Cα.m ≤ 2 * Cα.m
    · grind
    grind
  have hL1m : L₁ ≤ Cα.m := by_omega
  have hL2p : 0 < L₂ ↔ 2 * Cα.m < tp + Cα.m := by
    omega
  -- the frame so far
  have G₃ : ∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c₃.nreg q = c.nreg q := fun q a b hq => by
    have h1 : ¬ ztnhw := fun h => hq ztwkb
    have h2 : ¬ ztnhz := fun h => hq ztwxb
    have h3 := fun h => hq (Or.inl (Or.inr (Or.inl
      ztwkb)))
    rw [f₃ q by_omega by_omega by_omega by_omega by_omega by_omega,
      r₂ q by_omega by_omega h3 by_omega,
      f₁ q by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega]
  have G07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c₃.nreg q = c.nreg q := fun q a b => by
    rw [f₃ q by_omega by_omega by_omega by_omega by_omega by_omega,
      r₂ q by_omega by_omega by_omega by_omega,
      f₁ q by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega]
  have v₃ : ∀ q, (q = 81089 ∨ q = 81081 ∨ q = 81133 ∨ q = 81134) → c₃.nreg q = c₁.nreg q :=
    fun q hq => by
      rw [f₃ q by_omega by_omega by_omega by_omega by_omega by_omega,
        r₂ q by_omega by_omega by_omega by_omega]
  have s89 : c₃.nreg 81089 = s₀ := by rw [v₃ _ by_omega, l89]
  have s81 : c₃.nreg 81081 = Cα.m := by rw [v₃ _ by_omega, l81]
  have s33 : c₃.nreg 81133 = Dα := by rw [v₃ _ by_omega, l33]
  have s34 : c₃.nreg 81134 = Bα := by rw [v₃ _ by_omega, l34]
  have hw₃ := hw.congr' G07
  zufxa
  have hmn' := hmn
  -- the vertex tests
  refine FRS.seq (K₁ := voK E + (voK E + ztrye))
    (K₂ := 5 + (descK E Cα N zthgk +
      ztdss)) (Q₁ := fun d => FWin E d ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → d.nreg q = c₃.nreg q) ∧
      ztdmr ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
        (v = s₀ ∨ v = ztubn % E.M.W.n ∨
          zteku) →
        VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → d.nreg 81007 = 1)) ?_
    (fun c₆ hI₆ hA₆ ⟨hw₆, f₆, m₆, t₆⟩ => ?_) |>.mono (by unfold k1K at *; omega) ztb
  · refine FRS.seq (vOff_fs hE hB hBT hI₃ hw₃ by_norm_num by_omega
      by_omega hnW ztcmo)
      (fun c₄ hI₄ hA₄ ⟨hw₄, f₄, m₄, t₄⟩ => ?_)
    have w81 : ztusx := by
      rw [f₄ _ by_norm_num by_norm_num ztod by_norm_num, s81]
    have w89 : c₄.nreg 81089 = s₀ := by
      rw [f₄ _ by_norm_num by_norm_num ztod by_norm_num, s89]
    refine FRS.seq (vOff_fs hE hB hBT hI₄ hw₄ by_norm_num by_omega
      by_omega hnW ztcmo)
      (fun c₅ hI₅ hA₅ ⟨hw₅, f₅, m₅, t₅⟩ => ?_)
    rw [w89, w81] at t₅
    rw [s89, k0₃, Nat.add_zero, Nat.mod_eq_of_lt hs] at t₄
    have x88 : c₅.nreg 81088 = L₂ := by
      rw [f₅ _ by_norm_num by_norm_num ztod by_norm_num,
        f₄ _ by_norm_num by_norm_num ztod by_norm_num, hL₂]
    have x87 : c₅.nreg 81087 = L₁ := by
      rw [f₅ _ by_norm_num by_norm_num ztod by_norm_num,
        f₄ _ by_norm_num by_norm_num ztod by_norm_num, hL₁]
    have x89 : c₅.nreg 81089 = s₀ := by
      rw [f₅ _ by_norm_num by_norm_num ztod by_norm_num, w89]
    zukhz
    have F5 : ∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → c₅.nreg q = c₃.nreg q :=
      fun q a b h1 h2 => by rw [f₅ q a b h1 h2, f₄ q a b h1 h2]
    by_cases a : c₅.nreg 81011 < c₅.nreg 81088
    · zuhwz
      refine (FRS.ifT a (vOff_fs hE hB hBT hI₅ hw₅ by_norm_num
        by_omega by_omega hnW ztcmo)).mono
        by_omega (fun c₆ ⟨hw₆, f₆, m₆, t₆⟩ => ⟨hw₆, fun q a b h1 h2 => by
          rw [f₆ q a b h1 h2, F5 q a b h1 h2], fun h => m₆ (m₅ zthyx), ?_⟩)
      rw [x89, x87] at t₆
      zugom
      rcases hv with rfl | rfl | ⟨-, rfl⟩
      · exact m₆ (m₅ ztmoz)
      · exact m₆ (t₅ reg hr hch hvs σb hσb hg)
      · rcases hcase with ⟨h0, -, h2⟩ | ⟨h0, h1, -⟩
        · omega
        · rw [← h1] at hvs hg; exact t₆ reg hr hch hvs σb hσb hg
    · have hL2 : L₂ = 0 := by rw [k0₅, x88] at a; omega
      refine (FRS.ifF a (FRS.skip (K := 0) hI₅ ⟨hw₅, F5, fun h => m₅ zthyx, ?_⟩)).mono
        by_omega ztb
      zugom
      rcases hv with rfl | rfl | ⟨h3, rfl⟩
      · exact m₅ ztmoz
      · exact t₅ reg hr hch hvs σb hσb hg
      · exact absurd (hL2p.2 h3) by_omega
  -- the facts at `c₆`
  have nV : ∀ q, (q = 81089 ∨ q = 81086 ∨ q = 81087 ∨ q = 81088 ∨ q = 81133 ∨ q = 81134 ∨
      q = 81140 ∨ q = 81141 ∨ q = 81081) → c₆.nreg q = c₃.nreg q := fun q hq =>
    f₆ q by_omega by_omega ztod by_omega
  have u89 : c₆.nreg 81089 = s₀ := by rw [nV _ by_omega, s89]
  have u86 : c₆.nreg 81086 = tp := by rw [nV _ by_omega, p86]
  have u87 : c₆.nreg 81087 = L₁ := by rw [nV _ by_omega, hL₁]
  have u88 : c₆.nreg 81088 = L₂ := by rw [nV _ by_omega, hL₂]
  have u33 : c₆.nreg 81133 = Dα := by rw [nV _ by_omega, s33]
  have u34 : c₆.nreg 81134 = Bα := by rw [nV _ by_omega, s34]
  have u40 : c₆.nreg 81140 = c.nreg 81140 := by
    rw [nV _ by_omega, G₃ _ by_norm_num by_norm_num (by
      unfold K1W DescW NodeW LeafW KeyW VertW; omega)]
  have u41 : c₆.nreg 81141 = c.nreg 81141 := by
    rw [nV _ by_omega, G₃ _ by_norm_num by_norm_num (by
      unfold K1W DescW NodeW LeafW KeyW VertW; omega)]
  have G₆ : ∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c₆.nreg q = c.nreg q := fun q a b hq => by
    rw [f₆ q a b (fun h => hq ztband)
      (fun h => hq (Or.inl (Or.inr (Or.inl ztbh)))), G₃ q a b hq]
  -- the stretches
  obtain ⟨hst1, hst2⟩ := piece_stretches hs hmn hV
  have hS1 : Stretch E.M Cα s₀ ztsuc L₁ := by
    rcases hcase with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩
    · zvmwp; exact hst1 h0
    · zvmwp; exact (hst2 h0).1
  have hDd : IsDecomp N _ := hcan.2.2.2
  have hPC : ∀ {g g' L : ℕ}, Stretch E.M Cα g g' L → PCtx E c₀ Cα Hs N g g' L Dα Bα :=
    fun hS => ⟨hS, hQ, hcan.1, ⟨_, hDd⟩, hNW, hCD, hwf, hWm⟩
  -- the first stretch
  refine FRS.seq (K₁ := 5) (K₂ := descK E Cα N zthgk +
      ztdss)
    (str1_fs hE hB hI₆ by_omega)
    (fun c₇ hI₇ hA₇ ⟨a30, a31, a32, a35, f₇⟩ => ?_) |>.mono le_rfl ztb
  rw [u89] at a30; rw [u86] at a31; rw [u87] at a32; rw [u86, u87] at a35
  have hR₇ : SRegs c₇ s₀ _ L₁ Dα Bα := ⟨a30, a31, a32,
    by rw [f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u33],
    by rw [f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u34], by rw [a35]⟩
  have b40 : c₇.nreg 81140 = c.nreg 81140 := by
    rw [f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u40]
  have b41 : c₇.nreg 81141 = c.nreg 81141 := by
    rw [f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u41]
  have hw₇ := hw₆.congr' (fun q a b => f₇ q by_omega by_omega by_omega by_omega)
  refine FRS.seq (desc_fs hE hB hBT hI₇ hw₇ (hPC hS1) hR₇ hDd hdW (by rw [b40, b41]; exact hJ)
    hnW h2α hWa ztcmo)
    (fun c₈ hI₈ hA₈ ⟨hw₈, f₈, m₈, t₈⟩ => ?_)
  have nD : ∀ q, (q = 81089 ∨ q = 81087 ∨ q = 81088 ∨ q = 81133 ∨ q = 81134 ∨ q = 81140 ∨
      q = 81141) → c₈.nreg q = c₇.nreg q := fun q hq =>
    f₈ q by_omega by_omega (by unfold DescW NodeW LeafW KeyW VertW; omega)
  have v88 : c₈.nreg 81088 = L₂ := by
    rw [nD _ by_omega, f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u88]
  have k0₈ := k0_of hE hI₈
  have G₈ : ∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c₈.nreg q = c.nreg q := fun q a b hq => by
    rw [f₈ q a b ztxwu, f₇ q ztwix
      ztwix
      ztwix
      ztwix, G₆ q a b hq]
  have m8 := fun h => m₈ (by
    zunwp; exact m₆ h)
  have t8' : SComp E c₀ c Cα N s₀ ztsuc L₁ (c₈.nreg 81007) := by
    zqtf
    rw [← b40, ← b41] at hJa hJr
    exact t₈ reg ai bi aj bj dX regα T hD hJa hJr
  have t6' : ∀ reg, NFRegs E.M _ E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
      (v = s₀ ∨ v = ztubn % E.M.W.n ∨
        zteku) →
      VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → c₈.nreg 81007 = 1 :=
    fun reg hr hch v hv hvs σb hσb hg => m₈ (by
      zunwp
      exact t₆ reg hr hch v hv hvs σb hσb hg)
  by_cases a : c₈.nreg 81011 < c₈.nreg 81088
  · zuhwz
    have h2c := hL2p.1 hL2
    obtain ⟨-, hL1e, hL2e⟩ : 2 * Cα.m < tp + Cα.m ∧ L₁ = 2 * Cα.m - tp ∧
        L₂ = Cα.m - ztptm := by
      rcases hcase with ⟨h0, -, -⟩ | h
      · omega
      · zubh
    have hS2 : Stretch E.M Cα ((s₀ + L₁) % E.M.W.n) 6 L₂ := by
      rw [hL1e, hL2e]; exact (hst2 h2c).2
    have w89 : c₈.nreg 81089 = s₀ := by
      rw [nD _ by_omega, f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u89]
    have w87 : c₈.nreg 81087 = L₁ := by
      rw [nD _ by_omega, f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u87]
    refine (FRS.ifT a (FRS.seq (K₂ := descK E Cα N zthgk) (str2_fs hE hB hI₈ by_omega
      (by rw [w87]; omega) hnW (by rw [v88]; omega))
      (fun c₉ hI₉ hA₉ ⟨d30, d31, d32, d35, f₉⟩ => ?_))).mono by_omega (fun _ h => h)
    rw [w89, w87] at d30; rw [v88] at d32 d35
    have hR₉ : SRegs c₉ _ 6 L₂ Dα Bα := ⟨d30, d31, d32,
      by rw [f₉ _ by_norm_num by_norm_num by_norm_num by_norm_num, nD _ by_omega,
        f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u33],
      by rw [f₉ _ by_norm_num by_norm_num by_norm_num by_norm_num, nD _ by_omega,
        f₇ _ by_norm_num by_norm_num by_norm_num by_norm_num, u34], d35⟩
    have e40 : c₉.nreg 81140 = c.nreg 81140 := by
      rw [f₉ _ by_norm_num by_norm_num by_norm_num by_norm_num, nD _ by_omega, b40]
    have e41 : c₉.nreg 81141 = c.nreg 81141 := by
      rw [f₉ _ by_norm_num by_norm_num by_norm_num by_norm_num, nD _ by_omega, b41]
    have hw₉ := hw₈.congr' (fun q a b => f₉ q by_omega by_omega by_omega
      by_omega)
    refine (desc_fs hE hB hBT hI₉ hw₉ (hPC hS2) hR₉ hDd hdW ztkst
      hnW h2α hWa ztcmo).mono le_rfl
      (fun c' ⟨hw', f', m', t'⟩ => ⟨hw', fun q a b hq => ?_, fun h => m' (by
        zunfl; exact m8 h),
        J, hV, fun reg hr hch v hv hvs σb hσb hg => m' (by
          zunfl
          exact t6' reg hr hch v hv hvs σb hσb hg), fun h => absurd h by_omega, fun _ => ⟨?_, ?_⟩⟩)
    · rw [f' q a b ztxwu, f₉ q ztwix
        ztwix
        ztwix
        ztwix, G₈ q a b hq]
    · zuosv
      zqtf
      exact m' (by zunfl
                   exact t8' reg ai bi aj bj dX regα T hD hJa hJr)
    · rw [← hL1e, show Cα.m - L₁ = L₂ by omega]
      zqtf
      rw [← e40, ← e41] at hJa hJr
      exact t' reg ai bi aj bj dX regα T hD hJa hJr
  · have hL2 : L₂ = 0 := by rw [k0₈, v88] at a; omega
    have h1c : tp + Cα.m ≤ 2 * Cα.m := by
      by_contra h; exact absurd (hL2p.2 by_omega) by_omega
    have hL1e : L₁ = Cα.m := by rcases hcase with ⟨-, h1, -⟩ | ⟨h0, -, -⟩ <;> omega
    refine (FRS.ifF a (FRS.skip (K := 0) hI₈ ⟨hw₈, G₈, m8, J, hV, t6', fun _ => ?_,
      fun h => absurd h by_omega⟩)).mono by_omega (fun _ h => h)
    zuosv; omega
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- **Normalising a walk position** in `s`, `s + 1`. -/
def aNorm (s : ℕ) : Stmt :=
  .ifLtN 81011 ztbk (.ifLtN s 81021 .skip
    (.seq (Stmt.block [.copyN 81044 s, .constN 81045 0]) (.seq (cmpM 81046 81044 81045 s ztbk)
      (.ifLtN 81011 81046 .skip (Stmt.block [.constN ztbk 0]))))) .skip

/-- The cost bound of `aNorm`. -/
def anK : ℕ := 11040
variable {E : FEnv} {c₀ c : Config}
theorem aNorm_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (hs : 81030 ≤ s ∧ s + 1 ≤ 81043)
    (hp : ProperPos E.M zti E.P.n ztwlz) (hen : c.nreg s < E.M.W.n)
    (hy : ∀ C : Chain, E.M = chainModel C →
      |(E.M.pos (Qof E.P) ⟨c.nreg s, c.nreg (s + 1)⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + anK ≤ E.W) :
    FRS B E.P E.W c₀ (aNorm s) c anK (fun c' =>
      c'.nreg s = c.nreg s ∧
      c'.nreg ztbk = (normOf E.M zti ztwlz).hgt ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ s + 1 → ¬ ztnhv →
        c'.nreg q = c.nreg q) := by
  zubgm
  zufvq
  zunx
  unfold normOf
  -- height code 0: nothing to do
  by_cases a1 : c.nreg 81011 < c.nreg ztbk
  swap
  · have h0 : ztback := by_omega
    refine (FRS.ifF a1 (FRS.skip (K := 0) hI ztreb)).mono
      by_decide ztb
    simp_all
  refine (FRS.ifT a1 ?_).mono (K := anK - 2) by_omega ztb
  have hh0 : ztbabq := by_omega
  -- below the vertex range: a box edge of a chain model, positive parameter
  by_cases a2 : c.nreg s < c.nreg 81021
  · refine (FRS.ifT a2 (FRS.skip (K := 0) hI ztreb)).mono
      by_omega ztb
    zuiaq
    have hpos : ztbaqm := by
      zvmyq at a2
      by_cases hch : ∃ C : Chain, E.M = chainModel C
      · obtain ⟨C, hC⟩ := hch
        have hn7 : ztpjf := by rw [hC]; exact chainModel_n C
        have h6 := (hE.hvc 6 by_omega (fun C' hC' => by
          rw [hC', pos_eq_sidePt]
          show Chazelle.Chain.sidePt ztffh 6 0 ∈ C'.set
          rw [Chazelle.Chain.sidePt_zero, C'.sideWalk_vtx_six]
          exact C'.top_mem_set)).1
        have he6 : ztuox := by_omega
        have hp0 := hp.1
        have hy' := hy C hC
        rw [hC] at hp0 hy' ⊢
        exact ShootCut.box_param_pos' C _ he6 hp0 hy'
      · have := (hE.hvc _ hen by_simp_all).1
        omega
    grind
  refine (FRS.ifF a2 ?_).mono by_rfl ztb
  zuiaq
  have ok1 : okB E.W c.nmem [.copyN 81044 s, .constN 81045 0] c.nreg := by
    zuph
  refine FRS.seq (K₂ := 11025) ztbbr ztiy |>.mono
    by_simp ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81044 s, .constN 81045 0] c.nreg q :=
    by simp_all
  have v44 : c₁.nreg 81044 = c.nreg s := by
    tauto
  have v45 : c₁.nreg 81045 = 0 := by_tauto
  have f₁ : ∀ q, q ≠ 81044 → q ≠ 81045 → c₁.nreg q = c.nreg q := fun q a b => by
    zubei
  have w0 : ztsgq := by_grind
  have w1 : ztzpm := f₁ _ by_omega by_omega
  zudhe
  have hpg0 : PosG E.M zti E.P.n ⟨c₁.nreg 81044, c₁.nreg 81045⟩ := by
    rw [v44, v45]
    refine ⟨hen, ztdjf, fun C hC _ => ?_⟩
    have := hE.vlo6 C hC; grind
  have hpg1 : PosG E.M zti E.P.n ztxzl := by
    rw [w0, w1]; exact ⟨hen, hp, by_grind⟩
  refine FRS.seq (K₁ := 11022) (K₂ := 3) (cmpM_fs hE hB hI₁ (r := 81046) (a := 81044)
    (b := 81045) (d := s) (e := s + 1) ztfm ztfm
    ⟨by_norm_num, by_norm_num⟩ ⟨by_omega, by_omega⟩ ⟨by_omega, by_omega⟩ ztqj
    ztqj ztqj ztqj hpg0 hpg1
    (by rw [hA₁']; simp only [List.length_cons, List.length_nil] at hA₁; unfold anK at hroom;
        omega))
    (fun c₂ hI₂ hA₂ ⟨b46, _, f₂⟩ => ?_)
  rw [v44, v45, w0, w1, key_vtx_lt_iff] at b46
  zudpz
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → ¬ ztnhv →
      c₂.nreg q = c.nreg q := fun q a b h1 h2 => by
    grind
  have y0 := g₂ s by_omega by_omega ztqj by_omega
  have y1 : c₂.nreg _ = c.nreg ztbk :=
    g₂ _ by_omega by_omega ztqj by_omega
  by_cases a3 : c₂.nreg 81011 < c₂.nreg 81046
  · have hpos : ztbaqm := by
      rw [k0₂] at a3; exact b46.2.1 (by have := b46.1; omega)
    refine (FRS.ifT a3 (FRS.skip (K := 0) hI₂ ⟨y0, ?_, by_grind⟩)).mono
      by_omega ztb
    grind
  · have hz : E.M.param zti ztwlz = 0 := by
      rw [k0₂] at a3
      have h46 : c₂.nreg 81046 ≠ 1 := by_omega
      exact le_antisymm (not_lt.1 (fun h => h46 (b46.2.2 h))) hp.1
    have okz : okB E.W c₂.nmem [.constN ztbk 0] c₂.nreg := by
      zubzx
    refine (FRS.ifF a3 ztpyl).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.constN _ 0] c₂.nreg q := fun q => by zvmxl
    refine ⟨by zvmwg; zumxd; exact y0, by rw [e', ite_eq_left hz]; zumxd,
      fun q a b h1 h2 h3 => by zvmwg; zundw; grind⟩

/-! ## The piece loop -/

/-- The reads of piece `i` (`81079`) of the list at `L` (`81076`): its record address `81080`,
kind `81077`, start edge `81070`. -/
def pbL : List Instr :=
  [.addN 81080 81076 81012, .addN 81080 81080 81079, .addN 81080 81080 81079,
    .addN 81080 81080 81079, .addN 81080 81080 81079, .addN 81080 81080 81079,
    .addN 81080 81080 81079, .addN 81080 81080 81079, .addN 81073 81080 81014,
    .addN 81073 81073 81012, .loadN 81077 81073, .loadN 81070 81080]

/-- **One piece.** -/
def pieceBody (sT : Stmt) : Stmt :=
  .seq ztvdn (.seq (.ifLtN 81011 81077 (ifEq 81077 81012 (k1S sT)) (kind0 sT))
    ztnpj)

/-- The record address of piece `i` of the list at `L`. -/
def prOf (L i : ℕ) : ℕ := L + 1 + 7 * i
theorem pbL_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hPR : prOf ztmgi ztmgj + 6 < c₀.nreg ALLOC) :
    FRS B E.P E.W c₀ ztvdn c 12 (fun c' =>
      c'.nreg 81080 = prOf ztmgi ztmgj ∧
      c'.nreg 81077 = c₀.nmem (prOf ztmgi ztmgj + 4) ∧
      c'.nreg 81070 = c₀.nmem (prOf ztmgi ztmgj) ∧
      ∀ q, q ≠ 81070 → q ≠ 81073 → q ≠ 81077 → q ≠ 81080 → c'.nreg q = c.nreg q) := by
  zubnp
  zuki
  zuhr
  have k3 : c.nreg 81014 = 3 := by rw [hI.hin _ ztbc, hE.k3]
  unfold prOf at *
  have ok : okB E.W c.nmem pbL c.nreg := by
    simp only [pbL, okB, okI, regI, upd, FScr, FOut, k1, k3]; grind
  zucpb
  have e' : ∀ q, c'.nreg q = regB c.nmem pbL c.nreg q := by_simp_all
  have ea : c.nreg 81076 + 1 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 +
      c.nreg 81079 + c.nreg 81079 + c.nreg 81079 = c.nreg 81076 + 1 + 7 * c.nreg 81079 := by_ring
  refine ⟨?_, ?_, ?_, fun q a b d e => ?_⟩
  · zvmwg; zunmp; omega
  · zvmwg; simp [pbL, regB, regI, upd, k1, k3]
    rw [show c.nreg 81076 + 1 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 +
      c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + 3 + 1 =
      c.nreg 81076 + 1 + 7 * c.nreg 81079 + 4 by ring]
    zuitj
  · zvmwg; zunmp
    rw [show c.nreg 81076 + 1 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 + c.nreg 81079 +
      c.nreg 81079 + c.nreg 81079 + c.nreg 81079 = c.nreg 81076 + 1 + 7 * c.nreg 81079 by ring]
    zuitj
  · zuczs
    simp only [pbL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zubzs

/-- The facts a kind-1 piece at the record `PR` needs (from the cutter's contract, below the base
of the search). -/
structure K1Hyp (E : FEnv) (c₀ : Config) (PR : ℕ) (Hs : Host) (Cα : Chain) (N : NF) (γ' : ℕ) :
    Prop where
  hPR : PR + 6 < c₀.nreg ALLOC
  hCD : ChainDescAt c₀.nmem ztpai zti Hs Cα
  hwf : ChainWF E.P ztdq c₀.nmem ztpai
  hNW : NFWithin c₀.nmem (c₀.nmem (PR + 6)) ztdq N
  hcan : IsCanonicalNF ztbdc zti N γ' 4
  hQ : Cα.P = Qof E.P
  hdir : (∀ d, d ≤ Cα.m → E.M.W.vtx ztlze = Cα.vertex d) ∨
    (∀ d, d ≤ Cα.m → E.M.W.vtx ztlze = Cα.vertex ztclf)
  hs : c₀.nmem PR < E.M.W.n
  hmn : Cα.m < E.M.W.n
  hVs : VSet E (c₀.nmem PR)
  h2α : 2 * ztgb ≤ E.W
  hWa : ∀ r, r < N.nRegions → 2 * ztgb + (N.region r).arcs.length ≤ E.W
  hdW : decDepth 4 N.nChords + 1 ≤ E.W

/-- The facts of piece `i` of the list at `L` the loop needs. -/
def PieceGood (E : FEnv) (c₀ : Config) (L Kp i : ℕ) : Prop :=
  prOf L i + 6 < c₀.nreg ALLOC ∧ c₀.nmem ztcas < E.M.W.n ∧ k0K E ≤ Kp ∧
    (c₀.nmem ztdpb = 1 → ∃ Hs Cα N γ', K1Hyp E c₀ ztcas Hs Cα N γ' ∧
      k1K E Cα N ≤ Kp)

/-- **What the run of piece `i` tells**, with the success flag `f` (target in `cT`). -/
def PieceDone (E : FEnv) (c₀ cT : Config) (L i f : ℕ) : Prop :=
  (c₀.nmem ztdpb = 0 → ∀ reg, NFRegs E.M zti E.N reg →
    (E.N.region E.r).chords ≠ [] → ∀ t, t < 10 →
      VSet E ztyha → ∀ σb, σb ≤ 1 →
        GoodAt E reg ztyha σb → f = 1) ∧
  (c₀.nmem ztdpb = 1 → ∃ Hs Cα N γ', K1Hyp E c₀ ztcas Hs Cα N γ' ∧
    ∃ J, (∀ d, d ≤ Cα.m → E.M.W.vtx ((c₀.nmem ztcas + d) % E.M.W.n) =
        WalkEmbed.tourV Cα J d) ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
        (v = c₀.nmem ztcas ∨ v = (c₀.nmem ztcas + Cα.m) % E.M.W.n ∨
          (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m ∧
            v = ztzlh % E.M.W.n)) →
        VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → f = 1) ∧
      (WalkEmbed.tpos Cα J + Cα.m ≤ 2 * Cα.m →
        SComp E c₀ cT Cα N ztbagw ztgct Cα.m f) ∧
      (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m →
        SComp E c₀ cT Cα N ztbagw ztgct
          ztbpf f ∧
        SComp E c₀ cT Cα N (ztzlh %
          E.M.W.n) 6 (Cα.m - (2 * Cα.m - WalkEmbed.tpos Cα J)) f))
variable {cT : Config}
theorem SComp.mono {Cα : Chain} {N : NF} {g g' L f f' : ℕ}
    (h : SComp E c₀ cT Cα N g g' L f) (hf : f = 1 → f' = 1) : SComp E c₀ cT Cα N g g' L f' :=
  fun reg ai bi aj bj dX regα T hD hJ hJr => hf (h reg ai bi aj bj dX regα T hD hJ hJr)
theorem PieceDone.mono {L i f f' : ℕ} (h : PieceDone E c₀ cT L i f)
    (hf : f = 1 → f' = 1) : PieceDone E c₀ cT L i f' := by
  zueas
  refine ⟨by_grind,
    fun hk => ?_⟩
  zubxh
  exact ⟨Hs, Cα, N, γ', hK, J, hV, by_grind, fun h => (hs1 h).mono hf,
    fun h => ⟨(hs2 h).1.mono hf, (hs2 h).2.mono hf⟩⟩
theorem SComp.congr {cT cT' : Config} {Cα : Chain} {N : NF} {g g' L f : ℕ}
    (h : SComp E c₀ cT Cα N g g' L f) (h40 : cT'.nreg 81140 = cT.nreg 81140)
    (h41 : cT'.nreg 81141 = cT.nreg 81141) : SComp E c₀ cT' Cα N g g' L f := by
  intro reg ai bi aj bj dX regα T hD hJ hJr
  rw [h40, h41] at hJ hJr
  exact h reg ai bi aj bj dX regα T hD hJ hJr

/-- The registers the piece loop writes. -/
def PW (q : ℕ) : Prop := K1W q ∨ (81070 ≤ q ∧ q ≤ 81073) ∨ q = 81077 ∨ q = 81079 ∨ q = 81080
theorem pieceBody_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {L i Kp : ℕ}
    (hL : c.nreg 81076 = L) (hi : c.nreg 81079 = i) (hG : PieceGood E c₀ L Kp i)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + ztnma ≤ E.W) :
    FRS B E.P E.W c₀ (pieceBody E.sT) c ztnma (fun c' => FWin E c' ∧
      ztfjh ∧
      ztfn ∧ c'.nreg 81079 = i + 1 ∧
      PieceDone E c₀ c L i ztdzf) := by
  obtain ⟨hPR, hs0, hk0, hk1⟩ := hG
  refine FRS.seq (K₁ := 12) (K₂ := Kp + 8) (pbL_fs hE hB hI by_simp_all)
    (fun c₁ hI₁ hA₁ ⟨v80, v77, v70, f₁⟩ => ?_) |>.mono by_omega ztb
  rw [hL, hi] at v80 v77 v70
  zukhy
  zubrc
  zuizp
  have e40 : ztmvf := by_grind
  have e41 : ztmvg := by_grind
  have e79 : c₁.nreg 81079 = i := by
    grind
  -- the final counter step
  have fin : ∀ c₂ : Config, FInv E.W c₀ c₂ → FWin E c₂ →
      ztegl →
      c₂.nreg 81079 = i → ztlkz →
      PieceDone E c₀ c L i ztvmz → c₂.nreg ALLOC + 1 ≤ E.W →
      FRS B E.P E.W c₀ ztnpj c₂ 1 (fun c' => FWin E c' ∧
        ztfjh ∧
        ztfn ∧ c'.nreg 81079 = i + 1 ∧
        PieceDone E c₀ c L i ztdzf) := by
    intro c₂ hI₂ hw₂ f₂ h79 m₂ d₂ _
    zueho
    have hiW : i + 1 ≤ E.W := by
      have := hPR; have := hI.hA; have := hI.hw.1 ALLOC; unfold prOf at *; omega
    have ok : okB E.W c₂.nmem [.addN 81079 81079 81012] c₂.nreg := by
      simp only [okB, okI, FScr, FOut, k1₂, h79]; grind
    zugal
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.addN 81079 81079 81012] c₂.nreg q := fun q => by
      zuczu
    have f' : ∀ q, q ≠ 81079 → c'.nreg q = c₂.nreg q := fun q h => by
      zublr
    have g07 : ztsee := by_grind
    exact ⟨hw₂.congr' by_grind, fun q a b hq => by
      rw [f' q ztwix,
        f₂ q a b hq ztwix],
      by grind, by zvmwg; simp [regB, regI, upd, k1₂, h79],
      by grind⟩
  have nPW : ∀ q, ¬ PW q → q ≠ 81070 ∧ q ≠ 81073 ∧ q ≠ 81077 ∧ q ≠ 81080 := fun q hq =>
    ⟨fun h => hq ztbh,
      fun h => hq ztbh,
      fun h => hq ztbh, fun h => hq ztbh⟩
  by_cases a1 : c₁.nreg 81011 < c₁.nreg 81077
  · refine FRS.seq (K₁ := Kp + 6) (K₂ := 1) (Q₁ := fun c₂ => FWin E c₂ ∧
        ztegl ∧
        c₂.nreg 81079 = i ∧ ztlkz ∧
        PieceDone E c₀ c L i ztvmz)
      (FRS.ifT a1 ?_ |>.mono (K := Kp + 6) by_omega
      ztb) (fun c₂ hI₂ hA₂ h₂ => ?_) |>.mono by_omega (fun _ h => h)
    rotate_left
    · exact fin c₂ hI₂ h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2.1 h₂.2.2.2.2 by_omega
    by_cases a2 : c₁.nreg 81077 = c₁.nreg 81012
    · have hk : c₀.nmem ztdpb = 1 := by_omega
      obtain ⟨Hs, Cα, N, γ', hK, hKp⟩ := hk1 hk
      refine (FRS.ifEq_eq a2 (kind1_fs hE hB hBT hI₁ hw₁ by_omega
        (by rw [v80]; exact hK.hCD) (by rw [v80]; exact hK.hwf) (by rw [v80]; exact hK.hNW)
        hK.hcan hK.hQ (by rw [v80]; exact hK.hdir) by_grind hK.hmn
        (by rw [v80]; exact hK.hVs) by_grind hnW hK.h2α hK.hWa hK.hdW
        by_omega)).mono by_omega (fun c₂ ⟨w₂, f₂, m₂, J, hV, ht, hs1, hs2⟩ => ?_)
      rw [v80] at hV ht hs1 hs2
      refine ⟨w₂, fun q a b hq h79 => by
        rw [f₂ q a b ztxwu, f₁ q by_grind by_grind by_grind
          by_grind],
        by rw [f₂ _ by_norm_num by_norm_num (by unfold K1W DescW NodeW LeafW KeyW VertW; omega),
          e79],
        fun h => m₂ (by rw [f₁ _ by_norm_num by_norm_num by_norm_num by_norm_num]; exact h),
        ⟨by_grind, fun _ => ⟨Hs, Cα, N, γ', hK, J, hV, ht,
          fun h => (hs1 h).congr by_omega by_omega,
          fun h => ⟨(hs2 h).1.congr by_omega by_omega,
            (hs2 h).2.congr by_omega by_omega⟩⟩⟩⟩
    · refine (FRS.ifEq_ne (K := Kp) hI₁ a2 ⟨hw₁, by_grind, e79,
        fun h => by_grind,
        by grind, by_grind⟩).mono by_omega (fun _ h => h)
  · have hk : c₀.nmem ztdpb = 0 := by_omega
    refine FRS.seq (K₂ := 1) (FRS.ifF a1 ((kind0_fs hE hB hBT hI₁ hw₁ v70 hs0
      by_omega).mono hk0 (fun c₂ h => h))) (fun c₂ hI₂ hA₂ ⟨w₂, f₂, m₂, t₂⟩ => ?_) |>.mono
      by_omega ztb
    refine fin c₂ hI₂ w₂ (fun q a b hq h79 => by
      rw [f₂ q a b (fun h => hq (Or.inl ztband))
        ztwix
        ztwix,
        f₁ q by_grind by_grind by_grind by_grind])
      (by rw [f₂ _ by_norm_num by_norm_num ztod by_norm_num
        by_norm_num, e79])
      by_grind
      ⟨fun _ => t₂, by_grind⟩ by_omega
theorem PieceDone.congr {cT cT' : Config} {L i f : ℕ} (h : PieceDone E c₀ cT L i f)
    (h40 : cT'.nreg 81140 = cT.nreg 81140) (h41 : cT'.nreg 81141 = cT.nreg 81141) :
    PieceDone E c₀ cT' L i f := by
  zueas
  refine ⟨h0, fun hk => ?_⟩
  zubxh
  exact ⟨Hs, Cα, N, γ', hK, J, hV, ht, fun h => (hs1 h).congr h40 h41,
    fun h => ⟨(hs2 h).1.congr h40 h41, (hs2 h).2.congr h40 h41⟩⟩

/-- **The piece loop** over the pieces `81079 < 81078` of the list at `81076`. -/
def pieceLoop (sT : Stmt) : Stmt := .whileLtN 81079 81078 (pieceBody sT)

/-- The invariant of the piece loop (from its start `c`). -/
def PLI (E : FEnv) (c₀ c : Config) (L q : ℕ) (c' : Config) : Prop :=
  FWin E c' ∧ ztfjl ∧
    ztfn ∧ c'.nreg 81079 ≤ q ∧
    ∀ i, i < c'.nreg 81079 → PieceDone E c₀ c L i ztdzf
theorem pieceLoop_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {L q Kp : ℕ}
    (hL : c.nreg 81076 = L) (hq : c.nreg 81078 = q) (h0 : c.nreg 81079 = 0)
    (hG : ∀ i, i < q → PieceGood E c₀ L Kp i)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + ztfnv * q ≤ E.W) :
    FRS B E.P E.W c₀ (pieceLoop E.sT) c (ztfnv * q + 2) (fun c' => FWin E c' ∧
      ztfjl ∧
      ztfn ∧
      ∀ i, i < q → PieceDone E c₀ c L i ztdzf) := by
  have hq0 : c.nreg 81078 - c.nreg 81079 = q := by_omega
  have n78 : ¬ PW 81078 := by unfold PW K1W DescW NodeW LeafW KeyW VertW; omega
  have n76 : ¬ PW 81076 := by unfold PW K1W DescW NodeW LeafW KeyW VertW; omega
  have n40 : ¬ PW 81140 := by unfold PW K1W DescW NodeW LeafW KeyW VertW; omega
  have n41 : ¬ PW 81141 := by unfold PW K1W DescW NodeW LeafW KeyW VertW; omega
  refine (FRS.while (PLI E c₀ c L q)
    (fun d => d.nreg 81078 - d.nreg 81079) ztnma by_simp_all
    ztgiz hI ⟨hw, by_omega, id, by_omega,
      by simp_all⟩ by_simp_all).mono (by rw [hq0])
    ztjvq
  · zubri
    have d78 : d.nreg 81078 = q := by_simp_all
    have d40 := df _ by_norm_num by_norm_num n40
    have d41 := df _ by_norm_num by_norm_num n41
    rw [d78] at hlt
    refine (pieceBody_fs hE hB hBT hId dw by_simp_all rfl
      (hG _ hlt) by_simp_all hnW hroomd).mono le_rfl
      (fun c' ⟨w', f', m', h79, pd⟩ => ?_)
    have c78 : c'.nreg 81078 = q := by_simp_all
    refine ⟨⟨w', by_simp_all, by_omega,
      by omega, fun i hi => ?_⟩, by_omega⟩
    rcases Nat.lt_or_ge i _ with h | h
    · exact (dd i h).mono m'
    · rw [show i = d.nreg 81079 by omega]
      exact pd.congr d40.symm d41.symm
  · zuth

    grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
variable {E : FEnv} {c₀ c : Config}

/-- **A call with a frame**: the search's registers (band `bRestore`) survive any call whose bands
avoid `bRestore`. -/
theorem FRS.callF {B : Finset ℕ} {P : Polygon} {W : ℕ} {s : Stmt} {B' : Finset ℕ}
    {Pre : Polygon → ℕ → Config → Prop} {Post : Polygon → Config → Config → Prop}
    {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ B) (hI : FInv W c₀ c) (hpre : Pre P W c)
    (hroom : c.nreg ALLOC + cost P c ≤ W) (h8 : bRestore ∉ B') :
    FRS B P W c₀ s c ztnxg (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      zth ∧
      ∀ r, bandOf r ∉ B' → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  zute
  have hp : ztlbw := fun q hq => hfr.1 q (by
      have : ztplq := by unfold bandOf bRestore; unfold FFix at hq; omega
      simp_all) (by unfold ALLOC; unfold FFix at hq; omega)
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hp q hq).trans ztfsi,
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a ztftc).trans ztduw⟩,
    (RF.of_frame hfr hI.hA).mono hB le_rfl, hpost, hfr.2.2.2.2.2.1, hfr.2.2.1, hfr.1⟩

/-- Arc `t` of region `r`. -/
def arcOf (N : NF) (r t : ℕ) : ARec := N.arc ztml

/-- **The facts about arc `t` of region `r`** the pair run needs (from the normal form). -/
structure ArcOK (E : FEnv) (t : ℕ) : Prop where
  ht : t < (E.N.region E.r).arcs.length
  hj : (E.N.region E.r).arcs.getD t 0 < E.N.arcs.length
  se : (arcOf E.N E.r t).s.edge < E.M.W.n
  ee : (arcOf E.N E.r t).e.edge < E.M.W.n
  sp : ProperPos E.M zti E.P.n (arcOf E.N E.r t).s
  ep : ProperPos E.M zti E.P.n (arcOf E.N E.r t).e
  sy : ∀ C : Chain, E.M = chainModel C → |(E.M.pos zti (arcOf E.N E.r t).s).2| < C.radius
  ey : ∀ C : Chain, E.M = chainModel C → |(E.M.pos zti (arcOf E.N E.r t).e).2| < C.radius
  sI : (normOf E.M zti (arcOf E.N E.r t).s).hgt = 0 ∨
    E.M.InnerPt (E.M.pos zti (arcOf E.N E.r t).s)
  eI : (normOf E.M zti (arcOf E.N E.r t).e).hgt = 0 ∨
    E.M.InnerPt (E.M.pos zti (arcOf E.N E.r t).e)
  wt : E.M.arcWt ztxdo ztxdn
    ≤ E.γ

/-! ## The reads -/
def prL1 : List Instr := [.copyN 81134 81001, .copyN 81121 81002, .copyN 81100 81030]
def prL2 : List Instr := [.copyN 81035 81103, .copyN 81036 81106, .copyN 81037 81107,
  .copyN 81038 81108, .copyN 81100 81031]
def prL3 : List Instr := [.copyN 81140 81103, .copyN 81141 81106]

/-- **The reads** of the pair: the ends of arc `i` in `81035 … 81038`, the start of arc `j` in
`81140`, `81141`. -/
def prReads : Stmt := .seq (Stmt.block prL1) (.seq arcLoad (.seq (Stmt.block prL2)
  (.seq arcLoad (Stmt.block prL3))))

/-- The registers the reads write. -/
def RdW (q : ℕ) : Prop :=
  LeafW q ∨ ztnhu ∨ q = 81121 ∨ q = 81134 ∨ q = 81140 ∨ q = 81141
theorem prReads_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {i j : ℕ} (hi : c.nreg 81030 = i) (hj : c.nreg 81031 = j) (hAi : ArcOK E i)
    (hAj : ArcOK E j) :
    FRS B E.P E.W c₀ prReads c 70 (fun c' =>
      c'.nreg 81035 = (arcOf E.N E.r i).s.edge ∧ c'.nreg 81036 = (arcOf E.N E.r i).s.hgt ∧
      c'.nreg 81037 = (arcOf E.N E.r i).e.edge ∧ c'.nreg 81038 = (arcOf E.N E.r i).e.hgt ∧
      c'.nreg 81140 = (arcOf E.N E.r j).s.edge ∧ c'.nreg 81141 = (arcOf E.N E.r j).s.hgt ∧
      ∀ q, ¬ RdW q → c'.nreg q = c.nreg q) := by
  have hN : ztzoy := by zuomw; exact hE.hNW
  zubnj

  have ok1 : okB E.W c.nmem prL1 c.nreg := by
    simp only [prL1, okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₁ := 3) (K₂ := 67) ztbbr ztbzx
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem prL1 c.nreg q := by_simp_all
  have v34 : c₁.nreg 81134 = E.NH := by zumwx; tauto
  have v21 : c₁.nreg 81121 = E.r := by zumwx; tauto
  have v00 : c₁.nreg 81100 = i := by zumwx; tauto
  have f₁ : ∀ q, q ≠ 81134 → q ≠ 81121 → q ≠ 81100 → c₁.nreg q = c.nreg q := fun q a b d => by
    zumwx; simp [prL1, regB, regI, upd, a, b, d]
  refine FRS.seq (K₁ := 30) (K₂ := 37) (arcLoad_fs hE hB hI₁ (N := E.N) by_simp_all
    (by zunry; exact hE.hr) (by rw [v21, v00]; exact hAi.ht) (by rw [v21, v00]; exact hAi.hj))
    zthgu
  obtain ⟨-, a03, a06, a07, a08, f₂⟩ := h₂
  rw [v21, v00] at a03 a06 a07 a08
  have j₂ : c₂.nreg 81031 = j := by
    grind
  have ok2 : okB E.W c₂.nmem prL2 c₂.nreg := by
    simp only [prL2, okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₁ := 5) (K₂ := 32) (FRS.block hB _ hI₂ ok2) ztnyq
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem prL2 c₂.nreg q := fun q => by zunbh
  have v35 : ztlye := by
    zudtw
  have v36 : c₃.nreg 81036 = (arcOf E.N E.r i).s.hgt := by
    zudtw
  have v37 : ztlyf := by
    zudtw
  have v38 : c₃.nreg 81038 = (arcOf E.N E.r i).e.hgt := by
    zudtw
  have w00 : c₃.nreg 81100 = j := by zumzv; tauto
  have f₃ : ∀ q, ¬ ztnhu → q ≠ 81100 → c₃.nreg q = c₂.nreg q := fun q a b => by
    zumzv; simp [prL2, regB, regI, upd, b, show q ≠ 81035 by omega, show q ≠ 81036 by omega,
      show q ≠ 81037 by omega, show q ≠ 81038 by omega]
  have w34 : c₃.nreg 81134 = E.NH := by
    grind
  have w21 : c₃.nreg 81121 = E.r := by
    grind
  refine FRS.seq (K₁ := 30) (K₂ := 2) (arcLoad_fs hE hB hI₃ (N := E.N) by_grind
    (by rw [w21]; exact hE.hr) (by rw [w21, w00]; exact hAj.ht) (by rw [w21, w00]; exact hAj.hj))
    ztnyr
  obtain ⟨-, b03, b06, -, -, f₄⟩ := h₄
  rw [w21, w00] at b03 b06
  have ok3 : okB E.W c₄.nmem prL3 c₄.nreg := by
    simp only [prL3, okB, okI, FScr, FOut]; norm_num
  refine (FRS.block hB _ hI₄ ok3).mono by_rfl zthi
  have e' : ∀ q, c'.nreg q = regB c₄.nmem prL3 c₄.nreg q := fun q => by zvmxl
  have f' : ∀ q, q ≠ 81140 → q ≠ 81141 → c'.nreg q = c₄.nreg q := fun q a b => by
    zvmwg; simp [prL3, regB, regI, upd, a, b]
  have g4 : ∀ q, ¬ LeafW q → q ≠ 81140 → q ≠ 81141 → c'.nreg q = c₃.nreg q := fun q h a b => by
    rw [f' q a b, f₄ q ztben ztben
      ztben ztben
      ztben ztben
      ztben]
  have nL : ∀ q, 81035 ≤ q → q ≤ 81038 → ¬ LeafW q := fun q a b => by
    unfold LeafW KeyW VertW; omega
  refine ⟨by_grind,
    by grind,
    by grind,
    by grind,
    by zvmwg; tauto,
    by zvmwg; tauto, fun q hq => ?_⟩
  have hL := fun h => hq zteg
  rw [g4 q hL ztcvj ztcvj,
    f₃ q ztbakd ztvr,
    f₂ q ztvr ztvr
      ztvr ztvr
      ztvr ztvr
      ztvr,
    f₁ q ztcvj ztcvj
      ztvr]

/-! ## The cutter and the pieces -/

/-- **The cutter's contract** at the input positions `u`, `v` (memory `m`, allocator `A`, list
at `L`). -/
def CutPost (E : FEnv) (u v : WPos) (m : ℕ → ℕ) (A L : ℕ) : Prop :=
  let q := m L
  let pc := fun (i j : ℕ) => m ztlfb
  let key := fun (e h : ℕ) => E.M.key zti ztcq
  L + 1 + 7 * q ≤ A ∧ q ≤ E.G E.γ ∧ 1 ≤ q ∧
  key zttvw zttvx = key u.edge u.hgt ∧
  key ztzxp ztzxq = key v.edge v.hgt ∧
  ztwyi ∧
  (∀ i, i + 1 < q → Chain.sideInArc ztzn (key v.edge v.hgt)
    ztzo) ∧
  (∀ i, i < q → pc i 4 = 0 → E.M.arcWt ztzn ztzo ≤ 1) ∧
  (∀ i, i < q → pc i 4 = 1 → ChainWF E.P A m ztkcg ∧
    ∃ Hs Cα N, ChainDescAt m ztkcg zti Hs Cα ∧
    NFWithin m zttwa A N ∧
    (∃ γ', γ' ≤ E.H E.γ ∧ IsCanonicalNF ztbdc zti N γ' 4) ∧
    E.M.arcSet ztzn ztzo = Cα.set ∧
    E.M.arcWt ztzn ztzo = Cα.m ∧
    PieceWalk E.M Cα zteyu zteyv ∧ Cα.P = Qof E.P ∧
    ((∀ d, d ≤ Cα.m → E.M.W.vtx ztbaab = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m → E.M.W.vtx ztbaab = Cα.vertex ztclf))) ∧
  (∀ i, i < q → ProperPos E.M zti E.P.n zteyu ∧
    ProperPos E.M zti E.P.n zteyv ∧ pc i 0 < E.M.W.n ∧ pc i 2 < E.M.W.n) ∧
  ztiup

/-- The arguments of the cutter (band `bCut`). -/
def cutL : List Instr := [.copyN 150000 81000, .copyN 150001 81035, .copyN 150002 81036,
  .copyN 150003 81037, .copyN 150004 81038, .copyN 150009 81003, .copyN 150013 81004]

/-- The piece loop's start: the list `81076`, its length `81078`, the index `81079`. -/
def plL : List Instr := [.copyN 81076 150010, .loadN 81078 81076, .constN 81079 0]

/-- **One ordered pair of arcs.** -/
def pairBody (cu sT : Stmt) : Stmt := .seq prReads (.seq (aNorm 81035) (.seq (aNorm 81037)
  (.seq (Stmt.block cutL) (.seq cu (.seq (Stmt.block plL) (pieceLoop sT))))))

/-- The registers the pair writes. -/
def PairW (q : ℕ) : Prop := PW q ∨ RdW q ∨ (81035 ≤ q ∧ q ≤ 81047) ∨ q = 81076 ∨ q = 81078

/-- The cost bound of a pair (`Kp`: the bound of a piece). -/
def pairK (E : FEnv) (Kp : ℕ) : ℕ :=
  70 + anK + anK + 7 + E.G E.γ + 3 + ztyxn
theorem pairBody_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {i j Kp : ℕ}
    (hi : c.nreg 81030 = i) (hj : c.nreg 81031 = j) (hAi : ArcOK E i) (hAj : ArcOK E j)
    (hPG : ∀ c', FInv E.W c₀ c' → CutPost E ztwpm
      ztwpl c'.nmem ztdo zthue →
      ∀ i', i' < c'.nmem zthue → PieceGood ztpxn c' zthue Kp i')
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + pairK E Kp ≤ E.W) :
    FRS B E.P E.W c₀ zttvo c (pairK E Kp) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → c'.nreg q = c.nreg q) ∧
      ztfn ∧
      ∃ c₃ : Config, FInv E.W c₀ c₃ ∧ CutPost E ztwpm
        ztwpl c₃.nmem zterl zthwc ∧
        c₃.nreg 81140 = (arcOf E.N E.r j).s.edge ∧ c₃.nreg 81141 = (arcOf E.N E.r j).s.hgt ∧
        ∀ i', i' < c₃.nmem zthwc →
          PieceDone ztmau c₃ c₃ zthwc i' ztdzf) := by
  obtain ⟨-, ue, upos, ukey, -⟩ := normOf_facts hAi.sp
  obtain ⟨-, ve, vpos, vkey, -⟩ := normOf_facts hAi.ep
  have hGW := hroom
  unfold pairK at hGW
  -- the reads
  refine FRS.seq (K₂ := pairK E Kp - 70) (prReads_fs hE hB hI hi hj hAi hAj)
    ztiy |>.mono ztjrd ztb
  obtain ⟨r35, r36, r37, r38, r40, r41, f₁⟩ := h₁
  -- normalise the start of arc `i`
  refine FRS.seq (K₂ := pairK E Kp - 70 - anK) (aNorm_fs hE hB hI₁
    by_omega
    (by zvnid; exact hAi.sp)
    (by rw [r35]; exact hAi.se)
    (fun C hC => by zvnid; exact hAi.sy C hC)
    by_omega) (fun c₂ hI₂ hA₂ h₂ => ?_) |>.mono (by unfold pairK; omega) (fun _ h => h)
  obtain ⟨n35, n36, f₂⟩ := h₂
  zvnid at n36
  have m37 : c₂.nreg 81037 = c₁.nreg 81037 :=
    f₂ _ by_norm_num by_norm_num ztqj by_norm_num by_omega
  have m38 : c₂.nreg 81038 = c₁.nreg 81038 :=
    f₂ _ by_norm_num by_norm_num ztqj by_norm_num by_omega
  -- normalise its end
  refine FRS.seq (K₂ := pairK E Kp - 70 - anK - anK) (aNorm_fs hE hB hI₂
    by_omega
    (by zvnbt; exact hAi.ep)
    (by rw [m37, r37]; exact hAi.ee)
    (fun C hC => by
      zvnbt; exact hAi.ey C hC)
    by_omega) (fun c₃ hI₃ hA₃ h₃ => ?_) |>.mono (by unfold pairK; omega) (fun _ h => h)
  obtain ⟨o37, o38, f₃⟩ := h₃
  zvnbt at o38
  have x35 : ztlye := by
    rw [f₃ _ by_norm_num by_norm_num ztqj by_norm_num by_omega, n35, r35]
  have x36 : c₃.nreg 81036 = (normOf E.M zti (arcOf E.N E.r i).s).hgt := by
    rw [f₃ _ by_norm_num by_norm_num ztqj by_norm_num by_omega, n36]
  have x37 : ztlyf := by_omega
  -- the cutter's arguments
  have ok4 : okB E.W c₃.nmem cutL c₃.nreg := by
    simp [cutL, okB, okI, FScr, FOut, bandOf, oracleBands, kernelBands, bCut]
  refine FRS.seq (K₁ := 7) (K₂ := pairK E Kp - 70 - anK - anK - 7) (FRS.block hB _ hI₃ ok4)
    (fun c₄ hI₄ hA₄ h₄ => ?_) |>.mono ztjrd ztb
  have e₄ : ∀ q, c₄.nreg q = regB c₃.nmem cutL c₃.nreg q := fun q => by rw [h₄]
  have f₄ : ∀ q, q < 150000 → c₄.nreg q = c₃.nreg q := fun q hq => by
    rw [e₄, regB_other _ _ _ ztdp]
    simp only [cutL, List.mem_cons, List.not_mem_nil, or_false] at hi
    zupt
  have rd0 : rd c₄ bCut 0 = E.MD := by
    show c₄.nreg 150000 = _
    zunce; zundz; rw [hI₃.hin _ ztbc, hE.i0]
  have rd1 : rd c₄ bCut 1 = (normOf E.M zti (arcOf E.N E.r i).s).edge := by
    show c₄.nreg 150001 = _
    zudjw
  have rd2 : rd c₄ bCut 2 = (normOf E.M zti (arcOf E.N E.r i).s).hgt := by
    show c₄.nreg 150002 = _
    zukri
  have rd3 : rd c₄ bCut 3 = (normOf E.M zti (arcOf E.N E.r i).e).edge := by
    show c₄.nreg 150003 = _
    zudjw
  have rd4 : rd c₄ bCut 4 = (normOf E.M zti (arcOf E.N E.r i).e).hgt := by
    show c₄.nreg 150004 = _
    zukri
  have rd9 : rd c₄ bCut 9 = E.γ := by
    show c₄.nreg 150009 = _
    zunce; zundz; rw [hI₃.hin _ ztbc, hE.i3]
  have rd13 : rd c₄ bCut 13 = E.g := by
    show c₄.nreg 150013 = _
    zunce; zundz; rw [hI₃.hin _ ztbc, hE.i4]
  have pu : (⟨rd c₄ bCut 1, rd c₄ bCut 2⟩ : WPos) =
      normOf E.M zti (arcOf E.N E.r i).s := by rw [rd1, rd2]
  have pv : (⟨rd c₄ bCut 3, rd c₄ bCut 4⟩ : WPos) =
      normOf E.M zti (arcOf E.N E.r i).e := by rw [rd3, rd4]
  have hEb := hE.rebase hI₄
  -- the cutter
  have hcall := FRS.callF hE.hcu
    (hE.hBc.trans (Finset.subset_union_right.trans hBT)) hI₄
    ⟨hE.hG, hE.hWh, by rw [rd13]; exact hEb.hX, by rw [rd9, rd13]; exact hEb.hcap,
      by zuofx; exact hEb.hwf, E.M, by zuofx; exact hEb.hMD, hE.hOk,
      by rw [pu]; exact (normOf_facts hAi.sp).1.1, by rw [pv]; exact (normOf_facts hAi.ep).1.1,
      by rw [rd1, ue]; exact hAi.se, by rw [rd3, ve]; exact hAi.ee,
      by rw [pu, rd2, upos]; exact hAi.sI, by rw [pv, rd4, vpos]; exact hAi.eI,
      by rw [pu, pv, ukey, vkey, rd9]; exact hAi.wt⟩
    by_grind (fun h => hE.hB8 (hE.hBc h))
  refine FRS.seq (K₂ := 3 + ztyxn)
    (hcall.mono (by rw [rd9]) ztb) zthgv |>.mono
    ztjrd ztb
  obtain ⟨hpost, -, -, f₅⟩ := h₅
  -- the piece loop's start
  have ok6 : okB E.W c₅.nmem plL c₅.nreg := by
    simp only [plL, okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (FRS.block hB _ hI₅ ok6)
    (fun c₆ hI₆ hA₆ h₆ => ?_)
  have e₆ : ∀ q, c₆.nreg q = regB c₅.nmem plL c₅.nreg q := fun q => by rw [h₆]
  have nm6 : ztlar := by rw [h₆]
  have s76 : c₆.nreg 81076 = rd c₅ bCut 10 := by_tauto
  have s78 : c₆.nreg 81078 = c₆.nmem ztvoc := by
    rw [nm6, s76, e₆]; rfl
  have s79 : c₆.nreg 81079 = 0 := by_tauto
  have a6 : ztfkx := by_tauto
  have f₆ : ∀ q, q ≠ 81076 → q ≠ 81078 → q ≠ 81079 → c₆.nreg q = c₅.nreg q := fun q a b d => by
    rw [e₆]; simp [plL, regB, regI, upd, a, b, d]
  -- the frame so far
  have g6 : ∀ q, 80000 ≤ q → q < 83000 → ¬ PairW q → c₆.nreg q = c.nreg q := fun q a b hq => by
    zufte
    rw [f₆ q ztwix
        ztwix
        ztwxe,
      f₅ q zther ztu,
      f₄ q by_omega,
      f₃ q a by_omega ztqj
        ztwix
        ztwix,
      f₂ q a by_omega ztqj
        ztwix
        ztwix,
      f₁ q ztbakd]
  have nP : ∀ q, 81007 ≤ q → q ≤ 81010 → ¬ PairW q := fun q a b => by
    unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega
  have hw₆ := hw.congr' (fun q a b => g6 q by_omega by_omega (nP q a b))
  -- through the cutter, from the reads
  have g16 : ∀ q, 81140 ≤ q → q ≤ 81141 → c₆.nreg q = c₁.nreg q := fun q a b => by
    zufte
    rw [f₆ q by_omega by_omega by_omega,
      f₅ q zther ztu,
      f₄ q by_omega, f₃ q by_omega by_omega ztqj by_omega by_omega,
      f₂ q by_omega by_omega ztqj by_omega by_omega]
  have t40 : c₆.nreg 81140 = (arcOf E.N E.r j).s.edge := by rw [g16 _ le_rfl by_norm_num, r40]
  have t41 : c₆.nreg 81141 = (arcOf E.N E.r j).s.hgt := by rw [g16 _ by_norm_num le_rfl, r41]
  -- the cutter's contract
  have hcp : CutPost E ztwpm
      ztwpl c₆.nmem zthwe ztvoc := by
    have hp := hpost E.M (by zuofx; exact hEb.hMD)
    rw [rd1, rd2, rd3, rd4, rd9] at hp
    rw [nm6, a6, s76]
    exact hp.2
  have hq₆ : c₆.nmem _ ≤ E.G E.γ := hcp.2.1
  -- the piece loop, rebased
  have hE₆ := hE.rebase hI₆
  have hloop := pieceLoop_fs hE₆ hB hBT ⟨hI₆.hw, by_omega, le_rfl, by_omega⟩ hw₆
    rfl s78 s79 (hPG c₆ hI₆ hcp) (by rw [t40, t41]; exact ⟨hAj.se, hAj.sp⟩) hnW
    (by
      have := Nat.mul_le_mul_left ztfnv hq₆
      show c₆.nreg ALLOC + _ ≤ E.W
      omega)
  refine ((FRS.restrict hI₆ hloop hI₆.hA).mono (by
    have := Nat.mul_le_mul_left ztfnv hq₆; omega) (fun c₇ h₇ => ?_))
  obtain ⟨w₇, f₇, m₇, d₇⟩ := h₇
  have nPW : ∀ q, ¬ PairW q → ¬ PW q := fun q h h' => h zthrp
  refine ⟨w₇, fun q a b hq => (f₇ q a b (nPW q hq)).trans (g6 q by_omega b hq),
    fun h => m₇ (by rw [g6 _ by_norm_num by_norm_num (nP _ le_rfl by_norm_num)]; exact h),
    c₆, hI₆, hcp, t40, t41, d₇⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
variable {E : FEnv} {c₀ c : Config}

/-- **What the run of the pair `(i, j)` tells**, with the final flag `f`. -/
def PairDone (E : FEnv) (c₀ : Config) (i j f : ℕ) : Prop :=
  ∃ c₃ : Config, FInv E.W c₀ c₃ ∧ CutPost E ztwpm
    ztwpl c₃.nmem zterl zthwc ∧
    c₃.nreg 81140 = (arcOf E.N E.r j).s.edge ∧ c₃.nreg 81141 = (arcOf E.N E.r j).s.hgt ∧
    ∀ i', i' < c₃.nmem zthwc →
      PieceDone ztmau c₃ c₃ zthwc i' f
theorem PairDone.mono {i j f f' : ℕ} (h : PairDone E c₀ i j f) (hf : f = 1 → f' = 1) :
    PairDone E c₀ i j f' := by
  obtain ⟨c₃, h1, h2, h3, h4, h5⟩ := h
  exact ⟨c₃, h1, h2, h3, h4, fun i' hi' => (h5 i' hi').mono hf⟩

/-- The piece obligations of the cut of arc `i` (piece bound `Kp`). -/
def PGood (E : FEnv) (c₀ : Config) (Kp i : ℕ) : Prop :=
  ∀ c', FInv E.W c₀ c' → CutPost E ztwpm
    ztwpl c'.nmem ztdo zthue →
    ∀ i', i' < c'.nmem zthue → PieceGood ztpxn c' zthue Kp i'
theorem nPair30 : ¬ PairW 81030 := by unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega
theorem nPair31 : ¬ PairW 81031 := by unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega
theorem nPair32 : ¬ PairW 81032 := by unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega

/-! ## The inner loop -/

/-- **The inner loop** over `j`. -/
def innerLoop (cu sT : Stmt) : Stmt :=
  .whileLtN 81031 81032 (.seq (pairBody cu sT) ztnpi)

/-- The invariant of the inner loop (from its start `c`). -/
def IInv (E : FEnv) (c₀ c : Config) (i k : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81031 → d.nreg q = c.nreg q) ∧
    ztdmr ∧ d.nreg 81031 ≤ k ∧
    ∀ j, j < d.nreg 81031 → PairDone E c₀ i j ztqlt
theorem innerLoop_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {i k Kp : ℕ}
    (hi : c.nreg 81030 = i) (hk : c.nreg 81032 = k) (h0 : c.nreg 81031 = 0)
    (hAi : ArcOK E i) (hA : ∀ t, t < k → ArcOK E t) (hPG : PGood E c₀ Kp i)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + zteul * k ≤ E.W) :
    FRS B E.P E.W c₀ zttpi c (zteul * k + 2) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81031 → c'.nreg q = c.nreg q) ∧
      ztfn ∧ ∀ j, j < k → PairDone E c₀ i j ztdzf) := by
  have hkW : k ≤ E.W := by
    grind
  have hq0 : c.nreg 81032 - c.nreg 81031 = k := by_omega
  refine (FRS.while (a := 81031) (b := 81032) (body := .seq zttvo
    ztnpi) (IInv E c₀ c i k)
    (fun d => d.nreg 81032 - d.nreg 81031) (pairK E Kp + 1) ztpbi
    ztgiz hI ⟨hw, fun _ _ _ _ _ => rfl, id, by_omega,
      fun j hj => by_omega⟩ by_simp_all).mono (by rw [hq0])
    ztjvq
  · zubri
    have d32 : ztutl := by rw [df _ by_norm_num by_norm_num nPair32 by_norm_num, hk]
    have d30 : d.nreg 81030 = i := by rw [df _ by_norm_num by_norm_num nPair30 by_norm_num, hi]
    zukql
    refine FRS.seq (K₁ := pairK E Kp) (K₂ := 1) (pairBody_fs hE hB hBT hId dw d30 rfl hAi
      zttlx hPG hnW by_omega) (fun c₁ hI₁ hA₁ h₁ => ?_)
    obtain ⟨w₁, f₁, m₁, pd⟩ := h₁
    have k1 : ztlxw := by rw [hI₁.hin _ ztbc, hE.k1]
    have j₁ : c₁.nreg 81031 = d.nreg 81031 := f₁ _ by_norm_num by_norm_num nPair31
    have ok : okB E.W c₁.nmem [.addN 81031 81031 81012] c₁.nreg := by
      simp only [okB, okI, FScr, FOut, k1, j₁]; grind
    zugak
    have e' : ∀ q, c'.nreg q = regB c₁.nmem [.addN 81031 81031 81012] c₁.nreg q := fun q => by
      zuczu
    have f' : ∀ q, q ≠ 81031 → c'.nreg q = c₁.nreg q := fun q h => by
      zublr
    have v31 : c'.nreg 81031 = d.nreg 81031 + 1 := by
      zvmwg; simp [regB, regI, upd, k1, j₁]
    have g07 : ztmuj := f' _ by_norm_num
    have c32 : ztlxn := by
      rw [f' _ by_norm_num, f₁ _ by_norm_num by_norm_num nPair32, d32]
    refine ⟨⟨w₁.congr' ztmjx, fun q a b hq h31 => by
      grind, fun h => by_omega,
      by omega, fun j hj => ?_⟩, by_omega⟩
    rw [g07]
    rcases Nat.lt_or_ge j (d.nreg 81031) with h | h
    · exact (dd j h).mono m₁
    · rw [show j = d.nreg 81031 by omega]; exact pd
  · zuth

    have c32 : ztlxn := by
      rw [cf _ by_norm_num by_norm_num nPair32 by_norm_num, hk]
    grind

/-! ## The outer loop -/

/-- **The outer loop** over `i`. -/
def outerLoop (cu sT : Stmt) : Stmt :=
  .whileLtN 81030 81032 (.seq ztoxt (.seq (innerLoop cu sT)
    ztnph))

/-- The invariant of the outer loop (from its start `c`). -/
def OInv (E : FEnv) (c₀ c : Config) (k : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81030 → q ≠ 81031 →
    d.nreg q = c.nreg q) ∧ (c.nreg 81007 = 1 → d.nreg 81007 = 1) ∧ d.nreg 81030 ≤ k ∧
    ∀ i, i < d.nreg 81030 → ∀ j, j < k → PairDone E c₀ i j ztqlt

/-- The cost bound of an outer step. -/
def outerK (E : FEnv) (Kp k : ℕ) : ℕ := zteul * k + 4
theorem outerLoop_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {k Kp : ℕ}
    (hk : c.nreg 81032 = k) (h0 : c.nreg 81030 = 0)
    (hA : ∀ t, t < k → ArcOK E t) (hPG : ∀ t, t < k → PGood E c₀ Kp t)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + (outerK E Kp k + 2) * k ≤ E.W) :
    FRS B E.P E.W c₀ (outerLoop E.cu E.sT) c ztebn (fun c' =>
      FWin E c' ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81030 → q ≠ 81031 →
        c'.nreg q = c.nreg q) ∧ (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∀ i, i < k → ∀ j, j < k → PairDone E c₀ i j ztdzf) := by
  have hkW : k ≤ E.W := by
    grind
  have hq0 : c.nreg 81032 - c.nreg 81030 = k := by_omega
  refine (FRS.while (a := 81030) (b := 81032) (body := .seq ztoxt
    (.seq zttpi ztnph)) (OInv E c₀ c k)
    (fun d => d.nreg 81032 - d.nreg 81030) (outerK E Kp k) ztpbi
    ztgiz hI ⟨hw, fun _ _ _ _ _ _ => rfl, id, by_omega,
      fun i hi => by_omega⟩ by_simp_all).mono (by rw [hq0])
    ztjvq
  · zubri
    have d32 : ztutl := by
      rw [df _ by_norm_num by_norm_num nPair32 by_norm_num by_norm_num, hk]
    zukql
    have ok0 : okB E.W d.nmem [.constN 81031 0] d.nreg := by
      zuph
    refine FRS.seq (K₁ := 1) (K₂ := zteul * k + 2 + 1) (FRS.block hB _ hId ok0)
      ztiy |>.mono (by unfold outerK; omega) ztb
    have e₁ : ∀ q, c₁.nreg q = regB d.nmem [.constN 81031 0] d.nreg q := fun q => by zvnbm
    have f₁ : ∀ q, q ≠ 81031 → c₁.nreg q = d.nreg q := fun q h => by
      zukq
    have z31 : c₁.nreg 81031 = 0 := by_tauto
    have w₁ : ztmtb := dw.congr' (fun q a b => f₁ q by_omega)
    refine FRS.seq (K₁ := zteul * k + 2) (K₂ := 1)
      (innerLoop_fs hE hB hBT hI₁ w₁ (f₁ _ by_norm_num) by_simp_all z31
        zttlx hA (hPG _ hlt) hnW (by unfold outerK at hroomd; omega))
      ztcne
    obtain ⟨w₂, f₂, m₂, pd⟩ := h₂
    zubrb
    have i₂ : c₂.nreg 81030 = d.nreg 81030 := by
      rw [f₂ _ by_norm_num by_norm_num nPair30 by_norm_num, f₁ _ by_norm_num]
    have ok : okB E.W c₂.nmem [.addN 81030 81030 81012] c₂.nreg := by
      simp only [okB, okI, FScr, FOut, k1, i₂]; grind
    zugal
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.addN 81030 81030 81012] c₂.nreg q := fun q => by
      zuczu
    have f' : ∀ q, q ≠ 81030 → c'.nreg q = c₂.nreg q := fun q h => by
      zublr
    have v30 : c'.nreg 81030 = d.nreg 81030 + 1 := by
      zvmwg; simp [regB, regI, upd, k1, i₂]
    have g07 : ztsee := f' _ by_norm_num
    have g07' : c₂.nreg 81007 = 1 → c'.nreg 81007 = 1 := fun h => by_omega
    have c32 : ztlxn := by
      rw [f' _ by_norm_num, f₂ _ by_norm_num by_norm_num nPair32 by_norm_num,
        f₁ _ by_norm_num, d32]
    refine ⟨⟨w₂.congr' ztmjx, fun q a b hq h30 h31 => by
      grind,
      fun h => g07' (m₂ by_grind),
      by omega, fun i hi j hj => ?_⟩, by_omega⟩
    rcases Nat.lt_or_ge i (d.nreg 81030) with h | h
    · exact ((dd i h j hj).mono (fun h => m₂ by_grind)).mono g07'
    grind
  · zuth

    have c32 : ztlxn := by
      rw [cf _ by_norm_num by_norm_num nPair32 by_norm_num by_norm_num, hk]
    grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-! ## Blocks outside the search -/

/-- The side condition of an instruction of a block run outside the search. -/
def okX (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN _ k => k ≤ W
  | .copyN _ _ => True
  | .addN _ a b => f a + f b ≤ W
  | .subN _ _ _ => True
  | .loadN _ _ => True
  | _ => False

/-- The side conditions of a block run outside the search. -/
def okXB (W : ℕ) (m : ℕ → ℕ) : List Instr → ztjx → Prop
  | [], _ => True
  | i :: l, f => okX W f i ∧ okXB W m l ztefz
theorem execB {P : Polygon} {W : ℕ} : ∀ (l : List Instr) {c : Config}, WordsBounded W c →
    okXB W c.nmem l c.nreg →
    Exec P W ztqcu c { c with nreg := regB c.nmem l c.nreg } l.length
  | [], c, hw, _ => Exec.skip hw
  | i :: l, c, hw, h => by
    obtain ⟨hi, hl⟩ := h
    have h1 : Exec P W ztbgj c { c with nreg := regI c.nmem i c.nreg } 1 := by
      cases i with
      | constN r k => exact Exec.constN hw r k hi
      | copyN r a => exact Exec.copyN hw r a
      | addN r a b => exact Exec.addN hw r a b hi
      | subN r a b => exact Exec.subN hw r a b
      | loadN r a => exact Exec.loadN hw r a
      | _ => exact absurd hi by_tauto
    have h2 := execB l (P := P) h1.wb_right hl
    exact (Exec.seq h1 h2).cast by_grind

/-! ## The program -/

/-- The constants, the input size and `n / 2`, the kind of the model (`81029`). -/
def fIniL : List Instr := [.constN 81007 0, .constN 81011 0, .constN 81012 1, .constN 81013 2,
  .constN 81014 3, .constN 81015 5, .constN 81016 7, .constN 81024 10,
  .addN 81028 81004 81014, .loadN 81028 81028, .addN 81028 81028 81020, .loadN 81023 81028,
  .addN 81022 81023 81023, .loadN 81029 81000]

/-- The walk data of a chain model (`m` from the chain descriptor). -/
def fChL : List Instr := [.addN 81028 81000 81014, .loadN 81028 81028, .constN 81021 6,
  .addN 81019 81028 81028, .addN 81019 81019 81021, .copyN 81025 81019, .addN 81017 81019 81012]

/-- The walk data of the interior model. -/
def fIntL : List Instr := [.constN 81021 0, .copyN 81017 81020, .copyN 81019 81020,
  .copyN 81025 81020]

/-- **The initialisation.** -/
def fInit : Stmt := .seq (.instr (.inputSize 81020)) (.seq (Stmt.block fIniL)
  (.ifLtN 81011 81029 (Stmt.block fIntL) (Stmt.block fChL)))

/-- The registers the initialisation writes. -/
def IniW (q : ℕ) : Prop := 81007 ≤ q ∧ q < 81030
theorem fInit_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (h10 : 10 ≤ W)
    (hnW : P.n ≤ W) {X : MemCtx} (hX : X.holds P c.nmem ztjsd ztm)
    (hhalf : X.Halves) (hMD : c.nreg 81000 + 6 ≤ c.nreg ALLOC)
    (hk : c.nmem ztbzs = 0 → 2 * c.nmem ztcza + 7 ≤ W) :
    ∃ c₀ k, Exec P W fInit c c₀ k ∧ k ≤ 30 ∧ c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧
      c₀.rmem = c.rmem ∧ c₀.output = c.output ∧ ztius ∧
      c₀.nreg 81007 = 0 ∧ c₀.nreg 81011 = 0 ∧ c₀.nreg 81012 = 1 ∧ c₀.nreg 81013 = 2 ∧
      c₀.nreg 81014 = 3 ∧ c₀.nreg 81015 = 5 ∧ c₀.nreg 81016 = 7 ∧ c₀.nreg 81024 = 10 ∧
      c₀.nreg 81020 = P.n ∧ c₀.nreg 81023 = P.n / 2 ∧ c₀.nreg 81022 = 2 * zttbi ∧
      (c.nmem ztbzs = 0 → c₀.nreg 81021 = 6 ∧
        c₀.nreg 81019 = 2 * c.nmem ztcza + 6 ∧
        c₀.nreg 81025 = 2 * c.nmem ztcza + 6 ∧
        c₀.nreg 81017 = 2 * c.nmem ztcza + 7) ∧
      (c.nmem ztbzs ≠ 0 → c₀.nreg 81021 = 0 ∧ c₀.nreg 81019 = P.n ∧
        c₀.nreg 81025 = P.n ∧ c₀.nreg 81017 = P.n) := by
  obtain ⟨hg3, hT⟩ := hhalf P c.nmem _ _ hX
  obtain ⟨hTn, hTv⟩ := hT P.n le_rfl
  zueqh
  have h4 : c.nreg 81004 ≠ 0 ∨ c.nreg 81004 = 0 := by_omega
  -- the input size
  have e1 := Exec.inputSize hw 81020 hnW
  set c₁ : Config := { c with nreg := upd c.nreg 81020 P.n } with hc₁
  have hw₁ := e1.wb_right
  have r₁ : ∀ q, q ≠ 81020 → c₁.nreg q = c.nreg q := by_simp_all
  have n₁ : c₁.nreg 81020 = P.n := by_rfl
  -- the constants
  have ok2 : okXB W c₁.nmem fIniL c₁.nreg := by
    simp only [fIniL, okXB, okX, regI]
    simp only [upd, n₁, r₁ 81004 by_norm_num, show c₁.nmem = c.nmem from rfl]
    grind
  have e2 := execB (P := P) fIniL hw₁ ok2
  set c₂ : Config := { c₁ with nreg := regB c₁.nmem fIniL c₁.nreg } with hc₂
  have hw₂ := e2.wb_right
  have v₂ : ∀ q, c₂.nreg q = regB c.nmem fIniL c₁.nreg q := by_simp_all
  have f₂ : ∀ q, ¬ IniW q → c₂.nreg q = c.nreg q := fun q hq => by
    rw [v₂, regB_other _ _ _ ztdp, r₁ q (fun h => hq ztggl)]
    simp only [fIniL, List.mem_cons, List.not_mem_nil, or_false] at hi
    zujpu
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> zvmwd <;> omega
  have z : zturh := by_rfl
  have kd : c₂.nreg 81029 = c.nmem ztbzs := by
    rfl
  have c20 : c₂.nreg 81020 = P.n := by_rfl
  have c00 : c₂.nreg 81000 = c.nreg 81000 := f₂ _ ztggl
  have c12 : zthor := by_rfl
  have c14 : zturi := by_rfl
  have hv : ∀ q, q ∈ [81007, 81011, 81012, 81013, 81014, 81015, 81016, 81024, 81023, 81022] →
      ∀ c' : Config, (∀ r, r ∉ [81017, 81019, 81021, 81025, 81028] → c'.nreg r = c₂.nreg r) →
      c'.nreg q = c₂.nreg q := fun q hq c' h => h q (by simp at hq ⊢; omega)
  have vals : c₂.nreg 81007 = 0 ∧ c₂.nreg 81011 = 0 ∧ c₂.nreg 81012 = 1 ∧ c₂.nreg 81013 = 2 ∧
      c₂.nreg 81014 = 3 ∧ c₂.nreg 81015 = 5 ∧ c₂.nreg 81016 = 7 ∧ c₂.nreg 81024 = 10 ∧
      c₂.nreg 81020 = P.n ∧ c₂.nreg 81023 = P.n / 2 ∧ c₂.nreg 81022 = 2 * zttbi := by
    refine ⟨?_, z, c12, ?_, c14, ?_, ?_, ?_, c20, ?_, ?_⟩ <;>
      (rw [v₂]; simp [fIniL, regB, regI, upd, n₁, r₁ 81004 by_norm_num])
    · omega
    omega
  -- the walk data
  by_cases a : c₂.nreg 81011 < c₂.nreg 81029
  · have hk1 : ztbaci := by_omega
    have ok3 : okXB W c₂.nmem fIntL c₂.nreg := by
      simp only [fIntL, okXB, okX]; norm_num
    have e3 := execB (P := P) fIntL hw₂ ok3
    refine ⟨_, _, .seq e1 (.seq e2 (.ifLtN_true a e3)), by_decide, rfl, rfl, rfl, rfl,
      fun q hq => ?_,
      ?_⟩
    · show regB c₂.nmem fIntL c₂.nreg q = _
      zufoh
      simp only [fIntL, List.mem_cons, List.not_mem_nil, or_false] at hi
      zujpu
      zubca
    · have g : ∀ q, q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 →
          regB c₂.nmem fIntL c₂.nreg q = c₂.nreg q := fun q a b d e => by
        simp [fIntL, regB, regI, upd, a, b, d, e]
      zubue
      have G : ∀ q, q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 → ∀ v, c₂.nreg q = v →
          regB c₂.nmem fIntL c₂.nreg q = v := by_grind
      have w : ∀ q, q = 81021 ∨ q = 81017 ∨ q = 81019 ∨ q = 81025 →
          regB c₂.nmem fIntL c₂.nreg q = if q = 81021 then 0 else P.n := fun q hq => by
        rcases hq with rfl | rfl | rfl | rfl <;> simp [fIntL, regB, regI, upd, c20]
      grind
  · have hk0 : c.nmem ztbzs = 0 := by_omega
    have hm := hk hk0
    have ok3 : okXB W c₂.nmem fChL c₂.nreg := by
      simp only [fChL, okXB, okX, regI]
      simp only [upd, c00, c14, c12, show c₂.nmem = c.nmem from rfl]
      grind
    have e3 := execB (P := P) fChL hw₂ ok3
    refine ⟨_, _, .seq e1 (.seq e2 (.ifLtN_false a e3)), by_decide, rfl, rfl, rfl, rfl,
      fun q hq => ?_,
      ?_⟩
    · show regB c₂.nmem fChL c₂.nreg q = _
      zufoh
      simp only [fChL, List.mem_cons, List.not_mem_nil, or_false] at hi
      zujpu
      zupt
    · have g : ∀ q, q ≠ 81028 → q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 →
          regB c₂.nmem fChL c₂.nreg q = c₂.nreg q := fun q a b d e f => by
        simp [fChL, regB, regI, upd, a, b, d, e, f]
      zubue
      have G : ∀ q, q ≠ 81028 → q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 → ∀ v,
          c₂.nreg q = v → regB c₂.nmem fChL c₂.nreg q = v := by_grind
      have w21 : regB c₂.nmem fChL c₂.nreg 81021 = 6 := by_rfl
      have w19 : regB c₂.nmem fChL c₂.nreg 81019 = 2 * c.nmem ztcza + 6 := by
        simp [fChL, regB, regI, upd, c00, c14, show c₂.nmem = c.nmem from rfl]; ring
      have w25 : regB c₂.nmem fChL c₂.nreg 81025 = 2 * c.nmem ztcza + 6 := by
        tauto
      have w17 : regB c₂.nmem fChL c₂.nreg 81017 = 2 * c.nmem ztcza + 7 := by
        simp [fChL, regB, regI, upd, c00, c14, c12, show c₂.nmem = c.nmem from rfl]; ring
      grind
variable (C : Chain) (Q : Polygon) {v : ℕ}
theorem chain_vtx_mem (h6 : 6 ≤ v) (hv : v ≤ 2 * C.m + 6) :
    (chainModel C).pos Q ztcfs ∈ C.set := by
  rw [pos_eq_sidePt, param_vtx]
  show Chazelle.Chain.sidePt ztcs v 0 ∈ C.set
  have := C.sideWalk_tour_pt_mem C.sideBeta (i := v - 6) (t := 0) by_omega ztdnl
    le_rfl one_pos
  simp_all
theorem chain_vtx_six
    (hv : (chainModel C).pos Q ztcfs ∈ C.set) : 6 ≤ v := by
  zumv
  rw [pos_eq_sidePt, param_vtx] at hv
  exact IOrc.box_pos_not_mem C by_simp_all le_rfl one_pos hv
theorem chain_edge_mem {n e h : ℕ} (h6 : 6 ≤ e) (he : e < 2 * C.m + 6)
    (hp : ProperPos ztc Q n ztcq) : (chainModel C).pos Q ztcq ∈ C.set := by
  rw [pos_eq_sidePt]
  show Chazelle.Chain.sidePt ztcs e _ ∈ C.set
  have := C.sideWalk_tour_pt_mem C.sideBeta (i := e - 6)
    (t := (chainModel C).param Q ztcq) by_omega (fun h' => absurd h' by_omega) hp.1 hp.2.1
  simp_all
theorem chain_m_eq {C C' : Chain} (h : chainModel C = chainModel C') : C.m = C'.m := by
  have := congrArg (fun M : Model => M.W.n) h
  simp only [chainModel_n] at this
  omega
theorem interiorWalk_n' : (interiorWalk Q).n = Q.n := by
  zufdi
  · rfl
  · zufan

/-! ## The environment of a run -/

/-- The environment of the search started in `c` (model `M`, normal form `N`). -/
def fEnv (P : Polygon) (W : ℕ) (M : Model) (N : NF) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (cu sT : Stmt) (Bc Bo : Finset ℕ) (F G H κt : ℕ → ℕ) (c : Config) : FEnv where
  P := P
  W := W
  M := M
  N := N
  X := X
  Ok := Ok
  cu := cu
  sT := sT
  Bc := Bc
  Bo := Bo
  F := F
  G := G
  H := H
  κt := κt
  A₀ := c.nreg ALLOC
  m₀ := c.nmem
  MD := c.nreg 81000
  NH := c.nreg 81001
  r := c.nreg 81002
  γ := c.nreg 81003
  g := c.nreg 81004
  d := c.nreg 81005
  D := c.nreg 81006

/-- **The start of the search**: the initialisation runs, and the run facts hold after it. -/
theorem find_start {P : Polygon} {W : ℕ} {c : Config} {M : Model} {N : NF} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {cu sh : Stmt} {Bs Bc Bo : Finset ℕ} {F G H : ℕ → ℕ}
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hcu : CutterOK cu Bc G H X Ok)
    (hBc : Bc ⊆ Bo) (hBo : oracleBands ⊆ Bo) (hB8 : bRestore ∉ Bo) (hloc : X.CapLocal)
    (hhalf : X.Halves) (hOkM : ∀ P M, Ok P M → OkModel P M ∨ M = interiorModel zta)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hX : X.holds P c.nmem ztjsd ztm)
    (hcap : c.nreg 81003 ≤ X.cap P c.nmem ztjsd)
    (hwf : ModelDescWF P ztm c.nmem ztbzs)
    (hreg : c.nmem ztbzs = 0 → ∀ H C, ChainDescAt c.nmem zthuy zta H C →
      HostRegular (Qof P).n H)
    (hsimp : c.nmem ztbzs = 0 → ∀ H C, ChainDescAt c.nmem zthuy zta H C →
      C.P.Simple)
    (hMD : ModelDescAt c.nmem ztbzs zta M) (hGM : GoodModel M) (hOk : Ok P M)
    (hNW : NFWithin c.nmem ztqib ztm N) (hNF : IsNF M zta N)
    (hdeg : M.DegLe ztwiv ztghi)
    (hsg : M.Semigranular ztwiv ztbol) (hr : c.nreg 81002 < N.nRegions) :
    ∃ c₀ k, Exec P W fInit c c₀ k ∧ k ≤ 30 ∧ c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧
      c₀.rmem = c.rmem ∧ c₀.output = c.output ∧
      ztius ∧ c₀.nreg 81007 = 0 ∧
      FGood (fEnv P W M N X Ok cu ztibi Bc Bo F G H testκ c) c₀ := by
  zuc
  have hk : c.nmem ztbzs = 0 → 2 * c.nmem ztcza + 7 ≤ W := fun h0 => by
    rcases hMD with ⟨-, H', C', hC, hM⟩ | ⟨h1, -⟩
    · have := walk_le_W (P := P) (M := M) (W := W) (Or.inl ⟨h0, H', C', hC, hM⟩) hwf hWh hM
      zukdm
      grind
    · omega
  obtain ⟨c₀, k, ex, hk30, nm, rr, rm, ro, fr, v07, v11, v12, v13, v14, v15, v16, v24, v20, v23, v22, vch,
    vin⟩ := fInit_exec hw (by unfold hostWords at hWh; omega) (by unfold hostWords at hWh; omega)
      hX hhalf hwf.1 hk
  have fx : ∀ q, q < 81007 → c₀.nreg q = c.nreg q := fun q h => fr q ztggl
  have hA : ztsfw := fx _ by_decide
  refine ⟨c₀, k, ex, hk30, nm, rr, rm, ro, fr, v07, ?_⟩
  -- the walk data, by the kind of the model
  have hdata : c₀.nreg 81017 = M.W.n ∧
      (∀ v, v < M.W.n → c₀.nreg 81021 ≤ v → v ≤ c₀.nreg 81019 →
        ∀ C : Chain, M = chainModel C → M.pos zta ztcfs ∈ C.set) ∧
      (∀ v, v < M.W.n → (∀ C : Chain, M = chainModel C → M.pos zta ztcfs ∈ C.set) →
        c₀.nreg 81021 ≤ v ∧ v ≤ c₀.nreg 81019) ∧
      (∀ C : Chain, M = chainModel C → 6 ≤ c₀.nreg 81021) ∧
      (∀ e h, e < M.W.n → c₀.nreg 81021 ≤ e → e < c₀.nreg 81025 →
        ProperPos M zta P.n ztcq →
        ∀ C : Chain, M = chainModel C → M.pos zta ztcq ∈ C.set) ∧
      (∀ e, e < M.W.n → M.counted e → c₀.nreg 81021 ≤ e ∧ e < c₀.nreg 81025) := by
    rcases hMD with ⟨h0, H', C', hC, hM⟩ | ⟨h1, -, hM⟩
    · obtain ⟨d21, d19, d25, d17⟩ := vch h0
      zukdm
      rw [show c.nreg 81000 + 1 + 2 = c.nreg 81000 + 3 by omega] at hm
      zvmwi at d19 d25 d17
      have hn : M.W.n = 2 * C'.m + 7 := by zvmzx; exact chainModel_n C'
      refine ⟨by_omega, fun v hv a b C hC' => ?_, fun v hv h => ?_, fun _ _ => by_omega,
        fun e h he a b hp C hC' => ?_, fun e he hc => ?_⟩
      · rw [hC']
        have := chain_m_eq ztvsq
        exact chain_vtx_mem C _ by_omega by_omega
      · have h6 := chain_vtx_six C' zta (by rw [← hM]; exact h C' hM)
        omega
      · rw [hC'] at hp ⊢
        have := chain_m_eq ztvsq
        exact chain_edge_mem C _ by_omega by_omega hp
      · zuksx
        obtain ⟨c1, c2⟩ := hc
        omega
    · have h1' : ztbaci := by_omega
      obtain ⟨d21, d19, d25, d17⟩ := vin h1'
      have hn : M.W.n = P.n := by
        zvmzx; show (interiorWalk zta).n = _; zunqd
      refine ⟨by_omega, fun v _ _ _ C hC => absurd ztqpd
          zthgg,
        fun v hv _ => by_omega, fun C hC => absurd ztqpd zthgg,
        fun e h _ _ _ _ C hC => absurd ztqpd zthgg,
        fun e he _ => by_omega⟩
  obtain ⟨wn, hvr, hvc, vlo6, ehr, ehc⟩ := hdata
  exact {
    hT := testOK hsh hBs hloc hB8 hBo, hcu := hcu, hBc := hBc, hBo := hBo, hB8 := hB8,
    hloc := hloc, hhalf := hhalf, hOkM := hOkM, hG := hG, hWh := hWh, hX := hX, hcap := hcap,
    hwf := hwf, hreg := hreg, hsimp := hsimp, hMD := hMD, hGM := hGM, hOk := hOk, hNW := hNW,
    hNF := hNF, hdeg := hdeg, hsg := hsg, hr := hr, a0 := hA, m0 := nm,
    i0 := fx _ by_norm_num, i1 := fx _ by_norm_num, i2 := fx _ by_norm_num,
    i3 := fx _ by_norm_num, i4 := fx _ by_norm_num, i5 := fx _ by_norm_num,
    i6 := fx _ by_norm_num, k0 := v11, k1 := v12, k2 := v13, k3 := v14, k5 := v15, k7 := v16,
    pn := v20, nE := v22, hE2 := v23, wn := wn, k10 := v24, hvr := hvr, hvc := hvc,
    vlo6 := vlo6, ehr := ehr, ehc := ehc }

/-! ## The number of arcs -/

/-- The reads of the arc count `k` (`81032`) of region `r` (`0` if the region has no exit chord),
and `i = 0` (`81030`). -/
def aCntL : List Instr :=
  [.copyN 81134 81001, .copyN 81121 81002, .addN 81114 81134 81015, .loadN 81114 81114,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .loadN 81032 81114,
    .addN 81115 81114 81013, .loadN 81115 81115, .constN 81030 0]

/-- **The arc count.** -/
def aCntS : Stmt := .seq (Stmt.block aCntL) (.ifLtN 81011 81115 .skip (Stmt.block [.constN 81032 0]))

/-- The arc count of the search. -/
def kOf (E : FEnv) : ℕ :=
  if (E.N.region E.r).chords = [] then 0 else (E.N.region E.r).arcs.length
variable {E : FEnv} {c₀ c : Config}
theorem cnt_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c) :
    FRS B E.P E.W c₀ aCntS c 17 (fun c' => c'.nreg 81030 = 0 ∧ c'.nreg 81032 = kOf E ∧
      ∀ q, q ≠ 81134 → q ≠ 81121 → q ≠ 81114 → q ≠ 81115 → q ≠ 81030 → q ≠ 81032 →
        c'.nreg q = c.nreg q) := by
  have hN : NFWithin c.nmem E.NH ztdq E.N := by
    have h0 : ztzoy := by zuomw; exact hE.hNW
    exact Robust.transport h0 zttj
  have hNA := hN.nfAt
  obtain ⟨hB7, -, -, hrb, -, -⟩ := nf_bounds hN
  zubwb

  have hrl : E.r < E.N.regions.length := hE.hr
  obtain ⟨hna, hnc, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
  have b1 := hrb _ hE.hr
  zubnj

  zuwl
  have k2 : ztpmd := by rw [hI.hin _ ztbc, hE.k2]
  have e5 : c.nmem ztswx + E.r + E.r + E.r + E.r + E.r = c.nmem ztswx + 5 * E.r := by
    ring
  have ok : okB E.W c.nmem aCntL c.nreg := by
    simp only [aCntL, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k2, e01, e02]
    grind
  refine FRS.seq (K₁ := 13) (K₂ := 4) ztgds ztbzx
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem aCntL c.nreg q := fun q => by zvnbm
  have v30 : c₁.nreg 81030 = 0 := by_tauto
  have v32 : c₁.nreg 81032 = (E.N.region E.r).arcs.length := by
    zumwx; simp [aCntL, regB, regI, upd, k5, e01, e02]; simp_all
  have v15 : c₁.nreg 81115 = (E.N.region E.r).chords.length := by
    zumwx; simp [aCntL, regB, regI, upd, k5, k2, e01, e02]; simp_all
  have f₁ : ∀ q, q ≠ 81134 → q ≠ 81121 → q ≠ 81114 → q ≠ 81115 → q ≠ 81030 → q ≠ 81032 →
      c₁.nreg q = c.nreg q := fun q a b d e f g => by
    rw [e₁, regB_other _ _ _ ztdp]
    simp only [aCntL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zubzs
  zucna
  by_cases a : c₁.nreg 81011 < c₁.nreg 81115
  · have hne : ztfdm := by
      grind
    refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨v30, ?_, f₁⟩)).mono by_omega ztb
    rw [v32]; unfold kOf; simp_all
  · have he : (E.N.region E.r).chords = [] := by
      simp_all
    have ok2 : okB E.W c₁.nmem [.constN 81032 0] c₁.nreg := by
      zuph
    refine (FRS.ifF a ztjiu).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₁.nmem [.constN 81032 0] c₁.nreg q := fun q => by zvmxl
    refine ⟨by zvmwg; tauto, by zvmwg; simp [regB, regI, upd, kOf, he],
      fun q a b d e f g => by zvmwg; simp [regB, regI, upd, g]; grind⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
variable {E : FEnv} {c₀ : Config}
theorem FGood.kind (hE : FGood E c₀) :
    (∃ C : Chain, C.P.Simple ∧ E.M = chainModel C) ∨ E.M = interiorModel zti := by
  rcases hE.hOkM _ _ hE.hOk with ⟨H, C, -, -, -, hs, hM⟩ | hI
  · grind
  simp_all
theorem FGood.end_ok (hE : FGood E c₀) {x : WPos}
    (hx : ProperPos E.M zti (Qof E.P).n x) (hk : E.M.key zti x < E.M.W.n)
    (hy : ∀ C : Chain, E.M = chainModel C → |(E.M.pos zti x).2| < C.radius) :
    x.edge < E.M.W.n ∧
      ((normOf E.M zti x).hgt = 0 ∨ E.M.InnerPt (E.M.pos zti x)) := by
  zunx
  zukta
  obtain ⟨-, -, hpos, -, hcase⟩ := normOf_facts hx
  have hkey : E.M.key zti x = x.edge + E.M.param zti x := rfl
  have hxe : x.edge < E.M.W.n := by
    have : (x.edge : ℝ) < E.M.W.n := by zungt
    simp_all
  refine ⟨hxe, ?_⟩
  zuklc
  · omega
  right
  have hp' : 0 < E.M.param zti x := by
    zuhat
    · simp_all
    omega
  zubcv
  · have hy' := hy C hM
    zvmzx at hxe hx hy' ⊢
    exact innerPt_chain_walk C zti hxe hx.1 hx.2.1.le hy'
  · zvmzx at hxe hx ⊢
    have hn3 : 3 ≤ (Qof E.P).n := by zvmxg; exact hE.hG.1.1
    zubkw
    exact innerPt_mi_edge ztqcr hn3
      ztlgp by_simp_all hx.2.1
theorem FGood.arc_abs (hE : FGood E c₀) (hne : (E.N.F E.M zti).Nonempty) {j : ℕ}
    (hj : j < E.N.arcs.length) :
    (∀ C : Chain, E.M = chainModel C → |(E.M.pos zti (E.N.arc j).s).2| < C.radius) ∧
      (∀ C : Chain, E.M = chainModel C → |(E.M.pos zti (E.N.arc j).e).2| < C.radius) := by
  refine ztklb <;>
  · obtain ⟨C', hs, hM'⟩ : ∃ C' : Chain, C'.P.Simple ∧ E.M = chainModel C' := by
      rcases hE.kind with h | hI
      · zubh
      · exact absurd ztmkt (chainModel_ne_interior C zti)
    zucly

    have := arc_abs_lt hs hNF hne hj
    zuimi

/-- **The arcs of a region with an exit chord.** -/
theorem FGood.arcOK (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) : ArcOK E t := by
  zucmm
  obtain ⟨-, -, -, reg, hRC, -, hArcs, hRg, -, -, hpp⟩ := hE.hNF
  zunx
  -- the family is nonempty
  have hne : (E.N.F E.M zti).Nonempty := by
    zult

    have hmem : ztpjg := by
      zubsu

    exact ztmqb
  zufpf
  have hjm : ztizw := by
    simp_all
  obtain ⟨hj, -⟩ := (hArcs.2.2.2 E.r hr j).1 hjm
  zubjk

  obtain ⟨sy, ey⟩ := hE.arc_abs hne hj
  have hs := hE.end_ok (hpp j hj).1 ha sy
  have he := hE.end_ok (hpp j hj).2 hb ey
  have hps : ProperPos E.M zti E.P.n (E.N.arc j).s := by_simp_all
  have hpe : ProperPos E.M zti E.P.n (E.N.arc j).e := by_simp_all
  exact ⟨ht, hj, hs.1, he.1, hps, hpe, sy, ey, hs.2, he.2,
    (BoxT.arcWt_le_weight (hArcs.1 j hj).2).trans (hE.hsg _ hU)⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sideInArc)

/-- **The walk edges met by the open key interval of a piece** `(s, s + m)`. -/
theorem piece_edges {s m n : ℕ} (hs : s < n) (hm : 0 < m) (hmn : m < n) {p : ℕ} (hp : p < n) :
    (∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc (s : ℝ) ((ztbnl % n : ℕ) : ℝ) ztk) ↔
      ∃ d, d < m ∧ ztbuf % n = p := by
  rw [Model.mem_arcEdges_iff]
  zuhtk
  · rw [Nat.mod_eq_of_lt hw]
    have h1 : (s : ℝ) < ((s + m : ℕ) : ℝ) := by_simp_all
    zubel
    constructor
    · zukoh
      have a' : p < s + m := by exact_mod_cast a
      zugkt

    · zuifn
      zvmyc at e
      exact ⟨by exact_mod_cast (by omega : p < s + m), by exact_mod_cast (by omega : s < p + 1)⟩
  · have e1 : ztbnl % n = s + m - n := by
      zul
    zukd
    have h1 : ¬ (s : ℝ) < ((s + m - n : ℕ) : ℝ) := by
      have : ¬ s < s + m - n := by_omega
      simp_all
    zubmd
    constructor
    · zuknw
      · have a' : p < s + m - n := by exact_mod_cast a
        exact ⟨p + n - s, by_omega, by
          rw [show s + (p + n - s) = p + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]⟩
      · zugkt

    · zuifn
      by_cases h : s + d < n
      · zvnnm at e
        right; exact_mod_cast (by omega : s < p + 1)
      · zvnae at e
        left; exact_mod_cast (by omega : p < s + m - n)

/-- **A piece of weight `m` over `m` walk edges has all its edges counted.** -/
theorem counted_of_wt {M : Model} {s m : ℕ} (hs : s < M.W.n) (hm : 0 < m) (hmn : m < M.W.n)
    (hwt : M.arcWt (s : ℝ) ((ztbnl % M.W.n : ℕ) : ℝ) = m) :
    ∀ d, d < m → M.counted ztxys := by
  classical
  zugys
  set S : Set ℕ := {p | p < n ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    sideInArc (s : ℝ) ((ztbnl % n : ℕ) : ℝ) ztk} with hS
  set T : Set ℕ := {p | p < n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    sideInArc (s : ℝ) ((ztbnl % n : ℕ) : ℝ) ztk} with hT
  have hSe : S = ztywb '' Set.Iio m := by
    zufj
    simp only [hS, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨hp, h⟩
      obtain ⟨d, hd, e⟩ := (piece_edges hs hm hmn hp).1 h
      tauto
    · rintro ⟨d, hd, rfl⟩
      exact ⟨Nat.mod_lt _ by_omega, (piece_edges hs hm hmn ztcv).2 ⟨d, hd, rfl⟩⟩
  have hinj : Set.InjOn ztywb (Set.Iio m) := by
    zuvc
    zucez

    zuct
    zubxx
    · have := Nat.ModEq.add_left_cancel' s hxy
      have h2 := (Nat.modEq_iff_dvd' h.le).1 this
      zuicw
      zubhv
      · omega
      grind
    · have := Nat.ModEq.add_left_cancel' s hxy
      have h2 := (Nat.modEq_iff_dvd' h.le).1 this.symm
      zuicw
      zubhv
      · omega
      grind
  have hcS : S.ncard = m := by
    rw [hSe, hinj.ncard_image, Set.ncard_eq_toFinset_card' , Set.toFinset_Iio]
    simp
  have hTS : T ⊆ S := fun p hp => ⟨hp.1, hp.2.2⟩
  have hSf : S.Finite := by rw [hSe]; exact (Set.finite_Iio m).image _
  have hcT : T.ncard = m := hwt
  have hTeq : ztscn := Set.eq_of_subset_of_ncard_le hTS by_omega hSf
  zuip
  have hmem : ztbuf % n ∈ S := by_grind
  rw [← hTeq] at hmem
  exact hmem.2.1

/-- A point of a counted walk edge of a chain model lies on the chain. -/
theorem counted_pt_mem (C : Chain) {p : ℕ} (hp : (chainModel C).counted p) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) :
    Geometry.lerp ztdrr
      ztbakk t ∈ C.set := by
  obtain ⟨h6, hp'⟩ := hp
  zubgg
  rw [hn, Nat.mod_eq_of_lt by_omega]
  zukkp
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := p - 6) (t := t) by_omega
      ztpbm h0 h1
    rw [show p - 6 + 6 = p by omega] at this
    unfold Chazelle.Chain.sidePt at this
    rwa [C.sideWalk_n, Nat.mod_eq_of_lt by_omega] at this
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := p + 1 - 6) (t := 0) by_omega
      ztdnl le_rfl one_pos
    rw [show p + 1 - 6 + 6 = p + 1 by omega, Chazelle.Chain.sidePt_zero] at this
    have e : Geometry.lerp ztdrr ((chainModel C).W.vtx ztr) 1 =
        (chainModel C).W.vtx ztr := by
      simp
    zudtv

/-- **The chain of a piece over counted edges of a chain model lies on the model's chain.** -/
theorem piece_set_sub {C Cα : Chain} {s : ℕ}
    (hdir : (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ztxlp = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m →
        (chainModel C).W.vtx ztxlp = Cα.vertex ztclf))
    (hc : ∀ d, d < Cα.m → (chainModel C).counted ztxlp) :
    Cα.set ⊆ C.set := by
  set n := (chainModel C).W.n
  have hsucc : ∀ d, (ztbuf % n + 1) % n = (s + ztet) % n := fun d => by
    grind
  zuh
  obtain ⟨k, hk, hx⟩ := hx
  zugbv
  obtain ⟨t, t0, t1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  zufzv
  · have := counted_pt_mem C (hc k hk) t0 t1
    grind
  · have := counted_pt_mem C (hc ztpwy by_omega) (t := 1 - t) by_linarith
      by_linarith
    rw [hsucc, hd _ by_omega, hd _ by_omega, show Cα.m - ztpwy = k + 1 by omega,
      show Cα.m - (Cα.m - k - 1 + 1) = k by omega] at this
    have e : Geometry.lerp ztzbo ztpwz ztca =
        Geometry.lerp ztpwz ztzbo t := by
      simp only [Geometry.lerp, Prod.mk.injEq]; grind
    simp_all
open DownHost ArcT

/-- The walk edges meeting the open cyclic key interval `(a, b)`. -/
def MeetsArc (M : Model) (a b : ℝ) (p : ℕ) : Prop :=
  p < M.W.n ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk
theorem wrapK_bounds {n x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * n) :
    0 ≤ wrapK n x ∧ wrapK n x < n := by
  zujrg
theorem unwrapK_wrapK {n l x : ℝ} (_hl : 0 ≤ l ∧ l < n) (h0 : l ≤ x) (h1 : x < l + n) :
    unwrapK n l ztojx = x := by
  unfold wrapK unwrapK
  grind
variable {M : Model} {Q : Polygon} {n0 : ℕ}
/-- **An edge of the unwrapped interval `[⌊a⌋, P)` meets the interval `(a, b)`.** -/
theorem meets_of_unwrapped {a b : ℝ} (ha : 0 ≤ a ∧ a < M.W.n)
    (hb : 0 ≤ b ∧ b < M.W.n) (hab : a < unwrapK M.W.n a b) {j : ℕ} (hja : (j : ℝ) + 1 > a)
    (hjb : (j : ℝ) + 1 ≤ unwrapK M.W.n a b) (_hjn : (j : ℝ) < a + M.W.n) :
    MeetsArc M a b (j % M.W.n) := by
  zugys
  have hn : ztpgh := by_grind
  have hnN : ztcka := by_simp_all
  set y : ℝ := (max a j + ztl) / 2 with hy
  have hy1 : a < y := by
    grind
  have hy2 : (j : ℝ) < y := by
    grind
  have hy3 : y < j + 1 := by
    grind
  have hub := (unwrapK_bounds ha hb).2
  -- the wrapped point
  have hyb : 0 ≤ y ∧ y < 2 * n := ⟨by_grind, by_linarith⟩
  have hw := wrapK_bounds hyb.1 hyb.2
  have huw : unwrapK n a ztojy = y := unwrapK_wrapK ha hy1.le by_linarith
  have hin : sideInArc a b ztojy :=
    (cyc_unwrap ha ha hb hw ztcmh).2
      ⟨by rw [unwrapK_self, huw]; omega, by_grind⟩
  refine ⟨Nat.mod_lt _ hnN, y - j, by_linarith, by_linarith, ?_⟩
  have e : ((j % n : ℕ) : ℝ) + (y - j) = wrapK n y := by
    zuiqh
    by_cases hj : j < n
    · rw [Nat.mod_eq_of_lt hj]
      have : y < n := by
        have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
        linarith
      simp_all
    · have hj2 : j - n < n := by
        have : (j : ℝ) < 2 * n := by_linarith
        have : j < 2 * n := by exact_mod_cast this
        omega
      rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt hj2]
      have : ¬ y < n := by
        have : (n : ℝ) ≤ j := by_simp_all
        linarith
      rw [ite_eq_right this, Nat.cast_sub by_omega]; ring
  simp_all

/-- **The walk vertices of a light closed key interval** are within `9` steps of its start edge. -/
theorem light_cover
    (hunc : {p | p < M.W.n ∧ ¬ M.counted p}.ncard ≤ 7) {s e : WPos}
    (hs : ProperPos M Q n0 s) (hse : s.edge < M.W.n) (hke : 0 ≤ M.key Q e ∧ M.key Q e < M.W.n)
    (hne : M.key Q s ≠ M.key Q e) (hwt : M.arcWt ztenf ztfoc ≤ 1) {p : ℕ}
    (hp : p < M.W.n) (hx : ClosedArc ztenf ztfoc p) :
    ∃ t, t < 10 ∧ zttzq % M.W.n = p := by
  zubbm

  have ha : ztgaf := by
    zudxp

  have hab : ztlak := by
    have := unwrapK_bounds ha hke
    unfold unwrapK at *
    zuhqh
    · grind
    grind
  zudzm
  -- the unwrapped vertex

  have hPb : ztlxl := by
    zuebu
    · have := (cyc_unwrap ha ha hke hpn ztcmh).1 hx
      zuimu
    · zuguq
    grind
  -- `P` is the natural `p` or `p + n`
  obtain ⟨Pn, hPn, hPmod⟩ : ztgqg := by
    zuijh

    · exact ztiok
    · exact ztdqt
  have hsP : s.edge ≤ Pn := by
    zudmt
    zufc
  zudla

  have htn : t ≤ n := by
    zucfx

  -- the `t` edges before the vertex meet the interval
  have hmeet : ztfxe := fun d hd =>
    meets_of_unwrapped ha hke hab
      (by have : ztgts := by_simp
          zuntj)
      (by have : ztcft := by exact_mod_cast by_omega
          grind)
      (by have : ztcft := by exact_mod_cast by_omega
          grind)
  -- counting
  zufpb
  have hinj : Set.InjOn ztdcy ztvdd := by
    zuvc
    zucez

    zubvm

    · zueul
      zubhv
      · omega
      grind
    · zudes
      zubhv
      · omega
      grind
  have hcS : S.ncard = t := by
    zugdj

  zufty
  have h1 : (S ∩ {p | M.counted p}).ncard ≤ 1 := by
    zumjg
    · zuzs
      zudem

    · zucvd
  have h2 : (S \ {p | M.counted p}).ncard ≤ 7 := by
    zumjf
    · zuzs
      exact ztrae
    · zucvd
  zufft
  refine ztreq
  zuedh

/-- **The steps from the start edge to a walk vertex of a closed key interval** are at most its
weight plus the uncounted edges. -/
theorem steps_le
    {w u : ℕ} (hunc : {p | p < M.W.n ∧ ¬ M.counted p}.ncard ≤ u) {s e : WPos}
    (hs : ProperPos M Q n0 s) (hse : s.edge < M.W.n) (hke : 0 ≤ M.key Q e ∧ M.key Q e < M.W.n)
    (hne : M.key Q s ≠ M.key Q e) (hwt : M.arcWt ztenf ztfoc ≤ w) {p : ℕ}
    (hp : p < M.W.n) (hx : ClosedArc ztenf ztfoc p) :
    ∃ t, t ≤ w + u ∧ zttzq % M.W.n = p ∧
      ((s.edge + t : ℕ) : ℝ) = unwrapK M.W.n ztenf p := by
  zubbm

  have ha : ztgaf := by
    zudxp

  have hab : ztlak := by
    have := unwrapK_bounds ha hke
    unfold unwrapK at *
    zuhqh
    · grind
    grind
  zudzm
  -- the unwrapped vertex

  have hPb : ztlxl := by
    zuebu
    · have := (cyc_unwrap ha ha hke hpn ztcmh).1 hx
      zuimu
    · zuguq
    grind
  -- `P` is the natural `p` or `p + n`
  obtain ⟨Pn, hPn, hPmod⟩ : ztgqg := by
    zuijh

    · exact ztiok
    · exact ztdqt
  have hsP : s.edge ≤ Pn := by
    zudmt
    zufc
  zudla

  have htn : t ≤ n := by
    zucfx

  -- the `t` edges before the vertex meet the interval
  have hmeet : ztfxe := fun d hd =>
    meets_of_unwrapped ha hke hab
      (by have : ztgts := by_simp
          zuntj)
      (by have : ztcft := by exact_mod_cast by_omega
          grind)
      (by have : ztcft := by exact_mod_cast by_omega
          grind)
  -- counting
  zufpb
  have hinj : Set.InjOn ztdcy ztvdd := by
    zuvc
    zucez

    zubvm

    · zueul
      zubhv
      · omega
      grind
    · zudes
      zubhv
      · omega
      grind
  have hcS : S.ncard = t := by
    zugdj

  zufty
  have h1 : (S ∩ {p | M.counted p}).ncard ≤ w := by
    zumjg
    · zuzs
      zudem

    · zucvd
  have h2 : (S \ {p | M.counted p}).ncard ≤ u := by
    zumjf
    · zuzs
      exact ztrae
    · zucvd
  zufft
  refine ⟨t, by_omega, ?_, ?_⟩
  · zuedh
  · rw [htdef, show s.edge + ztnnw = Pn by omega, hPn]
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sideInArc)
open DownHost ArcT

/-! ## The arcs of a region of a normal form -/
variable {M : Model} {Q : Polygon}
/-- **A region of a normal form has at most `D + 1` arcs** if its degree is at most `D`. -/
theorem region_arcs_le {N : NF} (hM : WalkAx M) (hNF : IsNF M Q N)
    {D : ℕ} (hD : M.DegLe ztdu D) {r : ℕ} (hr : r < N.nRegions) :
    (N.region r).arcs.length ≤ D + 1 := by
  classical
  obtain ⟨hFam, -, -, reg, hRC, -, hArcs, hRg, -, -, -⟩ := hNF
  zufud
  set l := (N.region r).arcs
  have hnd : l.Nodup := (hRg r hr).2.2.1
  zufaj
  have hinj : Set.InjOn f (↑l.toFinset : Set ℕ) := by
    zukjm
    zulkg
    have hj' := List.mem_toFinset.1 hj'
    zueba
    obtain ⟨hjl', hjr'⟩ := (hArcs.2.2.2 r hr j').1 hj'
    exact hArcs.2.1 j j' hjl hjl' by_omega ztnxe
  have hsub : f '' (↑l.toFinset : Set ℕ) ⊆ {ab : ℝ × ℝ | M.IsArc ztdu ztcz ab.1 ab.2} := by
    rintro _ ⟨j, hj, rfl⟩
    zulkg
    zueba
    have := (hArcs.1 j hjl).2
    grind
  obtain ⟨hfin, hcard⟩ := hM.arcs_bound hFam.2.1 hFam.1 hU
  have hl : l.length = (↑l.toFinset : Set ℕ).ncard := by
    zuewx
  calc l.length = (f '' (↑l.toFinset : Set ℕ)).ncard := by rw [hinj.ncard_image, hl]
    _ ≤ {ab : ℝ × ℝ | M.IsArc ztdu ztcz ab.1 ab.2}.ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ M.deg ztdu ztcz + 1 := hcard
    _ ≤ D + 1 := by have := hD _ hU; omega

/-! ## The tiling of an arc by its pieces -/
variable {E : FEnv} {c₀ : Config}

/-- The key of the start of piece `i` of the list at `L` in memory `m`. -/
noncomputable def psK (E : FEnv) (m : ℕ → ℕ) (L i : ℕ) : ℝ :=
  E.M.key zti ⟨m ztfnw, m ztdla⟩

/-- The key of the end of piece `i`. -/
noncomputable def peK (E : FEnv) (m : ℕ → ℕ) (L i : ℕ) : ℝ :=
  E.M.key zti ⟨m ztclq, m ztdlb⟩
theorem key_bounds {n : ℕ} {x : WPos} (hx : ProperPos M Q n x)
    (he : x.edge < M.W.n) : 0 ≤ M.key Q x ∧ M.key Q x < M.W.n := by
  zuxf

/-- The arc `t` of the region is an arc of every region map of the normal form. -/
theorem arc_isArc (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) {t : ℕ} (ht : t < (E.N.region E.r).arcs.length) :
    E.M.IsArc ztwky ztbuw ztxdo
      ztxdn := by
  zucdm
  zucmm
  zufpf
  have hjm : ztizw := by
    simp_all
  obtain ⟨hj, hjr⟩ := (hArcs.2.2.2 E.r hr j).1 hjm
  have := (hArcs.1 j hj).2
  rw [hjr] at this
  tauto

/-- The ends of an arc of a region with an exit chord differ. -/
theorem arc_ne (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) :
    E.M.key zti (arcOf E.N E.r t).s ≠ E.M.key zti (arcOf E.N E.r t).e := by
  zuhhy
  obtain ⟨-, -, -, -, hc, -⟩ := arc_isArc hE hregs ht
  rcases hc with ⟨-, -, h⟩ | ⟨hF, -, -⟩
  · zubh
  · exfalso
    zucmm
    zufig
    zult

    have hmem : ztpjg := by
      zubsu

    have : (E.N.chord i).toSet E.M zti ∈ E.N.F E.M zti := ⟨E.N.chord i, hmem, rfl⟩
    simp_all

/-- **The pieces of the cut of arc `t` tile it.** -/
theorem tile_of_cut (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) {m : ℕ → ℕ} {A L : ℕ}
    (hcp : CutPost E ztybb
      ztyba m A L) :
    Tile E.M.W.n ztxdo ztxdn
      (m L) (psK E m L) (peK E m L) := by
  zuhhy
  obtain ⟨ha0, ha1, hb0, hb1, -, -⟩ := arc_isArc hE hregs ht
  zujyz
  obtain ⟨-, -, hq1, hk0, hkq, hcons, hin, -, -, hpos, -⟩ := hcp
  have ku := (normOf_facts hAi.sp).2.2.2.1
  have kv := (normOf_facts hAi.ep).2.2.2.1
  refine ⟨ztugy, ztuhc, arc_ne hE hch ht, hq1, fun i hi => ?_, fun i hi => ?_,
    ?_, ?_, fun i hi => hcons i hi, fun i hi => ?_⟩
  · obtain ⟨h1, -, h3, -⟩ := hpos i hi
    exact key_bounds h1 h3
  · obtain ⟨-, h2, -, h4⟩ := hpos i hi
    exact key_bounds h2 h4
  · exact hk0.trans ku
  · exact hkq.trans kv
  · have e1 : E.M.key zti ⟨(normOf E.M zti (arcOf E.N E.r t).e).edge,
        (normOf E.M zti (arcOf E.N E.r t).e).hgt⟩ = E.M.key (Qof E.P) (arcOf E.N E.r t).e := kv
    have := hin i hi
    dsimp only at this
    zvmxy at this
    tauto

/-- **A piece weighs at most its arc.** -/
theorem piece_wt_le {n a b : ℝ} {q : ℕ} {s e : ℕ → ℝ} {M : Model} (hn : n = M.W.n)
    (h : Tile n a b q s e) {i : ℕ} (hi : i < q) : M.arcWt ztciy ztfhe ≤ M.arcWt a b := by
  refine Set.ncard_le_ncard (fun p hp => ?_) ((Set.finite_Iio M.W.n).subset fun x hx => hx.1)
  obtain ⟨hp, hc, τ, h0, h1, hin⟩ := hp
  zucgv
  exact ⟨hp, hc, τ, h0, h1, tile_inner h hi ⟨by_positivity, by_grind⟩ hin⟩

/-! ## A kind-1 piece -/
theorem arcWt_le_size (M : Model) (a b : ℝ) : M.arcWt a b ≤ M.size :=
  Set.ncard_le_ncard (fun _ hp => ⟨hp.1, hp.2.1⟩) ((Set.finite_Iio M.W.n).subset fun _ hx => hx.1)
theorem qof_simple (hE : FGood E c₀) : (Qof E.P).Simple :=
  (shearInvariance ztmjb E.P).1 hE.hG.1

/-- **The facts of a kind-1 piece**, from the cutter's contract. -/
theorem k1hyp_of (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) {c' : Config} (hI' : FInv E.W c₀ c') {L : ℕ}
    (hcp : CutPost E ztybb
      ztyba c'.nmem ztdo L)
    {i : ℕ} (hi : i < c'.nmem L) (hk : c'.nmem ztdpb = 1) :
    ∃ Hs Cα N γ', K1Hyp ztpxn c' ztcas Hs Cα N γ' ∧ γ' ≤ E.H E.γ ∧ Cα.m ≤ E.γ := by
  have hT := tile_of_cut hE hch ht hcp
  zujyz
  zuixp
  obtain ⟨hLq, -, -, -, -, -, -, -, hk1w, hpos, -⟩ := hcp'
  obtain ⟨hwf, Hs, Cα, N, hCD, hNW, ⟨γ', hγ', hcan⟩, -, hwt, hPW, hQ, hdir⟩ := hk1w i hi hk
  obtain ⟨-, -, hs, -⟩ := hpos i hi
  obtain ⟨h0, h3, -, he, -⟩ := hPW
  zumct
  zudwh
  zunx
  have hmP : Cα.m < E.P.n := by have := Cα.m_lt; rw [hQ, hQn] at this; omega
  zumpi
  set s := c'.nmem ztfnw
  -- the weight of the piece
  have hwt' : E.M.arcWt (s : ℝ) ((ztohi % n : ℕ) : ℝ) = Cα.m := by
    have e1 : E.M.key zti ⟨c'.nmem ztfnw, c'.nmem ztdla⟩ = s := by
      simp only at h0; zvmzn; exact key_vtx' _ _ _
    have e2 : E.M.key zti ⟨c'.nmem ztclq, c'.nmem ztdlb⟩ =
        ((ztohi % n : ℕ) : ℝ) := by
      simp only at h3 he; rw [h3, he]; exact key_vtx' _ _ _
    have := hwt
    zugzu
    zvmws at this
    omega
  have hmn : Cα.m < n := by
    zubcv
    · have h1 := arcWt_le_size E.M (s : ℝ) ((ztohi % n : ℕ) : ℝ)
      rw [hwt'] at h1
      have h2 : E.M.size = 2 * C.m := by zvmzx; exact MergeAsm.chainModel_size C
      have h3 : ztppf := by show E.M.W.n = _; zvmzx; exact chainModel_n C
      omega
    · have : n = E.P.n := by
        show E.M.W.n = _; zvmzx; show (interiorWalk zti).n = _; zunqd
      omega
  zumea
  -- the piece's chain lies on the model's chain
  have hsub : ∀ C : Chain, E.M = chainModel C → Cα.set ⊆ C.set := fun C hM => by
    have hc := counted_of_wt (M := E.M) hs by_omega hmn hwt'
    zumdj
    have hn' : n = (chainModel C).W.n := by rw [← hM]
    rw [hn'] at hdir'
    zvmzx at hc hdir'
    zulzl
  -- the weight bound
  have hwγ : Cα.m ≤ E.γ := by
    have h1 := piece_wt_le rfl hT hi
    have h2 : E.M.arcWt (psK E c'.nmem L i) (peK E c'.nmem L i) = Cα.m := hwt
    have h3 := hAi.wt
    omega
  -- the walk model of the piece's chain
  have hGα : GoodModel ztbdc := Or.inl ⟨Cα, by zvnao; exact qof_simple hE, rfl⟩
  zuhel
  obtain ⟨hB7, hcb, -, -, -, -⟩ := nf_bounds hNW
  have hAW : c'.nreg ALLOC ≤ E.W := hI'.hw.1 ALLOC
  refine ⟨Hs, Cα, N, γ', ⟨?_, hCD, hwf, hNW, hcan, hQ, hdir, hs, hmn, fun C hM => ?_, ?_, ?_, ?_⟩,
    hγ', hwγ⟩
  · show L + 1 + 7 * i + 6 < _
    omega
  · have hv : E.M.pos zti ztujj = E.M.W.vtx s := by
      rw [pos_eq_sidePt, param_vtx, Chazelle.Chain.sidePt_zero]
    show E.M.pos zti ztujj ∈ C.set
    zueyk
    have hs0 : zttzc % n = s := by rw [Nat.add_zero, Nat.mod_eq_of_lt hs]
    zufzv
    · rw [← hs0, hu 0 ztbg]; exact hsub C hM (Cα.vertex_mem_set ztbg)
    · rw [← hs0, hd 0 ztbg]; exact hsub C hM (Cα.vertex_mem_set ztjkm)
  · show 2 * ztgb ≤ E.W
    omega
  · zuz
    have := region_arcs_le hMα hcan.1 hcan.2.1 hr
    show 2 * ztgb + _ ≤ E.W
    omega
  · show 4 * Nat.clog 2 zthbn + 1 + 1 ≤ E.W
    have hcl : Nat.clog 2 zthbn ≤ N.nChords :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self
    rcases Nat.lt_or_ge N.nChords 2 with h | h
    · omega
    · have := hcb (N.nChords - 1) by_omega
      omega

/-- **Every piece of the cut of an arc is good** for a piece bound `Kp` dominating the handlers. -/
theorem pgood_of (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) {Kp : ℕ} (hk0 : k0K E ≤ Kp)
    (hk1 : ∀ (Cα : Chain) (N : NF) (γ' : ℕ), Cα.P = Qof E.P →
      IsCanonicalNF ztbdc zti N γ' 4 → γ' ≤ E.H E.γ → Cα.m ≤ E.γ →
      k1K E Cα N ≤ Kp) :
    PGood E c₀ Kp t := by
  intro c' hI' hcp i hi
  zuixp
  obtain ⟨hLq, -, -, -, -, -, -, -, -, hpos, -⟩ := hcp'
  refine ⟨by show c'.nreg 81076 + 1 + 7 * i + 6 < _; omega, (hpos i hi).2.2.1, hk0, fun hk => ?_⟩
  obtain ⟨Hs, Cα, N, γ', hK, hγ', hm⟩ := k1hyp_of hE hch ht hI' hcp hi hk
  exact ⟨Hs, Cα, N, γ', hK, hk1 Cα N γ' hK.hQ hK.hcan hγ' hm⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sideInArc SideAttach sidePt)
open DownHost ArcT
variable {E : FEnv} {c₀ : Config}

/-- **An arc of the region is an arc record of its list.** -/
theorem arc_index (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) {a b : ℝ}
    (h : E.M.IsArc ztwky ztbuw a b) :
    ∃ t, t < (E.N.region E.r).arcs.length ∧ E.M.key zti (arcOf E.N E.r t).s = a ∧
      E.M.key zti (arcOf E.N E.r t).e = b := by
  zucdm
  zucmm
  obtain ⟨j, hj, hjr, hs, he⟩ := hArcs.2.2.1 E.r hr a b h
  have hjm : ztizw := (hArcs.2.2.2 E.r hr j).2 zthnb
  zufzc
  refine ⟨t, ht, ?_, ?_⟩ <;>
  · unfold arcOf
    simp_all

/-- **Closed cyclic intervals unwrapped.** -/
theorem closedArc_unwrap {n a b x : ℝ} (ha : 0 ≤ a ∧ a < n) (hb : 0 ≤ b ∧ b < n)
    (hx : 0 ≤ x ∧ x < n) (hab : a ≠ b) :
    ClosedArc a b x ↔ a ≤ unwrapK n a x ∧ unwrapK n a x ≤ unwrapK n a b := by
  have hub : ztlak := by
    have := unwrapK_bounds ha hb
    unfold unwrapK at *
    grind
  have hc := cyc_unwrap ha ha hb hx ztcmh
  rw [unwrapK_self] at hc
  constructor
  · rintro (h | rfl | rfl)
    · grind
    · rw [unwrapK_self]; grind
    grind
  · zubf
    zuff
    · zudt
      · tauto
      · zulw
        zudxs
        have e2 := wrapK_unwrapK (n := n) (l := a) hb
        simp_all
    · zuhl
      zudxs
      rw [← h1, wrapK] at e1
      grind

/-- **Two distinct keys of one closed arc fail the count test.** -/
theorem not_countOK_same_arc {M : Model} {S : Set ztf} {R : Set Point} {a b x y : ℝ}
    (hA : M.IsArc S R a b) (hab : a ≠ b) (hx : 0 ≤ x ∧ x < M.W.n) (hy : 0 ≤ y ∧ y < M.W.n)
    (hxy : x ≠ y) (hxA : ClosedArc a b x) (hyA : ClosedArc a b y) : ¬ CountOK M S R x y := by
  obtain ⟨ha0, ha1, hb0, hb1, -, hnc, -⟩ := hA
  have ha : 0 ≤ a ∧ a < (M.W.n : ℝ) := ztugy
  have hb : 0 ≤ b ∧ b < (M.W.n : ℝ) := ztuhc
  obtain ⟨x1, x2⟩ := (closedArc_unwrap ha hb hx hab).1 hxA
  obtain ⟨y1, y2⟩ := (closedArc_unwrap ha hb hy hab).1 hyA
  have hux : unwrapK M.W.n a x ≠ unwrapK M.W.n a y := by
    intro h; apply hxy
    rw [← wrapK_unwrapK (n := (M.W.n : ℝ)) (l := a) hx, h, wrapK_unwrapK hy]
  -- the keys strictly between the two keys (upwards from the lower) are inside the arc
  have hempty : ∀ k₁ k₂ : ℝ, (0 ≤ k₁ ∧ k₁ < M.W.n) → (0 ≤ k₂ ∧ k₂ < M.W.n) →
      a ≤ unwrapK M.W.n a k₁ → unwrapK M.W.n a k₁ < unwrapK M.W.n a k₂ →
      unwrapK M.W.n a k₂ ≤ unwrapK M.W.n a b → (sideExits M S R k₁ k₂).ncard = 0 := by
    intro k₁ k₂ hk₁ hk₂ h1 h2 h3
    suffices hE0 : sideExits M S R k₁ k₂ = ∅ by rw [hE0, Set.ncard_empty]
    zubcj
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hc, p, t, hat, hin⟩
    have hpt : 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < M.W.n := by
      obtain ⟨hp, ht0, ht1, -⟩ := hat
      have : ztbou := by exact_mod_cast hp
      grind
    have hk := (cyc_unwrap ha hk₁ hk₂ hpt h2).1 hin
    have hub : a < unwrapK M.W.n a b := by_linarith
    have : sideInArc a b ztdj :=
      (cyc_unwrap ha ha hb hpt ztcmh).2
        ⟨by rw [unwrapK_self]; grind, by_grind⟩
    exact hnc _ this ztkjs
  rintro ⟨c1, c2⟩
  grind

/-! ## The setup of completeness -/

/-- The key of the start of arc `t` of the region. -/
noncomputable def aK (E : FEnv) (t : ℕ) : ℝ := E.M.key zti (arcOf E.N E.r t).s

/-- The key of the end of arc `t` of the region. -/
noncomputable def bK (E : FEnv) (t : ℕ) : ℝ := E.M.key zti (arcOf E.N E.r t).e

/-- **The good chord of a region with too many exits**, its attachments and their arcs. -/
structure GoodSet (E : FEnv) (reg : ℕ → Set Point) (X : WPos) (σ T : ℝ) (po : ℕ) (tq : ℝ)
    (ti tj : ℕ) : Prop where
  hch : (E.N.region E.r).chords ≠ []
  hgc : GoodCand E.M zti ztwky ztbuw X σ T
  hXA : SideAttach E.M.W ztyiv X.edge 0
  hOA : SideAttach E.M.W ztyiv po tq
  hne : sidePt E.M.W X.edge 0 ≠ sidePt E.M.W po tq
  hVX : VSet E X.edge
  hti : ti < (E.N.region E.r).arcs.length
  htj : tj < (E.N.region E.r).arcs.length
  hXi : ClosedArc (aK E ti) (bK E ti) ztgvr
  hXj : ClosedArc (aK E tj) (bK E tj) ztdek
  hij : aK E ti ≠ aK E tj
  hcnt : CountOK E.M ztwky ztbuw ztgvr ztdek
theorem key_attach_ne {W : Polygon} {p p' : ℕ} {t t' : ℝ} (ht : 0 ≤ t ∧ t < 1) (ht' : 0 ≤ t' ∧ t' < 1)
    (hne : sidePt W p t ≠ sidePt W p' t') : (p : ℝ) + t ≠ p' + t' := by
  zuq
  have hp : p = p' := by
    zubnl

    omega
  simp_all

/-- **The setup of completeness.** -/
theorem good_set (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) (hfull : E.M.FullDegLe zti E.D)
    (hdeg : E.D < E.M.deg ztwky ztbuw) :
    ∃ X σ T po tq ti tj, GoodSet E reg X σ T po tq ti tj := by
  zuclv
  obtain ⟨hFam, -, -, -⟩ := hE.hNF
  have hregs' := hregs
  obtain ⟨hRC, -, hArcs, hRg⟩ := hregs'
  zucmm
  have hU := hRC.1 E.r hr
  set S := E.N.F E.M zti
  -- the region has an exit chord
  have hch : ztfdm := by
    zubww
    have : E.M.deg S ztbuw = 0 := by
      zuhqm
      rw [Set.ncard_eq_zero (hs := (hFam.1.subset fun c hc => hc.1))]
      zubcj
      zughe
      rintro ⟨r', hr', rfl⟩ htc
      obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.1 hr'
      have hci : E.N.chord i = r' := by
        zuub
      have := ((hRg E.r hr).1 i).2 ⟨hi, by_simp_all⟩
      simp_all
    omega
  have hne : S.Nonempty := by
    zult

    have hmem : ztpjg := by
      zubsu

    exact ztmqb
  -- the good chord
  obtain ⟨X, σ, T, hgc, hXA, ⟨po, tq, hOA, hne'⟩, p, hpr, hpos⟩ :=
    exists_good' hE.hGM hfull hFam hU hdeg
  obtain ⟨hX0, hXe, hσ, hT, -, -, -, hadm, hsw⟩ := id hgc
  obtain ⟨heS, heR, -⟩ := hsw
  set ex := chordOf (E.M.pos zti X) σ T
  obtain ⟨a₁, b₁, hA₁, hX₁⟩ := attach_closedArc hM hFam.2.1 hFam.1 hne hU hadm heS heR hXA
  obtain ⟨a₂, b₂, hA₂, hX₂⟩ := attach_closedArc hM hFam.2.1 hFam.1 hne hU hadm heS heR hOA
  obtain ⟨ti, hti, hai, hbi⟩ := arc_index hE hregs hA₁
  obtain ⟨tj, htj, haj, hbj⟩ := arc_index hE hregs hA₂
  have hcnt := counts_of_splitsWell hM hFam.2.1 hFam.1 hU hadm hXA hOA hne' hgc.2.2.2.2.2.2.2.2
  have hXk : ztgad := by
    simp_all
  have hOk : 0 ≤ (po : ℝ) + tq ∧ (po : ℝ) + tq < E.M.W.n := by
    obtain ⟨hp, ht0, ht1, -⟩ := hOA
    have : (po : ℝ) + 1 ≤ E.M.W.n := by exact_mod_cast hp
    grind
  have hkne : (X.edge : ℝ) + 0 ≠ (po : ℝ) + tq :=
    key_attach_ne ztuiz ⟨hOA.2.1, hOA.2.2.1⟩ hne'
  refine ⟨X, σ, T, po, tq, ti, tj, ⟨hch, hgc, hXA, hOA, hne', fun C hC => ?_, hti, htj,
    by unfold aK bK; simp_all, by unfold aK bK; simp_all, ?_,
    hcnt⟩⟩
  · have hXX : ztplj := by cases X; simp_all
    have h1 := hpr C hC
    rw [← hXX, hpos]
    have h2 := chain_vtx_mem C zti h1.1 h1.2
    rw [← hC, pos_eq_sidePt, param_vtx, Chazelle.Chain.sidePt_zero] at h2
    zucvi
  · intro hab
    unfold aK at hab
    rw [hai, haj] at hab
    zumqb
    -- the two arcs are one record
    have hr' : ztkzx := hr
    have mem : ∀ t, t < (E.N.region E.r).arcs.length →
        (E.N.region E.r).arcs.getD t 0 < E.N.arcs.length ∧
          (E.N.arc ((E.N.region E.r).arcs.getD t 0)).reg = E.r := fun t ht => by
      apply (hArcs.2.2.2 E.r hr' _).1
      simp_all
    obtain ⟨m1, r1⟩ := mem ti hti
    obtain ⟨m2, r2⟩ := mem tj htj
    have hjj := hArcs.2.1 _ _ m1 m2 by_omega (by
      have e1 := hai; have e2 := haj; unfold arcOf at e1 e2; simp_all)
    have hb : b₁ = b₂ := by rw [← hbi, ← hbj]; unfold arcOf; rw [hjj]
    zulsy
    exact not_countOK_same_arc hA₁ (by rw [← hai, ← hbi]; exact arc_ne hE hch hti) hXk hOk
      hkne hX₁ hX₂ hcnt
