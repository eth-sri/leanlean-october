module

public import Chazelle.Core.RestoreFDesc
public import Chazelle.Core.RestorePieceMath

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
    (hCD : ChainDescAt c₀.nmem (c₀.nmem (c.nreg 81080 + 5)) (Qof E.P) Hs Cα)
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c₀.nmem (c.nreg 81080 + 5))) :
    FRS B E.P E.W c₀ (Stmt.block k1L) c 13 (fun c' =>
      c'.nreg 81089 = c₀.nmem (c.nreg 81080) ∧
      c'.nreg 81133 = c₀.nmem (c.nreg 81080 + 5) ∧ c'.nreg 81134 = c₀.nmem (c.nreg 81080 + 6) ∧
      c'.nreg 81082 = Cα.s ∧ c'.nreg 81081 = Cα.m ∧ c'.nreg 81083 = Cα.topIdx ∧
      (c'.nreg 81084 = 1 ↔ Cα.sideBeta = true) ∧
      ∀ q, q ≠ 81081 → q ≠ 81082 → q ≠ 81083 → q ≠ 81084 → q ≠ 81089 → q ≠ 81090 →
        q ≠ 81133 → q ≠ 81134 → c'.nreg q = c.nreg q) := by
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := fun a ha => hI.hm a ha
  have hD5 := hwf.1
  have k5 : c.nreg 81015 = 5 := by rw [hI.hin _ (by unfold FFix; omega), hE.k5]
  have k1 : c.nreg 81012 = 1 := by rw [hI.hin _ (by unfold FFix; omega), hE.k1]
  have m5 : c.nmem (c.nreg 81080 + 5) = c₀.nmem (c.nreg 81080 + 5) := hm _ (by omega)
  have ea : ∀ j, j ≤ 4 → c.nmem (c₀.nmem (c.nreg 81080 + 5) + j) =
      c₀.nmem (c₀.nmem (c.nreg 81080 + 5) + j) := fun j hj => hm _ (by omega)
  have ok : okB E.W c.nmem k1L c.nreg := by
    simp only [k1L, okB, okI, regI, upd, FScr, FOut, k5, k1]
    norm_num
    rw [m5]
    (repeat' apply And.intro) <;> omega
  refine (FRS.block hB _ hI ok).mono (by simp [k1L]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem k1L c.nreg q := fun q => by rw [h']
  obtain ⟨-, -, h1, h2, h3, h4⟩ := hCD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q a1 a2 a3 a4 a5 a6 a7 a8 => ?_⟩
  · rw [e']; simp [k1L, regB, regI, upd]; exact hm _ (by omega)
  · rw [e']; simp [k1L, regB, regI, upd, k5]; exact m5
  · rw [e']; simp [k1L, regB, regI, upd, k5, k1]; exact hm _ (by omega)
  · rw [e']; simp [k1L, regB, regI, upd, k5, k1, m5]; rwa [ea 1 (by omega)]
  · rw [e']; simp [k1L, regB, regI, upd, k5, k1, m5]
    rwa [show c₀.nmem (c.nreg 81080 + 5) + 1 + 1 = c₀.nmem (c.nreg 81080 + 5) + 2 by ring,
      ea 2 (by omega)]
  · rw [e']; simp [k1L, regB, regI, upd, k5, k1, m5]
    rwa [show c₀.nmem (c.nreg 81080 + 5) + 1 + 1 + 1 = c₀.nmem (c.nreg 81080 + 5) + 3 by ring,
      ea 3 (by omega)]
  · rw [e']; simp [k1L, regB, regI, upd, k5, k1, m5]
    rwa [show c₀.nmem (c.nreg 81080 + 5) + 1 + 1 + 1 + 1 = c₀.nmem (c.nreg 81080 + 5) + 4 by ring,
      ea 4 (by omega)]
  · rw [e', regB_other _ _ _ (fun i hi => ?_)]
    simp only [k1L, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> omega

/-- The direction: `J = 0` (`81085`) if the first vertex of the piece is at the height of the
chain's first vertex, else `J = m`. -/
def k1Dir : Stmt :=
  .seq (Stmt.block [.copyN 81060 81089, .constN 81061 0]) (.seq (fHv 81060)
    (.seq (Stmt.block [.copyN 81085 81081]) (ifEq 81062 81082 (Stmt.block [.constN 81085 0]))))

theorem k1Dir_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hs : c.nreg 81089 < E.M.W.n) (hset : VSet E (c.nreg 81089))
    (hroom : c.nreg ALLOC + hvK + 9 ≤ E.W) :
    FRS B E.P E.W c₀ k1Dir c (hvK + 9) (fun c' => ∃ h, h < E.P.n ∧
      ((Qof E.P).vtx h).2 = (E.M.pos (Qof E.P) ⟨c.nreg 81089, 0⟩).2 ∧
      c'.nreg 81085 = (if h = c.nreg 81082 then 0 else c.nreg 81081) ∧
      ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
        q ≠ 81085 → c'.nreg q = c.nreg q) := by
  have ok1 : okB E.W c.nmem [.copyN 81060 81089, .constN 81061 0] c.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₂ := hvK + 7) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
    (by simp; omega) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81060 81089, .constN 81061 0] c.nreg q :=
    fun q => by rw [h₁]
  have v60 : c₁.nreg 81060 = c.nreg 81089 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81060 → q ≠ 81061 → c₁.nreg q = c.nreg q := fun q a b => by
    rw [e₁]; simp [regB, regI, upd, a, b]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  refine FRS.seq (K₂ := 7) (fHv_fs hE hB hI₁ (a := 81060) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rwa [v60]) (by rwa [v60]) (by rw [hA₁']; omega))
    (fun c₂ hI₂ hA₂ ⟨hh, hy, f₂⟩ => ?_)
  rw [v60] at hy
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
      c₂.nreg q = c.nreg q := fun q a b h1 h2 h3 h4 => by rw [f₂ q a b h3 h4, f₁ q h1 h2]
  have ok3 : okB E.W c₂.nmem [.copyN 81085 81081] c₂.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₂ := 5) (FRS.block hB _ hI₂ ok3) (fun c₃ hI₃ hA₃ h₃ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.copyN 81085 81081] c₂.nreg q := fun q => by rw [h₃]
  have v85 : c₃.nreg 81085 = c.nreg 81081 := by
    rw [e₃]; simp [regB, regI, upd]
    exact g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have f₃ : ∀ q, q ≠ 81085 → c₃.nreg q = c₂.nreg q := fun q h => by
    rw [e₃]; simp [regB, regI, upd, h]
  have u62 : c₃.nreg 81062 = c₂.nreg 81062 := f₃ _ (by norm_num)
  have u82 : c₃.nreg 81082 = c.nreg 81082 := by
    rw [f₃ _ (by norm_num), g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  have fin : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
      q ≠ 81085 → c₃.nreg q = c.nreg q := fun q a b h1 h2 h3 h4 h5 => by
    rw [f₃ q h5, g₂ q a b h1 h2 h3 h4]
  by_cases he : c₃.nreg 81062 = c₃.nreg 81082
  · have okz : okB E.W c₃.nmem [.constN 81085 0] c₃.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine FRS.ifEq_eq (K := 1) he ((FRS.block hB _ hI₃ okz).mono (by simp) (fun c' h' => ?_))
    have e' : ∀ q, c'.nreg q = regB c₃.nmem [.constN 81085 0] c₃.nreg q := fun q => by rw [h']
    refine ⟨c₂.nreg 81062, hh, hy, ?_, fun q a b h1 h2 h3 h4 h5 => ?_⟩
    · rw [u62, u82] at he; rw [e', ite_eq_left he]; simp [regB, regI, upd]
    · rw [e']; simp [regB, regI, upd, h5]; exact fin q a b h1 h2 h3 h4 h5
  · refine FRS.ifEq_ne (K := 1) hI₃ he ⟨c₂.nreg 81062, hh, hy, ?_, fin⟩
    rw [v85, ite_eq_right (by rwa [u62, u82] at he)]

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
      c'.nreg 81086 = WalkEmbed.tpos Cα (c.nreg 81085) ∧ c'.nreg 81091 = 2 * Cα.m ∧
      (WalkEmbed.tpos Cα (c.nreg 81085) + Cα.m ≤ 2 * Cα.m →
        c'.nreg 81087 = Cα.m ∧ c'.nreg 81088 = 0) ∧
      (2 * Cα.m < WalkEmbed.tpos Cα (c.nreg 81085) + Cα.m →
        c'.nreg 81087 = 2 * Cα.m - WalkEmbed.tpos Cα (c.nreg 81085) ∧
        c'.nreg 81088 = Cα.m - (2 * Cα.m - WalkEmbed.tpos Cα (c.nreg 81085))) ∧
      ∀ q, q ≠ 81086 → q ≠ 81087 → q ≠ 81088 → q ≠ 81091 → q ≠ 81092 → q ≠ 81093 →
        c'.nreg q = c.nreg q) := by
  have htop := Cα.topIdx_le
  have h1m := Cα.one_le
  have hbS := WalkEmbed.bS_le Cα
  have hbSd : WalkEmbed.bS Cα = if Cα.sideBeta then Cα.topIdx else 2 * Cα.m - Cα.topIdx := rfl
  -- 2m and 2m - top
  have ok1 : okB E.W c.nmem [.addN 81091 81081 81081, .subN 81092 81091 81083] c.nreg := by
    simp only [okB, okI, FScr, FOut, hm]; norm_num; omega
  refine FRS.seq (K₂ := 16) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.addN 81091 81081 81081, .subN 81092 81091 81083]
      c.nreg q := fun q => by rw [h₁]
  have v91 : c₁.nreg 81091 = 2 * Cα.m := by rw [e₁]; simp [regB, regI, upd, hm]; ring
  have v92 : c₁.nreg 81092 = 2 * Cα.m - Cα.topIdx := by
    rw [e₁]; simp [regB, regI, upd, hm, ht]; omega
  have f₁ : ∀ q, q ≠ 81091 → q ≠ 81092 → c₁.nreg q = c.nreg q := fun q a b => by
    rw [e₁]; simp [regB, regI, upd, a, b]
  have k1₁ : c₁.nreg 81012 = 1 := by rw [hI₁.hin _ (by unfold FFix; omega), hE.k1]
  -- bS
  refine FRS.seq (K₁ := 5) (K₂ := 11) (Q₁ := fun c' => c'.nreg 81092 = WalkEmbed.bS Cα ∧
      ∀ q, q ≠ 81092 → c'.nreg q = c₁.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v92', f₂⟩ => ?_) |>.mono
    (by omega) (fun _ h => h)
  · by_cases hβ : c₁.nreg 81084 = c₁.nreg 81012
    · have okc : okB E.W c₁.nmem [.copyN 81092 81083] c₁.nreg := by
        simp only [okB, okI, FScr, FOut]; norm_num
      refine FRS.ifEq_eq (K := 1) hβ ((FRS.block hB _ hI₁ okc).mono (by simp) (fun c' h' => ?_))
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.copyN 81092 81083] c₁.nreg q := fun q => by
        rw [h']
      rw [k1₁, f₁ _ (by norm_num) (by norm_num)] at hβ
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp [regB, regI, upd]
      rw [f₁ _ (by norm_num) (by norm_num), ht, hbSd, ite_eq_left (hb.1 hβ)]
    · refine FRS.ifEq_ne (K := 1) hI₁ hβ ⟨?_, fun _ _ => rfl⟩
      rw [k1₁, f₁ _ (by norm_num) (by norm_num)] at hβ
      rw [v92, hbSd, ite_eq_right (fun h => hβ (hb.2 h))]
  -- J + 2m - bS, mod 2m
  have w85 : c₂.nreg 81085 = c.nreg 81085 := by
    rw [f₂ _ (by norm_num), f₁ _ (by norm_num) (by norm_num)]
  have w91 : c₂.nreg 81091 = 2 * Cα.m := by rw [f₂ _ (by norm_num), v91]
  have ok3 : okB E.W c₂.nmem [.addN 81086 81085 81091, .subN 81086 81086 81092] c₂.nreg := by
    simp only [okB, okI, FScr, FOut, w85, w91]; norm_num; omega
  refine FRS.seq (K₂ := 9) (FRS.block hB _ hI₂ ok3) (fun c₃ hI₃ hA₃ h₃ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.addN 81086 81085 81091, .subN 81086 81086 81092]
      c₂.nreg q := fun q => by rw [h₃]
  have v86 : c₃.nreg 81086 = c.nreg 81085 + 2 * Cα.m - WalkEmbed.bS Cα := by
    rw [e₃]; simp [regB, regI, upd, w85, w91, v92']
  have f₃ : ∀ q, q ≠ 81086 → c₃.nreg q = c₂.nreg q := fun q h => by
    rw [e₃]; simp [regB, regI, upd, h]
  have x91 : c₃.nreg 81091 = 2 * Cα.m := by rw [f₃ _ (by norm_num), w91]
  refine FRS.seq (K₁ := 3) (K₂ := 5) (Q₁ := fun c' =>
      c'.nreg 81086 = WalkEmbed.tpos Cα (c.nreg 81085) ∧ ∀ q, q ≠ 81086 → c'.nreg q = c₃.nreg q)
    ?_ (fun c₄ hI₄ hA₄ ⟨v86', f₄⟩ => ?_) |>.mono (by omega) (fun _ h => h)
  · unfold WalkEmbed.tpos
    by_cases a : c₃.nreg 81086 < c₃.nreg 81091
    · refine (FRS.ifT a (FRS.skip (K := 0) hI₃ ⟨?_, fun _ _ => rfl⟩)).mono (by omega)
        (fun _ h => h)
      rw [v86, x91] at a; rw [v86, Nat.mod_eq_of_lt a]
    · have okm : okB E.W c₃.nmem [.subN 81086 81086 81091] c₃.nreg := by
        simp only [okB, okI, FScr, FOut]; norm_num
      refine (FRS.ifF a (FRS.block hB _ hI₃ okm)).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₃.nmem [.subN 81086 81086 81091] c₃.nreg q := fun q => by
        rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [v86, x91] at *
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  -- L₁, L₂
  have tl := WalkEmbed.tpos_lt Cα (c.nreg 81085)
  have y81 : c₄.nreg 81081 = Cα.m := by
    rw [f₄ _ (by norm_num), f₃ _ (by norm_num), f₂ _ (by norm_num), f₁ _ (by norm_num)
      (by norm_num), hm]
  have y91 : c₄.nreg 81091 = 2 * Cα.m := by rw [f₄ _ (by norm_num), x91]
  have ok5 : okB E.W c₄.nmem [.addN 81093 81086 81081] c₄.nreg := by
    simp only [okB, okI, FScr, FOut, v86', y81]; norm_num; omega
  refine FRS.seq (K₂ := 4) (FRS.block hB _ hI₄ ok5) (fun c₅ hI₅ hA₅ h₅ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₅ : ∀ q, c₅.nreg q = regB c₄.nmem [.addN 81093 81086 81081] c₄.nreg q := fun q => by
    rw [h₅]
  have v93 : c₅.nreg 81093 = WalkEmbed.tpos Cα (c.nreg 81085) + Cα.m := by
    rw [e₅]; simp [regB, regI, upd, v86', y81]
  have f₅ : ∀ q, q ≠ 81093 → c₅.nreg q = c₄.nreg q := fun q h => by
    rw [e₅]; simp [regB, regI, upd, h]
  have z86 : c₅.nreg 81086 = WalkEmbed.tpos Cα (c.nreg 81085) := by rw [f₅ _ (by norm_num), v86']
  have z81 : c₅.nreg 81081 = Cα.m := by rw [f₅ _ (by norm_num), y81]
  have z91 : c₅.nreg 81091 = 2 * Cα.m := by rw [f₅ _ (by norm_num), y91]
  have fr : ∀ q, q ≠ 81086 → q ≠ 81087 → q ≠ 81088 → q ≠ 81091 → q ≠ 81092 → q ≠ 81093 →
      c₅.nreg q = c.nreg q := fun q a1 a2 a3 a4 a5 a6 => by
    rw [f₅ q a6, f₄ q a1, f₃ q a1, f₂ q a5, f₁ q a4 a5]
  by_cases a : c₅.nreg 81091 < c₅.nreg 81093
  · have oka : okB E.W c₅.nmem [.subN 81087 81091 81086, .subN 81088 81081 81087] c₅.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine (FRS.ifT a (FRS.block hB _ hI₅ oka)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₅.nmem [.subN 81087 81091 81086, .subN 81088 81081 81087]
        c₅.nreg q := fun q => by rw [h']
    rw [z91, v93] at a
    refine ⟨by rw [e']; simp [regB, regI, upd, z86], by rw [e']; simp [regB, regI, upd, z91],
      fun h => absurd a (by omega), fun _ => ⟨by rw [e']; simp [regB, regI, upd, z91, z86],
        by rw [e']; simp [regB, regI, upd, z91, z86, z81]⟩,
      fun q a1 a2 a3 a4 a5 a6 => by rw [e']; simp [regB, regI, upd, a2, a3]; exact fr q a1 a2 a3 a4 a5 a6⟩
  · have okb : okB E.W c₅.nmem [.copyN 81087 81081, .constN 81088 0] c₅.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine (FRS.ifF a (FRS.block hB _ hI₅ okb)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₅.nmem [.copyN 81087 81081, .constN 81088 0] c₅.nreg q :=
      fun q => by rw [h']
    rw [z91, v93] at a
    refine ⟨by rw [e']; simp [regB, regI, upd, z86], by rw [e']; simp [regB, regI, upd, z91],
      fun _ => ⟨by rw [e']; simp [regB, regI, upd, z81], by rw [e']; simp [regB, regI, upd]⟩,
      fun h => absurd h (by omega),
      fun q a1 a2 a3 a4 a5 a6 => by rw [e']; simp [regB, regI, upd, a2, a3]; exact fr q a1 a2 a3 a4 a5 a6⟩

/-- Test the host vertex `(s + x) mod n` (`s` in `81089`, offset in register `x`). -/
def vOff (x : ℕ) (sT : Stmt) : Stmt :=
  .seq (Stmt.block [.addN 81071 81089 x])
    (.seq (.ifLtN 81071 81017 .skip (Stmt.block [.subN 81071 81071 81017])) (vTest sT))

/-- The cost bound of `vOff`. -/
def voK (E : FEnv) : ℕ := tvK E + 8

theorem vOff_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {x : ℕ}
    (_hx : x ≠ 81071) (hs : c.nreg 81089 < E.M.W.n) (hxn : c.nreg x < E.M.W.n)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + voK E ≤ E.W) :
    FRS B E.P E.W c₀ (vOff x E.sT) c (voK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        VSet E ((c.nreg 81089 + c.nreg x) % E.M.W.n) → ∀ σb, σb ≤ 1 →
        GoodAt E reg ((c.nreg 81089 + c.nreg x) % E.M.W.n) σb → c'.nreg 81007 = 1)) := by
  have n17 : c.nreg 81017 = E.M.W.n := by rw [hI.hin _ (by unfold FFix; omega), hE.wn]
  have ok1 : okB E.W c.nmem [.addN 81071 81089 x] c.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num; omega
  refine FRS.seq (K₂ := tvK E + 7) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
    (by simp [voK]; omega) (fun _ h => h)
  simp only [List.length_cons, List.length_nil] at hA₁
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.addN 81071 81089 x] c.nreg q := fun q => by rw [h₁]
  have v71 : c₁.nreg 81071 = c.nreg 81089 + c.nreg x := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81071 → c₁.nreg q = c.nreg q := fun q h => by
    rw [e₁]; simp [regB, regI, upd, h]
  have n17₁ : c₁.nreg 81017 = E.M.W.n := by rw [f₁ _ (by norm_num), n17]
  refine FRS.seq (K₁ := 3) (K₂ := tvK E + 4) (Q₁ := fun c' =>
      c'.nreg 81071 = (c.nreg 81089 + c.nreg x) % E.M.W.n ∧
      ∀ q, q ≠ 81071 → c'.nreg q = c.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v₂, f₂⟩ => ?_) |>.mono
    (by omega) (fun _ h => h)
  · by_cases a : c₁.nreg 81071 < c₁.nreg 81017
    · refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨?_, f₁⟩)).mono (by omega) (fun _ h => h)
      rw [v71, n17₁] at a; rw [v71, Nat.mod_eq_of_lt a]
    · have okm : okB E.W c₁.nmem [.subN 81071 81071 81017] c₁.nreg := by
        simp only [okB, okI, FScr, FOut]; norm_num
      refine (FRS.ifF a (FRS.block hB _ hI₁ okm)).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN 81071 81071 81017] c₁.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]; exact f₁ q hq⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [v71, n17₁] at *
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hv2 : c₂.nreg 81071 < E.M.W.n := by rw [v₂]; exact Nat.mod_lt _ (by omega)
  have hw₂ : FWin E c₂ := hw.congr' (fun q a b => f₂ q (by omega))
  refine (vTest_fs hE hB hBT hI₂ hw₂ hv2 (by unfold voK at hroom; omega)).mono le_rfl
    (fun c' ⟨w', fr', m', g'⟩ => ⟨w', fun q a b h1 h2 => by rw [fr' q a b h1, f₂ q h2],
      fun h => m' (by rwa [f₂ _ (by norm_num)]), fun reg hr hch hs σb hσb hg => ?_⟩)
  rw [v₂] at g'
  exact g' reg hr hch hs σb hσb hg

/-- The registers of the first stretch: `(s, 6 + tpos, L₁)`. -/
def str1L : List Instr :=
  [.copyN 81130 81089, .addN 81131 81086 81015, .addN 81131 81131 81012, .copyN 81132 81087,
    .addN 81135 81131 81087]

theorem str1_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hW : c.nreg 81086 + 6 + c.nreg 81087 ≤ E.W) :
    FRS B E.P E.W c₀ (Stmt.block str1L) c 5 (fun c' =>
      c'.nreg 81130 = c.nreg 81089 ∧ c'.nreg 81131 = 6 + c.nreg 81086 ∧
      c'.nreg 81132 = c.nreg 81087 ∧ c'.nreg 81135 = 6 + c.nreg 81086 + c.nreg 81087 ∧
      ∀ q, q ≠ 81130 → q ≠ 81131 → q ≠ 81132 → q ≠ 81135 → c'.nreg q = c.nreg q) := by
  have k5 : c.nreg 81015 = 5 := by rw [hI.hin _ (by unfold FFix; omega), hE.k5]
  have k1 : c.nreg 81012 = 1 := by rw [hI.hin _ (by unfold FFix; omega), hE.k1]
  have ok : okB E.W c.nmem str1L c.nreg := by
    simp only [str1L, okB, okI, regI, upd, FScr, FOut, k5, k1]; norm_num; omega
  refine (FRS.block hB _ hI ok).mono (by simp [str1L]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem str1L c.nreg q := fun q => by rw [h']
  refine ⟨by rw [e']; simp [str1L, regB, regI, upd], by rw [e']; simp [str1L, regB, regI, upd, k5, k1]; ring,
    by rw [e']; simp [str1L, regB, regI, upd], by rw [e']; simp [str1L, regB, regI, upd, k5, k1]; ring,
    fun q a b d e => by rw [e']; simp [str1L, regB, regI, upd, a, b, d, e]⟩

/-- The registers of the second stretch: `((s + L₁) mod n, 6, L₂)`. -/
def str2 : Stmt :=
  .seq (Stmt.block [.addN 81130 81089 81087])
    (.seq (.ifLtN 81130 81017 .skip (Stmt.block [.subN 81130 81130 81017]))
      (Stmt.block [.constN 81131 6, .copyN 81132 81088, .addN 81135 81131 81088]))

theorem str2_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hs : c.nreg 81089 < E.M.W.n) (hL : c.nreg 81087 < E.M.W.n) (hnW : 2 * E.M.W.n ≤ E.W)
    (hW : 6 + c.nreg 81088 ≤ E.W) :
    FRS B E.P E.W c₀ str2 c 7 (fun c' =>
      c'.nreg 81130 = (c.nreg 81089 + c.nreg 81087) % E.M.W.n ∧ c'.nreg 81131 = 6 ∧
      c'.nreg 81132 = c.nreg 81088 ∧ c'.nreg 81135 = 6 + c.nreg 81088 ∧
      ∀ q, q ≠ 81130 → q ≠ 81131 → q ≠ 81132 → q ≠ 81135 → c'.nreg q = c.nreg q) := by
  have n17 : c.nreg 81017 = E.M.W.n := by rw [hI.hin _ (by unfold FFix; omega), hE.wn]
  have ok1 : okB E.W c.nmem [.addN 81130 81089 81087] c.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num; omega
  refine FRS.seq (K₂ := 6) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.addN 81130 81089 81087] c.nreg q := fun q => by rw [h₁]
  have v30 : c₁.nreg 81130 = c.nreg 81089 + c.nreg 81087 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81130 → c₁.nreg q = c.nreg q := fun q h => by
    rw [e₁]; simp [regB, regI, upd, h]
  have n17₁ : c₁.nreg 81017 = E.M.W.n := by rw [f₁ _ (by norm_num), n17]
  refine FRS.seq (K₁ := 3) (K₂ := 3) (Q₁ := fun c' =>
      c'.nreg 81130 = (c.nreg 81089 + c.nreg 81087) % E.M.W.n ∧
      ∀ q, q ≠ 81130 → c'.nreg q = c.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v₂, f₂⟩ => ?_)
  · by_cases a : c₁.nreg 81130 < c₁.nreg 81017
    · refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨?_, f₁⟩)).mono (by omega) (fun _ h => h)
      rw [v30, n17₁] at a; rw [v30, Nat.mod_eq_of_lt a]
    · have okm : okB E.W c₁.nmem [.subN 81130 81130 81017] c₁.nreg := by
        simp only [okB, okI, FScr, FOut]; norm_num
      refine (FRS.ifF a (FRS.block hB _ hI₁ okm)).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN 81130 81130 81017] c₁.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]; exact f₁ q hq⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [v30, n17₁] at *
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have y88 : c₂.nreg 81088 = c.nreg 81088 := f₂ _ (by norm_num)
  have ok3 : okB E.W c₂.nmem [.constN 81131 6, .copyN 81132 81088, .addN 81135 81131 81088]
      c₂.nreg := by
    simp only [okB, okI, regI, upd, FScr, FOut, y88]; norm_num; omega
  refine (FRS.block hB _ hI₂ ok3).mono (by simp) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c₂.nmem [.constN 81131 6, .copyN 81132 81088,
      .addN 81135 81131 81088] c₂.nreg q := fun q => by rw [h']
  refine ⟨by rw [e']; simp [regB, regI, upd]; exact v₂, by rw [e']; simp [regB, regI, upd],
    by rw [e']; simp [regB, regI, upd, y88], by rw [e']; simp [regB, regI, upd, y88],
    fun q a b d e => by rw [e']; simp [regB, regI, upd, b, d, e]; exact f₂ q a⟩

/-- The vertex tests of a kind-1 piece: its ends and the junction of its stretches. -/
def k1Tests (sT : Stmt) : Stmt :=
  .seq (vOff 81011 sT) (.seq (vOff 81081 sT) (.ifLtN 81011 81088 (vOff 81087 sT) .skip))

/-- **A kind-1 piece.** -/
def k1S (sT : Stmt) : Stmt :=
  .seq (Stmt.block k1L) (.seq k1Dir (.seq k1Pos (.seq (k1Tests sT) (.seq (Stmt.block str1L)
    (.seq (descS sT) (.ifLtN 81011 81088 (.seq str2 (descS sT)) .skip))))))

/-- The cost bound of a kind-1 piece. -/
noncomputable def k1K (E : FEnv) (Cα : Chain) (N : NF) : ℕ :=
  13 + (hvK + 9 + (18 + (voK E + (voK E + ((voK E + 2) + (5 +
    (descK E Cα N (decDepth 4 N.nChords) + (7 + descK E Cα N (decDepth 4 N.nChords) + 2))))))))

/-- The registers a kind-1 piece writes. -/
def K1W (q : ℕ) : Prop := DescW q ∨ (81081 ≤ q ∧ q ≤ 81099) ∨ (81130 ≤ q ∧ q ≤ 81135)

/-- The completeness of a stretch `(g, g', L)` of a kind-1 piece (from the piece's start `c`). -/
def SComp (E : FEnv) (c₀ c : Config) (Cα : Chain) (N : NF) (g g' L f : ℕ) : Prop :=
  ∀ (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ),
    DescGood E c₀ Cα N g g' L reg ai bi aj bj dX regα T →
    aj = E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ →
    (0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) → f = 1

theorem kind1_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hPR : c.nreg 81080 + 6 < c₀.nreg ALLOC) {Hs : Host} {Cα : Chain} {N : NF} {γ' : ℕ}
    (hCD : ChainDescAt c₀.nmem (c₀.nmem (c.nreg 81080 + 5)) (Qof E.P) Hs Cα)
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c₀.nmem (c.nreg 81080 + 5)))
    (hNW : NFWithin c₀.nmem (c₀.nmem (c.nreg 81080 + 6)) (c₀.nreg ALLOC) N)
    (hcan : IsCanonicalNF (chainModel Cα) (Qof E.P) N γ' 4) (hQ : Cα.P = Qof E.P)
    (hdir : (∀ d, d ≤ Cα.m → E.M.W.vtx ((c₀.nmem (c.nreg 81080) + d) % E.M.W.n) = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m →
        E.M.W.vtx ((c₀.nmem (c.nreg 81080) + d) % E.M.W.n) = Cα.vertex (Cα.m - d)))
    (hs : c₀.nmem (c.nreg 81080) < E.M.W.n) (hmn : Cα.m < E.M.W.n)
    (hVs : VSet E (c₀.nmem (c.nreg 81080)))
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hnW : 2 * E.M.W.n ≤ E.W) (h2α : 2 * (2 * Cα.m + 7) ≤ E.W)
    (hWa : ∀ r, r < N.nRegions → 2 * (2 * Cα.m + 7) + (N.region r).arcs.length ≤ E.W)
    (hdW : decDepth 4 N.nChords + 1 ≤ E.W)
    (hroom : c.nreg ALLOC + k1K E Cα N ≤ E.W) :
    FRS B E.P E.W c₀ (k1S E.sT) c (k1K E Cα N) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∃ J, (∀ d, d ≤ Cα.m → E.M.W.vtx ((c₀.nmem (c.nreg 81080) + d) % E.M.W.n) =
          WalkEmbed.tourV Cα J d) ∧
        (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
          (v = c₀.nmem (c.nreg 81080) ∨ v = (c₀.nmem (c.nreg 81080) + Cα.m) % E.M.W.n ∨
            (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m ∧
              v = (c₀.nmem (c.nreg 81080) + (2 * Cα.m - WalkEmbed.tpos Cα J)) % E.M.W.n)) →
          VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → c'.nreg 81007 = 1) ∧
        (WalkEmbed.tpos Cα J + Cα.m ≤ 2 * Cα.m →
          SComp E c₀ c Cα N (c₀.nmem (c.nreg 81080)) (6 + WalkEmbed.tpos Cα J) Cα.m
            (c'.nreg 81007)) ∧
        (2 * Cα.m < WalkEmbed.tpos Cα J + Cα.m →
          SComp E c₀ c Cα N (c₀.nmem (c.nreg 81080)) (6 + WalkEmbed.tpos Cα J)
            (2 * Cα.m - WalkEmbed.tpos Cα J) (c'.nreg 81007) ∧
          SComp E c₀ c Cα N ((c₀.nmem (c.nreg 81080) + (2 * Cα.m - WalkEmbed.tpos Cα J)) %
            E.M.W.n) 6 (Cα.m - (2 * Cα.m - WalkEmbed.tpos Cα J)) (c'.nreg 81007))) := by
  have hDH : DistinctHeights (Qof E.P) := ShootCut.goodEnv_distinct hE.hG
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  have h1m := Cα.one_le
  have hsP : Cα.s < (Qof E.P).n := by
    have := (hwf.2 Hs Cα hCD).2.2.2; rwa [hQ] at this
  set s₀ := c₀.nmem (c.nreg 81080)
  set Dα := c₀.nmem (c.nreg 81080 + 5)
  set Bα := c₀.nmem (c.nreg 81080 + 6)
  have hWm : 2 * Cα.m + 7 ≤ E.W := by omega
  -- the reads
  refine FRS.seq (K₂ := k1K E Cα N - 13) (k1Load_fs hE hB hI hPR hCD hwf)
    (fun c₁ hI₁ hA₁ ⟨l89, l33, l34, l82, l81, l83, l84, f₁⟩ => ?_) |>.mono
    (by unfold k1K; omega) (fun _ h => h)
  -- the direction
  refine FRS.seq (K₁ := hvK + 9) (K₂ := k1K E Cα N - 13 - (hvK + 9))
    (k1Dir_fs hE hB hI₁ (by rwa [l89]) (by rwa [l89])
      (by unfold k1K at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨h, hh, hy, d85, f₂⟩ => ?_) |>.mono (by unfold k1K; omega) (fun _ h => h)
  rw [l82, l81] at d85
  rw [l89] at hy
  have hV := dir_correct hDH hQ (by rwa [hQn]) hsP hs
    (by rw [hy]; show (Chazelle.Chain.sidePt E.M.W s₀ 0).2 = _
        rw [Chazelle.Chain.sidePt_zero]) hdir
  set J := if h = Cα.s then 0 else Cα.m with hJdef
  have hJm : J ≤ Cα.m := by rw [hJdef]; split_ifs <;> omega
  have r₂ : ∀ q, 80000 ≤ q → q < 90000 → ¬ (81060 ≤ q ∧ q ≤ 81064) → q ≠ 81085 →
      c₂.nreg q = c₁.nreg q := fun q a b h1 h2 => f₂ q a b (by omega) (by omega) (by omega)
        (by omega) h2
  have q81 : c₂.nreg 81081 = Cα.m := by rw [r₂ _ (by norm_num) (by norm_num) (by omega) (by norm_num), l81]
  have q83 : c₂.nreg 81083 = Cα.topIdx := by
    rw [r₂ _ (by norm_num) (by norm_num) (by omega) (by norm_num), l83]
  have q84 : c₂.nreg 81084 = c₁.nreg 81084 := r₂ _ (by norm_num) (by norm_num) (by omega) (by norm_num)
  -- the offsets
  refine FRS.seq (K₁ := 18) (K₂ := k1K E Cα N - 13 - (hvK + 9) - 18)
    (k1Pos_fs hE hB hI₂ q81 q83 (by rwa [q84]) (by rwa [d85]) (by omega))
    (fun c₃ hI₃ hA₃ ⟨p86, p91, pa, pb, f₃⟩ => ?_) |>.mono (by unfold k1K; omega) (fun _ h => h)
  rw [d85] at p86 pa pb
  set tp := WalkEmbed.tpos Cα J
  have htp2 : tp < 2 * Cα.m := WalkEmbed.tpos_lt Cα J
  -- the lengths
  obtain ⟨L₁, L₂, hL₁, hL₂, hcase⟩ : ∃ L₁ L₂, c₃.nreg 81087 = L₁ ∧ c₃.nreg 81088 = L₂ ∧
      ((tp + Cα.m ≤ 2 * Cα.m ∧ L₁ = Cα.m ∧ L₂ = 0) ∨
        (2 * Cα.m < tp + Cα.m ∧ L₁ = 2 * Cα.m - tp ∧ L₂ = Cα.m - (2 * Cα.m - tp))) := by
    by_cases hc : tp + Cα.m ≤ 2 * Cα.m
    · exact ⟨_, _, rfl, rfl, Or.inl ⟨hc, (pa hc).1, (pa hc).2⟩⟩
    · exact ⟨_, _, rfl, rfl, Or.inr ⟨by omega, (pb (by omega)).1, (pb (by omega)).2⟩⟩
  have hL1m : L₁ ≤ Cα.m := by rcases hcase with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega
  have hL2p : 0 < L₂ ↔ 2 * Cα.m < tp + Cα.m := by
    rcases hcase with ⟨h0, -, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
  -- the frame so far
  have f₁' (q) (h : q ≠ 81081 ∧ q ≠ 81082 ∧ q ≠ 81083 ∧ q ≠ 81084 ∧ q ≠ 81089 ∧ q ≠ 81090 ∧
      q ≠ 81133 ∧ q ≠ 81134 := by omega) : c₁.nreg q = c.nreg q :=
    f₁ q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
  have f₃' (q) (h : q ≠ 81086 ∧ q ≠ 81087 ∧ q ≠ 81088 ∧ q ≠ 81091 ∧ q ≠ 81092 ∧ q ≠ 81093 := by omega) :
      c₃.nreg q = c₂.nreg q := f₃ q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  have G₃ : ∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c₃.nreg q = c.nreg q := fun q a b hq => by
    have h1 : ¬ (81081 ≤ q ∧ q ≤ 81099) := fun h => hq (Or.inr (Or.inl h))
    have h2 : ¬ (81130 ≤ q ∧ q ≤ 81135) := fun h => hq (Or.inr (Or.inr h))
    have h3 : ¬ (81060 ≤ q ∧ q ≤ 81064) := fun h => hq (Or.inl (Or.inr (Or.inl
      (Or.inr (Or.inl h)))))
    rw [f₃' q (by omega), r₂ q (by omega) (by omega) h3 (by omega), f₁' q (by omega)]
  have G07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c₃.nreg q = c.nreg q := fun q a b => by
    rw [f₃' q (by omega), r₂ q (by omega) (by omega) (by omega) (by omega), f₁' q (by omega)]
  have v₃ (q) (hq : q = 81089 ∨ q = 81081 ∨ q = 81133 ∨ q = 81134 := by omega) :
      c₃.nreg q = c₁.nreg q := by
    rw [f₃' q (by omega), r₂ q (by omega) (by omega) (by omega) (by omega)]
  have s89 : c₃.nreg 81089 = s₀ := (v₃ _).trans l89
  have s81 : c₃.nreg 81081 = Cα.m := (v₃ _).trans l81
  have s33 : c₃.nreg 81133 = Dα := (v₃ _).trans l33
  have s34 : c₃.nreg 81134 = Bα := (v₃ _).trans l34
  have hw₃ : FWin E c₃ := hw.congr' G07
  have k0₃ := k0_of hE hI₃
  have hmn' : Cα.m < E.M.W.n := hmn
  -- the vertex tests
  refine FRS.seq (K₁ := voK E + (voK E + (voK E + 2)))
    (K₂ := 5 + (descK E Cα N (decDepth 4 N.nChords) +
      (7 + descK E Cα N (decDepth 4 N.nChords) + 2))) (Q₁ := fun d => FWin E d ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → d.nreg q = c₃.nreg q) ∧
      (c.nreg 81007 = 1 → d.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
        (v = s₀ ∨ v = (s₀ + Cα.m) % E.M.W.n ∨
          (2 * Cα.m < tp + Cα.m ∧ v = (s₀ + (2 * Cα.m - tp)) % E.M.W.n)) →
        VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → d.nreg 81007 = 1)) ?_
    (fun c₆ hI₆ hA₆ ⟨hw₆, f₆, m₆, t₆⟩ => ?_) |>.mono (by unfold k1K at *; omega) (fun _ h => h)
  · refine FRS.seq (vOff_fs hE hB hBT hI₃ hw₃ (x := 81011) (by norm_num) (by rwa [s89])
      (by rw [k0₃]; omega) hnW (by unfold k1K at hroom; omega))
      (fun c₄ hI₄ hA₄ ⟨hw₄, f₄, m₄, t₄⟩ => ?_)
    have f4' (q) (h : 81011 ≤ q ∧ q < 83000 ∧ ¬ VertW q ∧ q ≠ 81071 := by unfold VertW; omega) :
        c₄.nreg q = c₃.nreg q := f₄ q h.1 h.2.1 h.2.2.1 h.2.2.2
    have w81 : c₄.nreg 81081 = Cα.m := (f4' _).trans s81
    have w89 : c₄.nreg 81089 = s₀ := (f4' _).trans s89
    refine FRS.seq (vOff_fs hE hB hBT hI₄ hw₄ (x := 81081) (by norm_num) (by rwa [w89])
      (by rwa [w81]) hnW (by unfold k1K at hroom; omega))
      (fun c₅ hI₅ hA₅ ⟨hw₅, f₅, m₅, t₅⟩ => ?_)
    rw [w89, w81] at t₅
    rw [s89, k0₃, Nat.add_zero, Nat.mod_eq_of_lt hs] at t₄
    have f5' (q) (h : 81011 ≤ q ∧ q < 83000 ∧ ¬ VertW q ∧ q ≠ 81071 := by unfold VertW; omega) :
        c₅.nreg q = c₄.nreg q := f₅ q h.1 h.2.1 h.2.2.1 h.2.2.2
    have x88 : c₅.nreg 81088 = L₂ := (f5' _).trans ((f4' _).trans hL₂)
    have x87 : c₅.nreg 81087 = L₁ := (f5' _).trans ((f4' _).trans hL₁)
    have x89 : c₅.nreg 81089 = s₀ := (f5' _).trans w89
    have k0₅ := k0_of hE hI₅
    have F5 : ∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → c₅.nreg q = c₃.nreg q :=
      fun q a b h1 h2 => by rw [f₅ q a b h1 h2, f₄ q a b h1 h2]
    by_cases a : c₅.nreg 81011 < c₅.nreg 81088
    · have hL2 : 0 < L₂ := by rwa [k0₅, x88] at a
      refine (FRS.ifT a (vOff_fs hE hB hBT hI₅ hw₅ (x := 81087) (by norm_num)
        (by rwa [x89]) (by rw [x87]; omega) hnW (by unfold k1K at hroom; omega))).mono
        (by omega) (fun c₆ ⟨hw₆, f₆, m₆, t₆⟩ => ⟨hw₆, fun q a b h1 h2 => by
          rw [f₆ q a b h1 h2, F5 q a b h1 h2], fun h => m₆ (m₅ (m₄ (by rwa [G07 _ le_rfl (by norm_num)]))), ?_⟩)
      rw [x89, x87] at t₆
      intro reg hr hch v hv hvs σb hσb hg
      rcases hv with rfl | rfl | ⟨-, rfl⟩
      · exact m₆ (m₅ (t₄ reg hr hch hvs σb hσb hg))
      · exact m₆ (t₅ reg hr hch hvs σb hσb hg)
      · rcases hcase with ⟨h0, -, h2⟩ | ⟨h0, h1, -⟩
        · omega
        · rw [← h1] at hvs hg; exact t₆ reg hr hch hvs σb hσb hg
    · have hL2 : L₂ = 0 := by rw [k0₅, x88] at a; omega
      refine (FRS.ifF a (FRS.skip (K := 0) hI₅ ⟨hw₅, F5, fun h => m₅ (m₄ (by rwa [G07 _ le_rfl (by norm_num)])), ?_⟩)).mono
        (by omega) (fun _ h => h)
      intro reg hr hch v hv hvs σb hσb hg
      rcases hv with rfl | rfl | ⟨h3, rfl⟩
      · exact m₅ (t₄ reg hr hch hvs σb hσb hg)
      · exact t₅ reg hr hch hvs σb hσb hg
      · exact absurd (hL2p.2 h3) (by omega)
  -- the facts at `c₆`
  have nV (q) (hq : q = 81089 ∨ q = 81086 ∨ q = 81087 ∨ q = 81088 ∨ q = 81133 ∨ q = 81134 ∨
      q = 81140 ∨ q = 81141 ∨ q = 81081 := by omega) : c₆.nreg q = c₃.nreg q :=
    f₆ q (by omega) (by omega) (by unfold VertW; omega) (by omega)
  have u89 : c₆.nreg 81089 = s₀ := (nV _).trans s89
  have u86 : c₆.nreg 81086 = tp := (nV _).trans p86
  have u87 : c₆.nreg 81087 = L₁ := (nV _).trans hL₁
  have u88 : c₆.nreg 81088 = L₂ := (nV _).trans hL₂
  have u33 : c₆.nreg 81133 = Dα := (nV _).trans s33
  have u34 : c₆.nreg 81134 = Bα := (nV _).trans s34
  have u40 : c₆.nreg 81140 = c.nreg 81140 := (nV _).trans (G₃ _ (by norm_num) (by norm_num)
    (by unfold K1W DescW NodeW LeafW KeyW VertW; omega))
  have u41 : c₆.nreg 81141 = c.nreg 81141 := (nV _).trans (G₃ _ (by norm_num) (by norm_num)
    (by unfold K1W DescW NodeW LeafW KeyW VertW; omega))
  have G₆ : ∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c₆.nreg q = c.nreg q := fun q a b hq => by
    rw [f₆ q a b (fun h => hq (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl h))))))
      (fun h => hq (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))))), G₃ q a b hq]
  -- the stretches
  obtain ⟨hst1, hst2⟩ := piece_stretches hs hmn hV
  have hS1 : Stretch E.M Cα s₀ (6 + tp) L₁ := by
    rcases hcase with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩
    · rw [h1]; exact hst1 h0
    · rw [h1]; exact (hst2 h0).1
  have hDd : IsDecomp N (decDepth 4 N.nChords) := hcan.2.2.2
  have hPC : ∀ {g g' L : ℕ}, Stretch E.M Cα g g' L → PCtx E c₀ Cα Hs N g g' L Dα Bα :=
    fun hS => ⟨hS, hQ, hcan.1, ⟨_, hDd⟩, hNW, hCD, hwf, hWm⟩
  -- the first stretch
  refine FRS.seq (K₁ := 5) (K₂ := descK E Cα N (decDepth 4 N.nChords) +
      (7 + descK E Cα N (decDepth 4 N.nChords) + 2))
    (str1_fs hE hB hI₆ (by rw [u86, u87]; omega))
    (fun c₇ hI₇ hA₇ ⟨a30, a31, a32, a35, f₇⟩ => ?_) |>.mono le_rfl (fun _ h => h)
  rw [u89] at a30; rw [u86] at a31; rw [u87] at a32; rw [u86, u87] at a35
  have f7' (q) (h : q ≠ 81130 ∧ q ≠ 81131 ∧ q ≠ 81132 ∧ q ≠ 81135 := by omega) :
      c₇.nreg q = c₆.nreg q := f₇ q h.1 h.2.1 h.2.2.1 h.2.2.2
  have hR₇ : SRegs c₇ s₀ (6 + tp) L₁ Dα Bα := ⟨a30, a31, a32,
    (f7' _).trans u33, (f7' _).trans u34, a35⟩
  have b40 : c₇.nreg 81140 = c.nreg 81140 := (f7' _).trans u40
  have b41 : c₇.nreg 81141 = c.nreg 81141 := (f7' _).trans u41
  have hw₇ : FWin E c₇ := hw₆.congr' (fun q a b => f7' q (by omega))
  refine FRS.seq (desc_fs hE hB hBT hI₇ hw₇ (hPC hS1) hR₇ hDd hdW (by rwa [b40, b41])
    hnW h2α hWa (by unfold k1K at hroom; omega))
    (fun c₈ hI₈ hA₈ ⟨hw₈, f₈, m₈, t₈⟩ => ?_)
  have nD (q) (hq : q = 81089 ∨ q = 81087 ∨ q = 81088 ∨ q = 81133 ∨ q = 81134 ∨ q = 81140 ∨
      q = 81141 := by omega) : c₈.nreg q = c₇.nreg q :=
    f₈ q (by omega) (by omega) (by unfold DescW NodeW LeafW KeyW VertW; omega)
  have v88 : c₈.nreg 81088 = L₂ := (nD _).trans ((f7' _).trans u88)
  have k0₈ := k0_of hE hI₈
  have G₈ : ∀ q, 81011 ≤ q → q < 83000 → ¬ K1W q → c₈.nreg q = c.nreg q := fun q a b hq => by
    rw [f₈ q a b (fun h => hq (Or.inl h)),
      f7' q (by refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; exact hq (Or.inr (Or.inr ⟨by omega, by omega⟩)))),
      G₆ q a b hq]
  have m8 : c.nreg 81007 = 1 → c₈.nreg 81007 = 1 := fun h => m₈ ((f7' _).trans (m₆ h))
  have t8' : SComp E c₀ c Cα N s₀ (6 + tp) L₁ (c₈.nreg 81007) := by
    intro reg ai bi aj bj dX regα T hD hJa hJr
    rw [← b40, ← b41] at hJa hJr
    exact t₈ reg ai bi aj bj dX regα T hD hJa hJr
  have t6' : ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] → ∀ v,
      (v = s₀ ∨ v = (s₀ + Cα.m) % E.M.W.n ∨
        (2 * Cα.m < tp + Cα.m ∧ v = (s₀ + (2 * Cα.m - tp)) % E.M.W.n)) →
      VSet E v → ∀ σb, σb ≤ 1 → GoodAt E reg v σb → c₈.nreg 81007 = 1 :=
    fun reg hr hch v hv hvs σb hσb hg => m₈ ((f7' _).trans (t₆ reg hr hch v hv hvs σb hσb hg))
  by_cases a : c₈.nreg 81011 < c₈.nreg 81088
  · have hL2 : 0 < L₂ := by rwa [k0₈, v88] at a
    have h2c := hL2p.1 hL2
    obtain ⟨-, hL1e, hL2e⟩ : 2 * Cα.m < tp + Cα.m ∧ L₁ = 2 * Cα.m - tp ∧
        L₂ = Cα.m - (2 * Cα.m - tp) := by
      rcases hcase with ⟨h0, -, -⟩ | h
      · omega
      · exact h
    have hS2 : Stretch E.M Cα ((s₀ + L₁) % E.M.W.n) 6 L₂ := by
      rw [hL1e, hL2e]; exact (hst2 h2c).2
    have w89 : c₈.nreg 81089 = s₀ := (nD _).trans ((f7' _).trans u89)
    have w87 : c₈.nreg 81087 = L₁ := (nD _).trans ((f7' _).trans u87)
    refine (FRS.ifT a (FRS.seq (K₁ := 7) (K₂ := descK E Cα N (decDepth 4 N.nChords)) (str2_fs hE hB hI₈ (by rwa [w89])
      (by rw [w87]; omega) hnW (by rw [v88]; omega))
      (fun c₉ hI₉ hA₉ ⟨d30, d31, d32, d35, f₉⟩ => ?_))).mono (by omega) (fun _ h => h)
    rw [w89, w87] at d30; rw [v88] at d32 d35
    have f9' (q) (h : q ≠ 81130 ∧ q ≠ 81131 ∧ q ≠ 81132 ∧ q ≠ 81135 := by omega) :
        c₉.nreg q = c₈.nreg q := f₉ q h.1 h.2.1 h.2.2.1 h.2.2.2
    have hR₉ : SRegs c₉ ((s₀ + L₁) % E.M.W.n) 6 L₂ Dα Bα := ⟨d30, d31, d32,
      (f9' _).trans ((nD _).trans ((f7' _).trans u33)),
      (f9' _).trans ((nD _).trans ((f7' _).trans u34)), d35⟩
    have e40 : c₉.nreg 81140 = c.nreg 81140 := (f9' _).trans ((nD _).trans b40)
    have e41 : c₉.nreg 81141 = c.nreg 81141 := (f9' _).trans ((nD _).trans b41)
    have hw₉ : FWin E c₉ := hw₈.congr' (fun q a b => f9' q (by omega))
    refine (desc_fs hE hB hBT hI₉ hw₉ (hPC hS2) hR₉ hDd hdW (by rwa [e40, e41])
      hnW h2α hWa (by unfold k1K at hroom; omega)).mono le_rfl
      (fun c' ⟨hw', f', m', t'⟩ => ⟨hw', fun q a b hq => ?_,
        fun h => m' ((f9' _).trans (m8 h)), J, hV,
        fun reg hr hch v hv hvs σb hσb hg => m' ((f9' _).trans (t6' reg hr hch v hv hvs σb hσb hg)),
        fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩⟩)
    · rw [f' q a b (fun h => hq (Or.inl h)),
        f9' q (by refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; exact hq (Or.inr (Or.inr ⟨by omega, by omega⟩)))),
        G₈ q a b hq]
    · rw [← hL1e]
      intro reg ai bi aj bj dX regα T hD hJa hJr
      exact m' ((f9' _).trans (t8' reg ai bi aj bj dX regα T hD hJa hJr))
    · rw [← hL1e, show Cα.m - L₁ = L₂ by omega]
      intro reg ai bi aj bj dX regα T hD hJa hJr
      rw [← e40, ← e41] at hJa hJr
      exact t' reg ai bi aj bj dX regα T hD hJa hJr
  · have hL2 : L₂ = 0 := by rw [k0₈, v88] at a; omega
    have h1c : tp + Cα.m ≤ 2 * Cα.m := by
      by_contra h; exact absurd (hL2p.2 (by omega)) (by omega)
    have hL1e : L₁ = Cα.m := by rcases hcase with ⟨-, h1, -⟩ | ⟨h0, -, -⟩ <;> omega
    refine (FRS.ifF a (FRS.skip (K := 0) hI₈ ⟨hw₈, G₈, m8, J, hV, t6', fun _ => ?_,
      fun h => absurd h (by omega)⟩)).mono (by omega) (fun _ h => h)
    rwa [← hL1e]

end

end Restore

end Chazelle.Core
