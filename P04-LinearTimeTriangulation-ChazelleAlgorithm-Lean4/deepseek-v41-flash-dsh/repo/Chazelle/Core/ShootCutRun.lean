module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutDyDn
public import Chazelle.Core.ShootCutGrade

/-!
# WP-G, part 17: the stretches of the main loop

A step of the main loop starts at a walk vertex `c = i + 6` of the double boundary whose host
point lies in a `run a ℓ` item at offset `t`, with `q = (a + t) mod n`:

* `uOf_up`, `uOf_down`: along a climbing (descending) stretch the host point moves forward
  (backward) inside the item;
* `Brk`: the tour position `i` is a breakpoint (a turn of the tour or a break host point,
  `card_brk_le`); `brk_run`, `brk_pt`: the host breaks met by a step;
* `upBlocks_of`, `dnBlocks_of`: the blocks of the dyadic cover of a stretch are valid pieces
  with vertex ends (`VPc`), as the sweeps need them.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)

namespace ShootCut

/-- A valid piece with walk-vertex ends, the start before the end. -/
def VPc (P : Polygon) (C : Chain) (m : ℕ → ℕ) (h γ : ℕ) (pc : Pc) : Prop :=
  PcOK P C m h γ pc ∧ pc.s.hgt = 0 ∧ pc.e.hgt = 0 ∧ pc.s.edge < pc.e.edge

theorem EmitOK.mono {P : Polygon} {W : ℕ} {emit : Machine.Stmt} {A₀ : ℕ} {Pv Pv' : Pc → Prop}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ Pv I K)
    (h : ∀ pc, Pv' pc → Pv pc) : EmitOK P W emit A₀ Pv' I K :=
  ⟨hE.stable, fun ps pc c hw hI hR hv => hE.run ps pc c hw hI hR (h pc hv)⟩

section Run

variable (C : Chain) {Q : Polygon} {H : Host}

/-- **The host point along a climbing stretch.** -/
theorem uOf_up (hP : C.P = H.poly Q) {i d : ℕ} (hJ : tJ C i + d ≤ C.m) {r a ℓ t : ℕ}
    (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : (C.s + sideE C.m (tJ C i)) % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t + d ≤ ℓ) :
    (C.s + sideE C.m (tJ C (i + d))) % C.P.n = NFLoc.preLen Q.n H r + (t + d) := by
  have hN : C.P.n = (H.pts Q.n).length := by rw [hP]; simp [Host.poly, Polygon.n]
  have hsucc := NFLoc.preLen_succ Q.n H hr
  have hlen := NFLoc.preLen_mono Q.n H (show r + 1 ≤ H.length by omega)
  rw [NFLoc.preLen_length] at hlen
  rw [hrun] at hsucc
  simp only [NFLoc.itemCnt] at hsucc
  rw [sideE_up C hJ, ← Nat.add_assoc, Nat.add_mod, hu, Nat.mod_eq_of_lt (show d < C.P.n by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The host point along a descending stretch.** -/
theorem uOf_down (hP : C.P = H.poly Q) {i d : ℕ} (hm : C.m ≤ tJ C i) (hJ : tJ C i + d ≤ 2 * C.m)
    {r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : (C.s + sideE C.m (tJ C i)) % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t ≤ ℓ)
    (hdt : d ≤ t) :
    (C.s + sideE C.m (tJ C (i + d))) % C.P.n = NFLoc.preLen Q.n H r + (t - d) := by
  have hN : C.P.n = (H.pts Q.n).length := by rw [hP]; simp [Host.poly, Polygon.n]
  have hsucc := NFLoc.preLen_succ Q.n H hr
  have hlen := NFLoc.preLen_mono Q.n H (show r + 1 ≤ H.length by omega)
  rw [NFLoc.preLen_length] at hlen
  rw [hrun] at hsucc
  simp only [NFLoc.itemCnt] at hsucc
  have hkd : d ≤ sideE C.m (tJ C i) := by
    have := sideE_down C (d := d) hm hJ
    have hle := Chazelle.Chain.sideE_le (m := C.m) (j := tJ C i) (tJ_lt C i).le
    unfold sideE at *
    split_ifs at * <;> omega
  rw [sideE_down C hm hJ]
  have hpos : 0 < C.P.n := C.n_pos
  have e := Nat.div_add_mod (C.s + sideE C.m (tJ C i)) C.P.n
  rw [hu] at e
  have e2 : C.s + (sideE C.m (tJ C i) - d) =
      C.P.n * ((C.s + sideE C.m (tJ C i)) / C.P.n) + (NFLoc.preLen Q.n H r + (t - d)) := by
    omega
  rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- The tour position `i` is a **breakpoint**: a turn of the tour or a break host point. -/
def Brk (n : ℕ) (H : Host) (i : ℕ) : Prop :=
  tJ C i = 0 ∨ tJ C i = C.m ∨ HostBreak n H (uOf C i)

/-- **A break in a run.** -/
theorem brk_run {n : ℕ} {i r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C i = NFLoc.preLen n H r + t) (ht : t ≤ ℓ)
    (hc : t = 0 ∨ t = ℓ ∨ (a + t) % n = 0 ∨ (a + t) % n = n - 1) : Brk C n H i := by
  right; right
  have hsucc := NFLoc.preLen_succ n H hr
  rw [hrun] at hsucc
  simp only [NFLoc.itemCnt] at hsucc
  refine ⟨r, hr, by omega, by omega, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some, hrun]
  simp only
  rw [hu, show NFLoc.preLen n H r + t - NFLoc.preLen n H r = t by omega]
  exact hc

/-- **A point item is a break.** -/
theorem brk_pt {n : ℕ} {i r : ℕ} {x : SymPt} (hr : r < H.length) (hpt : H[r] = .pt x)
    (hu1 : NFLoc.preLen n H r ≤ uOf C i) (hu2 : uOf C i < NFLoc.preLen n H (r + 1)) :
    Brk C n H i := by
  right; right
  refine ⟨r, hr, hu1, hu2, ?_⟩
  Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some, hpt
  trivial

end Run

/-! ## The blocks of a stretch -/

theorem lt_gradeCount {n g b : ℕ} (h : b * 2 ^ g + 2 ^ g ≤ n - 1) : b < gradeCount n g := by
  have hp := Nat.two_pow_pos g
  unfold gradeCount
  have : b * 2 ^ g ≤ n - 2 := ⋄
  have := (Nat.le_div_iff_mul_le hp).2 this
  omega

variable {O : OracleIface} {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ A₀ W : ℕ}

/-- The words of the entry of a processed block lie below `A₀`. -/
theorem entry_low (hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀) {γ g b : ℕ} (hg : 0 < g)
    (hγ : 2 ^ g ≤ γ) (hcap : γ ≤ 2 ^ (m₀ h - 1)) (hb : b * 2 ^ g + 2 ^ g ≤ P.n - 1) :
    m₀ (h + 2) + g < A₀ ∧ m₀ (m₀ (h + 2) + g) + 3 * b + 2 < A₀ := by
  obtain ⟨hΛ, -⟩ := block_grade (γ := γ) hg hγ hcap
  obtain ⟨-, h1, h2⟩ := grade_entry hR hΛ (lt_gradeCount hb)
  exact ⟨h1, h2⟩

/-- **The blocks of a climbing stretch** are valid pieces for the upward sweep. -/
theorem upBlocks_of (hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀) (hAW : A₀ ≤ W)
    {c₀ q₀ L : ℕ} (hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx (c₀ + d) = (Qof P).vtx (q₀ + d))
    (h6 : 6 ≤ c₀) (hcL : c₀ + L ≤ 2 * C.m + 6) (hqL : q₀ + L < P.n) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ (m₀ h - 1)) :
    UpBlocks (VPc P C m₀ h γ) m₀ W A₀ (m₀ (h + 2)) c₀ q₀ L := by
  intro g b hlo hhi
  have hp := Nat.two_pow_pos g
  have e1 : (b + 1) * 2 ^ g = b * 2 ^ g + 2 ^ g := ⋆
  refine ⟨fun hg => ?_, fun e he => ?_⟩
  · obtain ⟨h1, h2⟩ := entry_low hR hg (γ := γ) (b := b) (⋄) hcap (by omega)
    exact ⟨h1, ⋄⟩
  · refine ⟨blockUp_ok hwalk h6 hcL hqL hLγ hcap hlo hhi fun hg => he (⋄), rfl, rfl,
      by simp only [upPc]; omega⟩

/-- **The blocks of a descending stretch** are valid pieces for the downward sweep. -/
theorem dnBlocks_of (hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀) (hAW : A₀ ≤ W)
    {c₀ q₀ L : ℕ} (hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx (c₀ + d) = (Qof P).vtx (q₀ - d))
    (h6 : 6 ≤ c₀) (hcL : c₀ + L ≤ 2 * C.m + 6) (hq : q₀ < P.n) (hLq : L ≤ q₀) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ (m₀ h - 1)) :
    DnBlocks (VPc P C m₀ h γ) m₀ W A₀ (m₀ (h + 2)) c₀ q₀ L := by
  intro g b hlo hhi
  have hp := Nat.two_pow_pos g
  have e1 : (b + 1) * 2 ^ g = b * 2 ^ g + 2 ^ g := ⋆
  refine ⟨fun hg => ?_, fun e he => ?_⟩
  · obtain ⟨h1, h2⟩ := entry_low hR hg (γ := γ) (b := b) (⋄) hcap (by omega)
    exact ⟨h1, ⋄⟩
  · refine ⟨blockDn_ok hwalk h6 hcL hq hLq hLγ hcap hlo hhi fun hg => he (⋄), rfl, rfl,
      by simp only [dnPc]; omega⟩

end ShootCut

end

end Chazelle.Core
