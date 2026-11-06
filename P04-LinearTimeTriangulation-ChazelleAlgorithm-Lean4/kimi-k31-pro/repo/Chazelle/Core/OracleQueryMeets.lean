module

public import Chazelle.Core.OracleQueryCost
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# Lemma 3.6 (WP-H), part 28: the query meets its specification

`query_meets`: the query `qry` meets the query clause of `OracleIface.Valid` for the structure
predicate `OAt`, any bands containing `bSign`, `bLocate`, `bOQuery`, and any cost constant
`κ ≥ κq`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook NFLoc

@[expose] public section

/-- A query origin in registers is determined by the registers. -/
theorem qOriginIn_unique {c : Config} {r : ℕ} {o o' : QOrigin} (h : QOriginIn c r o)
    (h' : QOriginIn c r o') : o = o' := by
  rcases o with (i | ⟨e, hh⟩) | hh <;> rcases o' with (i' | ⟨e', hh'⟩) | hh' <;>
    simp [QOriginIn, SymPtIn] at h h' <;>
    first
      | (exfalso; omega)
      | (simp [QOrigin.sym.injEq, SymPt.vtx.injEq, SymPt.onEdge.injEq, QOrigin.box.injEq]
         omega)

/-- The registers written by the query lie in the bands `bSign`, `bLocate`, `bOQuery`. -/
theorem BQ_band {r : ℕ} (h : BQ r = true) : bandOf r = bSign ∨ bandOf r = bLocate ∨
    bandOf r = bOQuery := by
  unfold bandOf bSign bLocate bOQuery
  simp [BQ, BLd, BRest, Bk, BCS, BP, BX2, BCP, BDg, BX, BMain, BD, BN, BA, BW, BE, BT, BPo,
    BCa, BL, Bdir, Bloc, Bcmp, BC, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- **The query meets its specification.** -/
theorem query_meets {bands : Finset ℕ} (hb : bSign ∈ bands ∧ bLocate ∈ bands ∧ bOQuery ∈ bands)
    {κ : ℕ} (hκ : κq ≤ κ) :
    Meets qry bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ OAt P c.nmem (rd c bOQuery 0) ∧
        ∃ o : QOrigin, o.Lt P.n ∧ QOriginIn c (bandReg bOQuery 1) o)
      (fun P c c' => ∀ H C (o : QOrigin),
        ChainDescAt c.nmem (c.nmem (rd c bOQuery 0)) (Qof P) H C →
        QOriginIn c (bandReg bOQuery 1) o →
          let z := o.eval (Qof P) C (dirOf (rd c bOQuery 4))
          (rd c' bOQuery 5 = 1 → ∃ t, FirstHit C.set z (dirOf (rd c bOQuery 4)) t ∧
            rd c' bOQuery 6 < P.n ∧
            Visibility.rayPt z (dirOf (rd c bOQuery 4)) t ∈ (Qof P).edge (rd c' bOQuery 6)) ∧
          (rd c' bOQuery 5 ≠ 1 → NoHit C.set z (dirOf (rd c bOQuery 4))))
      (fun _ c => ⌈(κ : ℝ) * ((c.nmem (rd c bOQuery 0 + 2) : ℝ) ^ ((1 : ℝ) / 3) *
        ((c.nmem (c.nmem (rd c bOQuery 0) + 2) : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)⌉₊) := by
  intro P W c hw ⟨hG, hHW, ⟨E, hE, hOE, hrob⟩, o, hol, ho⟩ _
  set O := rd c bOQuery 0 with hOdef
  obtain ⟨V, H, C, N, B, k, hA⟩ := hrob.holds
  have hEW : E ≤ W := by rw [← hE]; exact hw.2 _
  have hn : 1 ≤ P.n := by
    have := C.add_one_le; rwo [hA.CQ, show (Qof P).n = P.n from shear_n _ _] at this
  have hW : 8 * P.n + 32 ≤ W := by ufo hostWords at hHW
  obtain ⟨c', k', ex, hk, hf, hans⟩ := qry_exec hG hW hA hEW hHW c hw rfl rfl ho hol
    (NC := NCof (min (c.nmem (O + 2)) (2 * V.m + 7))) (CS := 8 * k ^ 2)
    (fun u _ => (hA.withQ o _).nodeCost_le hA.simple)
    (fun u _ => (hA.withQ o _).clusSize_le _)
  refine ⟨c', k', ex, ?_, ?_, frame_of_frameB hf (fun r hr => ⟨?_, ?_⟩) k'⟩
  · -- the cost
    beta_reduce
    have hc := hA.qcost_le
    have hk' : (k' : ℝ) ≤ ((100 + (715 * V.L + 700 + dstarCost c.nmem V +
        4 * candCost V (NCof (min (c.nmem (O + 2)) (2 * V.m + 7))) (8 * k ^ 2) + 500) : ℕ) : ℝ) := by
      exact_mod_cast hk
    have hD : c.nmem (c.nmem (rd c bOQuery 0) + 2) = V.m := by rw [hA.lD, hA.dm]
    rw [hD]
    have hG0 : (0 : ℝ) ≤ (c.nmem (O + 2) : ℝ) ^ ((1 : ℝ) / 3) * ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1 :=
      by positivity
    have hκR : (κq : ℝ) ≤ κ := by exact_mod_cast hκ
    have : (k' : ℝ) ≤ (κ : ℝ) * ((c.nmem (O + 2) : ℝ) ^ ((1 : ℝ) / 3) *
        ((V.m : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1) := by nlinarith
    exact_mod_cast this.trans (Nat.le_ceil _)
  · -- the answer
    intro H' C' o' hC' ho'
    have hCC : C' = C := NFLoc.chain_eq_of_desc hC' (by rw [hA.lD]; exact hA.desc)
    have hoo  := qOriginIn_unique ho' ho
    subst hCC hoo
    exact hans
  · rcases BQ_band hr with h | h | h <;> rw [h]
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2
  · rintro rfl; simp [BQ, BLd, BRest, Bk, BCS, BP, BX2, BCP, BDg, BX, BMain, BD, BN, BA, BW, BE,
      BT, BPo, BCa, BL, Bdir, Bloc, Bcmp, BC, ALLOC] at hr

end

end OracleR

end Chazelle.Core
