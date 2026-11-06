module

public import Chazelle.Golf

public import Chazelle.Core.OracleMainAns

/-!
# Lemma 3.6 (WP-H), part 23: the proof contexts from the structure

From `QAt` (the structure of Lemma 3.6 in memory) and a good environment: the chain data of the
values (`TopOK`), the chord table (`ChordRecOK`) and the context of the main phase (`MainCtx`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ OracleBook

@[expose] public section

variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}

theorem distinctHeights_of_goodEnv (hG : GoodEnv P) : DistinctHeights (Qof P) :=
  (goodShear_epsOf hG.2).2.1

theorem QAt.topOK (h : QAt P m O E V H C N B k) (hG : GoodEnv P) (hv : QVOK P C V) :
    TopOK P C V := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨-, -, -, -, hd3, -⟩ := h.desc
  have hn : 0 < P.n := by
    have := C.n_pos; rw [h.CQ, hQn] at this; exact this
  refine ⟨hv, ?_, by rw [h.tv]; exact Nat.mod_lt _ hn, distinctHeights_of_goodEnv hG⟩
  Ξ h.tv, ← h.dt, hd3
  unfold Chain.top
  Ξ vertex_eq hv

theorem QAt.chordRec (h : QAt P m O E V H C N B k) (hT : TopOK P C V) : ChordRecOK P C V m N :=
  ⟨hT, h.isNF, h.nf, h.nCB, h.hK, h.ch_lt, h.ch_inj, h.ch_sorted⟩

theorem QAt.mainCtx (h : QAt P m O E V H C N B k) (hT : TopOK P C V) : MainCtx P C V N B m :=
  ⟨h.chordRec hT, h.simple, h.nodeMem, h.gOK, h.μ, h.hlab, h.dl, h.dl_all⟩

open Chazelle.Visibility (rayPt) in
/-- **The answer of the query** from the trace of its phases after loading. -/
theorem rest_answer {B : BookData} (X : MainCtx P C V N B m) {z : Point} (hs : SemOK P C V z)
    {c' : Config} (tr : RestTrace P C V N z m c') :
    Answer P C z (sgnOf V.σb) (c'.nreg 120005) (c'.nreg 120006) := by
  have hT := X.ch.hT
  have hv := hT.hv
  have hQn : (Qof P).n = P.n := shear_n _ _
  rcases tr with ⟨hab, h0⟩ | ⟨hab, t, hpart, hf, hdg, h1, h2⟩ |
      ⟨hab, t, hpart, hnd, bD, hD, hbD, pk, hloc, hbest, hb, o5, o6⟩
  · refine ⟨fun h => by rw [h0] at h; omega, fun _ => noHit_of_above C ?_ _⟩
    rw [hs.zy, ← hT.top]; exact hab
  · exact deg_answer X.ch hs hpart hf hdg h1 h2
  · obtain ⟨q1, q2⟩ := main_answer X hs hab hpart hnd hD hbD hloc hbest
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · rw [o5] at hf
      obtain ⟨he, hlt⟩ := hb2 hf
      have hbo : bestOf c' = some (c'.nreg 120052) := by unfold bestOf; rw [ite_eq_left hf]
      have hfh := q1 _ hbo
      refine ⟨_, hfh, ?_, ?_⟩
      · rw [o6, he]; exact Nat.mod_lt _ (by have := hT.tv_lt; omega)
      · Ξ o6, he
        have hsp := spans_of_vOf_pos hfh.1
        Ξ vOf_of_spans hsp
        have hσ2 : sgnOf V.σb * sgnOf V.σb = 1 := by
          rcases hs.σ with h | h <;> rw [h] <;> norm_num
        have hpt : rayPt z (sgnOf V.σb) (sgnOf V.σb *
            (xe (Qof P) (eIdx (Qof P).n V.s (c'.nreg 120052)) V.hz - z.1)) =
            ((xe (Qof P) (eIdx (Qof P).n V.s (c'.nreg 120052)) V.hz, ((Qof P).vtx V.hz).2) : Point) := by
          ϴ rayPt
          ext
          · simp only; rw [← mul_assoc, hσ2, one_mul]; ring
          · simp only; rw [hs.zy]
        Ξ hpt
        rw [hQn] at hsp ⊢
        have hn2 : 2 ≤ P.n := by
          have := C.add_one_le; have := C.one_le; rw [hv.CQ, hQn] at *; omega
        exact xe_mem_edge hT (Nat.mod_lt _ (⋄)) hsp hn2
    · rw [o5] at hf
      have hbo : bestOf c' = none := by unfold bestOf; rw [ite_eq_right hf]
      exact q2 hbo

end

end OracleR

end Chazelle.Core
