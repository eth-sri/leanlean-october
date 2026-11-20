module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Rect
public import ThreeSumApsp.Lang.Lib.Pass
public import ImprovedExponents.AllEdges.Task

@[expose] public section

/-! Check every pair with the interval scan and write its flag to the given output matrix. -/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

registers [Size, _, AdrAB, AdrBC, AdrAC, Out, _, VtxA, VtxB, _, Res]

end Brute

/-- What brute needs: sums of three weights, no cells, one call. -/
def bruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩

/-- An instance of Exact Triangle gives `scan` what it assumes. -/
theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x where
  hw := hok.space
  hU := by exact_mod_cast hok.word
  toArrays := hpre.toArrays.mono hok.cells

open Brute

/-- One pair `(a, b)`: res := scan(ab, bc, ac, n, a, b, 0, n); M (fr + a n + b) := res.  The locals
are those of upstream's `brute`: `Res` is the result of the scan. -/
def bruteAEPair (pScan : ℕ) : Stmt :=
  .call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, v VtxA, v VtxB, k 0, v Size] Res ;;
  .store (v Out +' v VtxA *' v Size +' v VtxB) (v Res)

/-- bruteAE(n, U, ab, bc, ac, out, fr). -/
def bruteAEBody (pScan : ℕ) : Stmt :=
  .for VtxA (v Size) (.for VtxB (v Size) (bruteAEPair pScan)) ;; .set 0 (v Out)

/-- The time of bruteAE. -/
def tBruteAE (n : ℕ) : ℕ := 110 * n ^ 3 + 100

private theorem tBruteAE_ge (n : ℕ) : n * (n * (tScan n + 24 + 8) + 14) + 6 + 2 ≤ tBruteAE n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · have hsq : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
    have hlin : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
    rw [tScan, show n * (n * (24 * n + 35 + 24 + 8) + 14) =
      24 * n ^ 3 + 67 * n ^ 2 + 14 * n by ring, tBruteAE]
    omega

abbrev bruteArgs (x : AeInst) (fr : ℕ) : List ℤ := [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr]

private theorem bruteAE_spec {pScan : ℕ} (hP : P[pScan]? = some scanBody) (x : AeInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Ends lim P d (bruteAEBody pScan) ⟨frame (bruteArgs x fr), μ⟩ (tBruteAE x.n) fun σ =>
      σ.loc 0 = x.out ∧ Seg σ.mem x.out (aeFlags x.n x.AB x.BC x.AC) ∧
        SameOutside μ σ.mem x.out (x.n * x.n) := by
  have C := hpre.toPre.weights hok
  have hw := C.hw
  have hd : d < lim.depth := hok.depth
  have hcap := hpre.belowOut.trans hok.cells
  have hn := Nat.le_mul_of_pos_left x.n hpre.n_pos
  have hword : (x.n : ℤ) ≤ lim.word := by omega
  let flags := aeFlags x.n x.AB x.BC x.AC
  let f q := flags.getD q 0
  let loc (r : ℤ) := frame (bruteArgs x fr ++ [0, 0, 0, r])
  rw [← frame_append_zeros (bruteArgs x fr) 4]
  unfold bruteAEBody
  refine Ends.seq _ 2 (Ends.forRect loc (fun i j _ ν => ν = wrote μ x.out f (i * x.n + j))
    0 (by simp [wrote_zero]) hword hword (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_ (hT := le_rfl))
    (tBruteAE_ge x.n)
  · rintro i j r _ hi hj rfl
    have hidx : i * x.n + j < x.n * x.n := Nat.mul_add_lt_mul hi hj
    have C' := C.keep (sameOutside_wrote (f := f) hidx.le)
      hpre.apartAB.symm hpre.apartBC.symm hpre.apartAC.symm
    simp only [loc, rectLoc, update_frame_setLocal]
    unfold bruteAEPair
    light_call (scan_meets hP C' hi hj (c0 := 0) (Nat.zero_add x.n).le) with _ _ ⟨rfl, rfl⟩
    have he : flag (scanHit x.n x.AB x.BC x.AC i j 0 x.n = true) = f (i * x.n + j) := by
      rw [flag_eq_bit]; exact (aeFlags_getD_eq_bit_scanHit _ _ _ hi hj).symm
    rw [he]
    refine Ends.storeTo (x.out + (i * x.n + j)) (f (i * x.n + j)) ⟨_, rfl, ?_⟩
    simpa only [Nat.add_assoc] using
      (wrote_succ (μ := μ) (dst := x.out) (f := f) (j := i * x.n + j))
  · rintro i r ν _ rfl
    simp [Nat.succ_mul]
  · rintro r j ν rfl
    simp only [loc, rectLoc, update_frame_setLocal]
    exact Ends.setTo x.out ⟨rfl, seg_wrote (length_aeFlags ..) fun i hi => (List.getD_eq_getElem _ _ hi).symm,
      sameOutside_wrote le_rfl⟩

theorem bruteAE_meets {p pScan : ℕ} (hB : P[p]? = some (bruteAEBody pScan))
    (hP : P[pScan]? = some scanBody) (x : AeInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Meets lim P p d (bruteArgs x fr) μ (tBruteAE x.n) fun r ν =>
      r = x.out ∧ Seg ν x.out (aeFlags x.n x.AB x.BC x.AC) ∧ SameOutside μ ν x.out (x.n * x.n) :=
  .of_body hB (bruteAE_spec hP x μ fr hpre hok)

theorem bruteAE_solves : Solves aeTask [scanBody, bruteAEBody 0] 1 (fun n _ => tBruteAE n) bruteNeed :=
  ⟨_, rfl, fun R lim d x μ fr hpre hok => (bruteAE_spec rfl x μ fr hpre hok).mono le_rfl
    fun _ ⟨_, hs, hk⟩ => ⟨hs, fun b hb => hk b hb.2⟩⟩

end ImprovedExponents.AllEdges
