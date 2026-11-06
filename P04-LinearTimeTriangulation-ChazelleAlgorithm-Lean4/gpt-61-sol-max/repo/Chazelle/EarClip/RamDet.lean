module

public import Chazelle.Programs.Tactics
public import Chazelle.Geometry.Det

/-!
# RAM kernels for ear clipping, part 1: the successor table and the determinant

## The successor table (`SuccTable`)

The remaining polygon is a cyclic list `l` of original vertex indices (see
`docs/design-earclip.md`).  On the RAM it is stored as a *successor table* in natural memory:
`nmem (l[p]) = l[(p+1) % l.length]`.  `cyc l q = l[q % l.length]` is the element at cyclic
position `q` (`0` for the empty list); `SuccTable c n l` says that `l` is a list of distinct
indices `< n` and that `c.nmem` follows the cyclic order of `l`.  `SuccTable.iterate_nmem`:
iterating `nmem` `k` times from `l[0]` gives `cyc l k`.

## `detInto`

`detInto dst t1 t2 a1 a2 v1 v2 b1 b2` computes `det (a1, a2) (v1, v2) (b1, b2)` (registers) into
real register `dst`, using `t1`, `t2` as scratch; exactly `7` instructions, no side condition
(`detInto_exec`).  It is instantiated four times by the ear test (`D` and the three
sub-determinants of the point-in-triangle test).

## `halfInit`

`rreg 16 := 1 / 2` (`constR 16 1; constR 21 2; divR 16 16 21`), cost `3`; the ear test takes
`rreg 16 = 1/2` as a precondition (`halfInit_exec`).
-/

namespace Chazelle

namespace EarClip

open Machine Machine.Stmt Programs

@[expose] public section

/-! ### The cyclic list and the successor table -/


/-! ### The determinant kernel -/

/-- `rreg dst := det (rreg a1, rreg a2) (rreg v1, rreg v2) (rreg b1, rreg b2)`, with scratch
registers `t1`, `t2`:
`t1 := v1 - a1; t2 := b2 - a2; t1 := t1 * t2; t2 := b1 - a1; dst := v2 - a2; t2 := t2 * dst;
dst := t1 - t2`.  Exactly `7` instructions. -/
def detInto (dst t1 t2 a1 a2 v1 v2 b1 b2 : ℕ) : Stmt :=
  block [.subR t1 v1 a1, .subR t2 b2 a2, .mulR t1 t1 t2, .subR t2 b1 a1, .subR dst v2 a2,
    .mulR t2 t2 dst, .subR dst t1 t2]

/-- **Spec lemma for `detInto`.**  With `dst`, `t1`, `t2` pairwise distinct and distinct from
the six input registers: cost `≤ 7` (the code is straight-line, so exactly `7`); `rreg dst` receives the determinant; real registers
other than `dst, t1, t2`, all natural registers, both memories and the output are unchanged. -/
theorem detInto_exec {P : Polygon} {W : ℕ} (dst t1 t2 a1 a2 v1 v2 b1 b2 : ℕ)
    (hdt1 : dst ≠ t1) (hdt2 : dst ≠ t2) (ht12 : t1 ≠ t2)
    (hin : ∀ r, r = a1 ∨ r = a2 ∨ r = v1 ∨ r = v2 ∨ r = b1 ∨ r = b2 →
      r ≠ dst ∧ r ≠ t1 ∧ r ≠ t2)
    (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (detInto dst t1 t2 a1 a2 v1 v2 b1 b2) c c' k ∧ k ≤ 7 ∧
      c'.rreg dst = det (c.rreg a1, c.rreg a2) (c.rreg v1, c.rreg v2) (c.rreg b1, c.rreg b2) ∧
      (∀ r, r ≠ dst → r ≠ t1 → r ≠ t2 → c'.rreg r = c.rreg r) ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ha1d, ha1t1, ha1t2⟩ := hin a1 (by simp)
  obtain ⟨ha2d, ha2t1, ha2t2⟩ := hin a2 (by simp)
  obtain ⟨hv1d, hv1t1, hv1t2⟩ := hin v1 (by simp)
  obtain ⟨hv2d, hv2t1, hv2t2⟩ := hin v2 (by simp)
  obtain ⟨hb1d, hb1t1, hb1t2⟩ := hin b1 (by simp)
  obtain ⟨hb2d, hb2t1, hb2t2⟩ := hin b2 (by simp)
  unfold detInto
  exec_block
  refine ⟨by omega, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [hdt1, hdt2, ht12, hdt1.symm, hdt2.symm, ht12.symm, ha1d, ha1t1, ha1t2, ha2d, ha2t1,
      ha2t2, hv1d, hv1t1, hv1t2, hv2d, hv2t1, hv2t2, hb1d, hb1t1, hb1t2, hb2d, hb2t1, hb2t2, det]
  · intro r h1 h2 h3
    simp [h1, h2, h3]

/-! ### The constant `1/2` -/

end

end EarClip

end Chazelle
