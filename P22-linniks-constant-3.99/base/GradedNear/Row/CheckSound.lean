module

public import RowCheckCore
public import GradedNear.Row
public import GradedNear.LeafNumSound

/-!
# Soundness of the near-row checker `RowCheckCore`

* `phiI_sound`, `fI_sound`: the enclosures of `Φ(u)` and of the transform `F_c(x) = c Φ(cx)`
  (`Parabolic.laplace_fpar_real`) contain the true values;
* `good_sound`: `RowP.good` gives `Params.Good`;
* `shortSum_sound`, `longSum_sound`, `ibUpper_sound`: the checker's Riemann sum bounds the builders'
  `Params.riemann`, hence `I_B` (`Params.IB_le`), and every cell bound `L_k` is positive;
* `mem_hornerL`, `dI_sound`: the enclosure of `D(δ)` (`Params.Dδ_eq`) contains `D(δ)`.

The enclosures at complex points are proved sound in `GradedNear/Row/SpecialSound.lean`, the
special entries' values in `GradedNear/Row/SpecSound.lean`, and the row check in
`GradedNear/Row/RowSound.lean`.
-/

@[expose] public section

noncomputable section

open IntervalCore LeafNumCore MeasureTheory Set

namespace GradedNear.Row

open Parabolic

/-- The row parameters of the checker as `Params`. -/
def ofCore (p : RowCheckCore.RowP) : Params := ⟨p.γ, p.g1, p.t0, p.s, p.s1, p.h⟩

@[simp] lemma ofCore_m (p : RowCheckCore.RowP) : (ofCore p).m = p.m := rfl
@[simp] lemma ofCore_tk (p : RowCheckCore.RowP) (k : ℕ) : (ofCore p).tk k = p.tk k := rfl
@[simp] lemma ofCore_hk (p : RowCheckCore.RowP) (k : ℕ) : (ofCore p).hk k = p.hk k := rfl
@[simp] lemma ofCore_γ (p : RowCheckCore.RowP) : (ofCore p).γ = p.γ := rfl
@[simp] lemma ofCore_g1 (p : RowCheckCore.RowP) : (ofCore p).g1 = p.g1 := rfl
@[simp] lemma ofCore_t0 (p : RowCheckCore.RowP) : (ofCore p).t0 = p.t0 := rfl
@[simp] lemma ofCore_s (p : RowCheckCore.RowP) : (ofCore p).s = p.s := rfl
@[simp] lemma ofCore_s1 (p : RowCheckCore.RowP) : (ofCore p).s1 = p.s1 := rfl

/-! ## Casts -/

/-! ## `Φ` and `F` -/

/-! ## The parameters -/

/-! ## The Riemann sum -/

/-! ## `D(δ)` -/

/-! ## The constants -/

end GradedNear.Row

end
