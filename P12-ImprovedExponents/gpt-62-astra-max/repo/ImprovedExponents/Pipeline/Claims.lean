module

public import ImprovedExponents.Pipeline.Fits
public import ImprovedExponents.Pipeline.HostBound
public import ImprovedExponents.Cost8X.Offline
public import ImprovedExponents.HostMid.AtParameters
public import ImprovedExponents.ParamRoutines.Rat

@[expose] public section

/-!
# The two ingredients as claims about programs

For the time model `lightModel` of upstream (procedures of programs of its language):

* **The thin product** at rational ratios `c = a/b` and `θ = p/q` with
  `(c/2) H(1/c) + (c - 1) ln 3 < 18 ln 4`, on the instances with `D ≤ N^ε`, `ε ≤ 1/18`:
  with the paper's exponent `γ = θ ln(1/ρ_c)/ln 4` for `ε < R_c(γ)` (`thinClaim_gammaOf`), and with
  every `γ` below the exact exponent `γX(c, θ)` for `ε < R_c(γ)` (`thinClaim_gammaX`). The program
  is the same; the second statement rests on the exact count of the leaves. With the regime test
  `D^r ≤ N^s` in place of the program's `D^18 ≤ N`, the conditions become
  `(c/2) H(1/c) + (c - 1) ln 3 < (r/s) ln 4` and `ε ≤ s/r` (`thinClaimRS_gammaX`).
* **The reduction from Exact Triangle** with the parameters `D(n) = ⌊n^{a/b}⌋` and
  `g = ⌈D^{c/d}⌉`: as in the paper, every call of the solver charged at the dimension `D`
  (`hostBound_rat`), and for the host that passes the true size of the middle part, charged at
  `⌈⌊√D⌋/g⌉ ⌊√D⌋ ≈ D/g` (`hostBound_mid_rat`).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4 ParamRoutines HostMid

/-! ## The thin product -/

section thin

variable {a b p q : ℕ}

end thin

/-! ## The reduction from Exact Triangle -/

/-- The host that passes the true size of the middle part, for any parameter routines. -/
theorem claim17Mid_of_pack {D g : ℕ → ℕ} (pk : ParamPack D g) :
    Claim17Mid lightModel strassen D g :=
  claim17Mid_of_paramProcs D g pk.procD pk.procG pk.D_pos pk.polyD pk.polyG pk.polyWD pk.polyWG
    pk.D_eq pk.G_eq pk.stepsD_budget pk.stepsG_budget

/-- `Claim17Mid` is `HostBound` with the solver charged at `⌈⌊√D⌋/g⌉ ⌊√D⌋`. -/
theorem hostBound_iff_claim17Mid (M : DetTimeModel) (MM : ℕ → ℝ) (D g : ℕ → ℕ) :
    HostBound M MM D g (fun n => pieceSizeNat (D n) (g n) * Nat.sqrt (D n))
      ↔ Claim17Mid M MM D g :=
  Iff.rfl

variable (a b c d : ℕ)

/-- **Theorem 17 at rational exponents, charged at the true size of the middle part**:
`D(n) = ⌊n^{a/b}⌋`, `g = ⌈D^{c/d}⌉`, every call of the solver charged at `⌈⌊√D⌋/g⌉ ⌊√D⌋`. -/
theorem hostBound_mid_rat (hb : 1 ≤ b) (hd : 1 ≤ d) (hab : a ≤ 2 * b) (hcd : c ≤ 3 * d) :
    HostBound lightModel strassen (paramDRat a b) (paramGRatOf a b c d)
      (fun n => pieceSizeNat (paramDRat a b n) (paramGRatOf a b c d n)
        * Nat.sqrt (paramDRat a b n)) :=
  (hostBound_iff_claim17Mid _ _ _ _).2 (claim17Mid_of_pack (paramPackRat a b c d hb hd hab hcd))

/-- **Theorem 17 charged at the true size of the middle part, at all rational exponents**, in the
time model `M`: the statement `hostBound_mid_rat` makes about `lightModel`, as a property of `M`.
The model of all-edges Exact Triangle (`ImprovedExponents.AllEdges.lightModelAE`) has it too, and
the deduction from here to Exact Triangle is the same for every model that has it. -/
def MidHostRat (M : DetTimeModel) : Prop :=
  ∀ a b c d : ℕ, 1 ≤ b → 1 ≤ d → a ≤ 2 * b → c ≤ 3 * d →
    HostBound M strassen (paramDRat a b) (paramGRatOf a b c d)
      (fun n => pieceSizeNat (paramDRat a b n) (paramGRatOf a b c d n)
        * Nat.sqrt (paramDRat a b n))

/-- `lightModel` has the host of Theorem 17 at the true size of the middle part. -/
theorem midHostRat_light : MidHostRat lightModel := fun a b c d hb hd hab hcd =>
  hostBound_mid_rat a b c d hb hd hab hcd

end ImprovedExponents
