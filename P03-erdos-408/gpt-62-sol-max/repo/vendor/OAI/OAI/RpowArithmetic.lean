module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.FieldSimp
public meta import Qq

@[expose] public section

namespace OAI.RpowArithmetic

theorem atom (z a : ℝ) : a = a*z^(0:ℝ) := by simp
theorem base (z : ℝ) : z = 1*z^(1:ℝ) := by simp
theorem power (z e : ℝ) : z^e = 1*z^e := by simp
theorem product {z a b c d e f : ℝ} (hz : 0<z)
    (ha : a = c*z^e) (hb : b = d*z^f) : a*b = (c*d)*z^(e+f) := by
  rw [ha,hb,Real.rpow_add hz]
  ring
theorem quotient {z a b c d e f : ℝ} (hz : 0<z)
    (ha : a = c*z^e) (hb : b = d*z^f) : a/b = (c/d)*z^(e-f) := by
  rw [ha,hb,Real.rpow_sub hz,mul_div_mul_comm]
theorem inverse {z a c e : ℝ} (hz : 0<z) (ha : a = c*z^e) :
    a⁻¹ = c⁻¹*z^(-e) := by rw [ha,Real.rpow_neg hz.le,mul_inv_rev,mul_comm]
theorem naturalPower {z a c e : ℝ} (hz : 0<z) (ha : a = c*z^e) (n : ℕ) :
    a^n = c^n*z^(e*(n:ℝ)) := by rw [ha,mul_pow,Real.rpow_mul_natCast hz.le]
theorem nestedPower {z e f : ℝ} (hz : 0 < z) : (z^e)^f = 1*z^(e*f) := by
  rw [← Real.rpow_mul hz.le, one_mul]
theorem sqrtPower {z a c e : ℝ} (hz : 0 < z) (h : a = c*z^e) :
    Real.sqrt a = Real.sqrt c*z^(e/2) := by
  rw [h, Real.sqrt_mul' _ (Real.rpow_nonneg hz.le _), Real.sqrt_eq_rpow (z^e),
    ← Real.rpow_mul hz.le]
  congr 2 <;> ring

theorem same {z a b c d e f : ℝ} (ha : a = c*z^e) (hb : b = d*z^f)
    (hc : c = d) (he : e = f) : a = b := by rw [ha,hb,hc,he]

end OAI.RpowArithmetic

public meta section
open Lean Meta Elab Tactic Qq

namespace OAI.RpowArithmetic

/-- Collect powers of `z`, keeping other real factors in the coefficient. -/
partial def collect (z : Q(ℝ)) (hz : Q(0 < $z)) (a : Q(ℝ)) :
    MetaM ((c : Q(ℝ)) × (e : Q(ℝ)) × Q($a = $c*$z^$e)) := do
  if ← withReducible (isDefEq a z) then
    let _ : $a =Q $z := ⟨⟩
    return ⟨q(1),q(1),q(base $z)⟩
  match a with
  | ~q($x*$y) =>
    let ⟨c,e,hc⟩ ← collect z hz x
    let ⟨d,f,hd⟩ ← collect z hz y
    return ⟨q($c*$d),q($e+$f),q(product $hz $hc $hd)⟩
  | ~q($x/$y) =>
    let ⟨c,e,hc⟩ ← collect z hz x
    let ⟨d,f,hd⟩ ← collect z hz y
    return ⟨q($c/$d),q($e-$f),q(quotient $hz $hc $hd)⟩
  | ~q($x⁻¹) =>
    let ⟨c,e,hc⟩ ← collect z hz x
    return ⟨q($c⁻¹),q(-$e),q(inverse $hz $hc)⟩
  | ~q($x^($n : ℕ)) =>
    let ⟨c,e,hc⟩ ← collect z hz x
    return ⟨q($c ^ $n),q($e * (Nat.cast $n : ℝ)),q(naturalPower $hz $hc $n)⟩
  | ~q(Real.sqrt $x) =>
    let ⟨c,e,hc⟩ ← collect z hz x
    return ⟨q(Real.sqrt $c),q($e/2),q(sqrtPower $hz $hc)⟩
  | ~q(($x ^ ($m : ℝ)) ^ ($n : ℝ)) =>
    if ← withReducible (isDefEq x z) then
      let _ : $x =Q $z := ⟨⟩
      return ⟨q(1),q($m*$n),q(nestedPower (e := $m) (f := $n) $hz)⟩
    return ⟨a,q(0),q(atom $z $a)⟩
  | ~q($x^($n : ℝ)) =>
    if ← withReducible (isDefEq x z) then
      let _ : $x =Q $z := ⟨⟩
      return ⟨q(1),n,q(power $z $n)⟩
    return ⟨a,q(0),q(atom $z $a)⟩
  | _ => return ⟨a,q(0),q(atom $z $a)⟩

/-- Solve identities of real monomials by collecting powers of the positive base in `h`
    and normalizing the coefficient and exponent separately. -/
elab "rpow_ring " h:term : tactic => withMainContext do
  let goal ← getMainGoal
  let h ← elabTerm h none
  let hty : Q(Prop) ← inferType h
  let target : Q(Prop) ← goal.getType
  match hty, target with
  | ~q(0 < ($z : ℝ)), ~q(($a : ℝ) = $b) =>
    let hz : Q(0 < $z) := h
    let ⟨c,e,ha⟩ ← collect z hz a
    let ⟨d,f,hb⟩ ← collect z hz b
    let hc : Q($c = $d) ← mkFreshExprSyntheticOpaqueMVar q($c = $d)
    let he : Q($e = $f) ← mkFreshExprSyntheticOpaqueMVar q($e = $f)
    goal.assign q(same $ha $hb $hc $he)
    replaceMainGoal [hc.mvarId!,he.mvarId!]
    evalTactic (← `(tactic| all_goals (first | rfl | (ring; done) | (field_simp <;> ring))))
  | _, _ => throwError "rpow_ring expects a real equality and a proof that the base is positive"

end OAI.RpowArithmetic
