module

public import Chazelle.Core.SpecPhases

/-!
# The grade context has local capacity

`gradeCtx O` reads its capacity `2^(m h - 1)` at the handle `h`; a robust grade record at `h`
below `A` forces `h < A` (otherwise a memory changing `m h` beyond `topGrade n + 1` would break
it), so the capacity is local (`MemCtx.CapLocal`, review finding E4).
-/

namespace Chazelle.Core

@[expose] public section

/-- A robust grade record at `h` below `A` lies partly below `A`: `h < A`. -/
theorem gradeRaw_handle_lt {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {h A : ℕ}
    (hR : Robust A m fun m' => GradeRaw O P m' h A) : h < A := by
  by_contra hA
  push Not at hA
  have := (hR (Function.update m h (topGrade P.n + 2)) fun a ha => by
    rw [Function.update_of_ne (by omega)]).1
  rw [Function.update_self] at this
  omega

/-- **The grade context has local capacity.** -/
theorem gradeCtx_capLocal (O : OracleIface) : (gradeCtx O).CapLocal := by
  intro P m m' g A hmm' hh
  have hlt := gradeRaw_handle_lt (O := O) hh
  show 2 ^ (m' g - 1) = 2 ^ (m g - 1)
  rw [hmm' g hlt]

end

end Chazelle.Core
