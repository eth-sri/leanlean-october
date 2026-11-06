module

public import Chazelle.Core.SpecBase

/-!
# WP-J, part 3: coarsening (finding J1)

A `γ'`-granular submap is `γ`-semigranular for every `γ ≥ γ'`, so the short last chain of a grade
can be coarsened from the canonical submap of the previous grade by granularity enforcement.
-/

namespace Chazelle.Core

@[expose] public section

namespace Model

variable (M : Model)

/-- Semigranularity is monotone in `γ`. -/
theorem Semigranular.mono {F : Set (Set Point)} {γ γ' : ℕ} (h : M.Semigranular F γ)
    (hγ : γ ≤ γ') : M.Semigranular F γ' := fun U hU => (h U hU).trans hγ

/-- **A `γ`-granular submap is `γ'`-semigranular for `γ ≤ γ'`.** -/
theorem Granular.semigranular_of_le {F : Set (Set Point)} {γ γ' : ℕ} (h : M.Granular F γ)
    (hγ : γ ≤ γ') : M.Semigranular F γ' :=
  Semigranular.mono M h.1 hγ

end Model

end

end Chazelle.Core
