module

public import Chazelle.Golf

public import Chazelle.Core.RestoreNodeDec

/-!
# WP-E, the search: the leaf of the descent (mathematics)

At a leaf `2r + 1` above the target `T`, `r = T` (`leaf_target`); the good vertex (`Cα` walk
vertex `g' + dX`) is on the closed key interval of an arc of `T` (`arc_of_target`), so it is one of
the walk vertices the leaf visits on that arc: from the start edge, `arcCnt` steps
(`arc_int`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)

/-- The number of walk vertices the leaf visits on an arc from the start edge `se` to the end
edge `ee` (walk of length `N`); `w = 0` iff the start key is not below the end key. -/
def arcCnt (N se ee w : ℕ) : ℕ := (ee + N - se) % N + 1 + (if se = ee ∧ w = 0 then N else 0)

/-- **Every integer key on the closed arc is visited.** -/
theorem arc_int {N se ee w : ℕ} {a b : ℝ} (hse : se < N) (hee : ee < N) (ha0 : (se : ℝ) ≤ a)
    (ha1 : a < se + 1) (hb0 : (ee : ℝ) ≤ b) (hb1 : b < ee + 1) (hw : w = 0 ∨ a < b)
    {x : ℕ} (hx : x < N) (hc : ClosedArc a b x) :
    ∃ i, i < arcCnt N se ee w ∧ (se + i) % N = x := by
  refine ⟨(x + N - se) % N, ?_, ?_⟩
  swap
  · have : se + (x + N - se) % N ≡ x [MOD N] := by
      rw [Nat.ModEq, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show se + (x + N - se) = x + N by
        omega, Nat.add_mod_right]
    rw [this, Nat.mod_eq_of_lt hx]
  unfold arcCnt
  by_cases hsp : se = ee ∧ w = 0
  · rw [ite_eq_left hsp]
    have := Nat.mod_lt (x + N - se) (by omega : 0 < N)
    omega
  rw [ite_eq_right hsp]
  have hxa : ∀ y : ℕ, (y : ℝ) = a → y = se := fun y h => by
    have h1 : (se : ℝ) ≤ y := h ▸ ha0
    have h2 : (y : ℝ) < se + 1 := h ▸ ha1
    have h1' : se ≤ y := by exact_mod_cast h1
    have h2' : y < se + 1 := by exact_mod_cast h2
    omega
  have hxb : ∀ y : ℕ, (y : ℝ) = b → y = ee := fun y h => by
    have h1 : (ee : ℝ) ≤ y := h ▸ hb0
    have h2 : (y : ℝ) < ee + 1 := h ▸ hb1
    have h1' : ee ≤ y := by exact_mod_cast h1
    have h2' : y < ee + 1 := by exact_mod_cast h2
    omega
  rcases hc with hc | hc | hc
  · unfold sideInArc at hc
    split_ifs at hc with hab
    · -- a < x < b
      have h1 : se < x + 1 := by
        have : (se : ℝ) < x + 1 := by linarith [hc.1]
        exact_mod_cast this
      have h2 : x < ee + 1 := by
        have : (x : ℝ) < ee + 1 := by linarith [hc.2]
        exact_mod_cast this
      have h3 : se ≤ ee := by
        have : (se : ℝ) < ee + 1 := by linarith
        have : se < ee + 1 := by exact_mod_cast this
        omega
      rw [show x + N - se = (x - se) + N by omega, Nat.add_mod_right,
        show ee + N - se = (ee - se) + N by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · -- b ≤ a
      have hab' : ee ≤ se := by
        have : (ee : ℝ) < se + 1 := by linarith
        have : ee < se + 1 := by exact_mod_cast this
        omega
      have hne : ee ≠ se := by
        intro e; subst e
        rcases hw with hw | hw
        · exact hsp ⟨rfl, hw⟩
        · exact hab hw
      have hlt : ee < se := by omega
      rw [Nat.mod_eq_of_lt (by omega : ee + N - se < N)]
      rcases hc with hc | hc
      · have h1 : se ≤ x := by
          have : (se : ℝ) < x + 1 := by linarith
          have : se < x + 1 := by exact_mod_cast this
          omega
        rw [show x + N - se = (x - se) + N by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        omega
      · have h2 : x ≤ ee := by
          have : (x : ℝ) < ee + 1 := by linarith
          have : x < ee + 1 := by exact_mod_cast this
          omega
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
  · have := hxa x hc
    subst this
    simp
  · have := hxb x hc
    subst this
    have := Nat.mod_lt (x + N - se) (by omega : 0 < N)
    omega

/-- **The leaf above the target is the target.** -/
theorem leaf_target {N : NF} {d : ℕ} (hD : IsDecomp N d) {r T : ℕ} (hr : r < N.nRegions)
    (hT : T < N.nRegions) (hb : N.Below (2 * r + 1) T) : r = T :=
  (hD.2.2.2.2.2.2.2.1 r T hr hT hb).symm

variable {E : FEnv} {c₀ : Config} {Cα : Chain} {g g' L : ℕ}

/-- **The good vertex is on the closed arc of an arc record of the target.** -/
theorem arc_of_target (hGα : GoodModel (chainModel Cα)) {Nα : NF}
    (hNα : IsNF (chainModel Cα) (Qof E.P) Nα)
    {reg : ℕ → Set Point} {ai bi aj bj : ℝ} {dX : ℕ} {regα : ℕ → Set Point} {T : ℕ}
    (hD : DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T)
    (hXn : g' + dX < (chainModel Cα).W.n) :
    ∃ t, t < (Nα.region T).arcs.length ∧
      (Nα.region T).arcs.getD t 0 < Nα.arcs.length ∧
      ClosedArc ((chainModel Cα).key (Qof E.P) (Nα.arc ((Nα.region T).arcs.getD t 0)).s)
        ((chainModel Cα).key (Qof E.P) (Nα.arc ((Nα.region T).arcs.getD t 0)).e)
        ((g' + dX : ℕ) : ℝ) := by
  obtain ⟨hcorr, -, harcs, -⟩ := hD.hregsα
  have hFam := hNα.1
  obtain ⟨U, hU, a, b, harc, hcl, hev⟩ := arc_after hGα hFam hXn
  have hTU := hcorr.1 T hD.hT
  obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := ((hD.hfT.and hev).and (Ioo_mem_nhdsGT one_pos)).exists
  have hfU := harc.2.2.2.2.2.2 _ ε hXn h3.1 h3.2 h2
  have hUT : U = regα T := WalkAx.faces_unique hU hTU hfU h1
  subst hUT
  obtain ⟨j, hj, hjr, hjs, hje⟩ := harcs.2.2.1 T hD.hT a b harc
  have hmem : j ∈ (Nα.region T).arcs := (harcs.2.2.2 T hD.hT j).2 ⟨hj, hjr⟩
  obtain ⟨t, ht, htj⟩ := List.mem_iff_getElem.1 hmem
  have hget : (Nα.region T).arcs.getD t 0 = j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, htj]; rfl
  refine ⟨t, ht, by rw [hget]; exact hj, ?_⟩
  Ξ hget, hjs, hje
  exact hcl

end

end Restore

end Chazelle.Core
