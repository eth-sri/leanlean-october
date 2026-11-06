module

public import GradedNear.Cert.Relax

/-!
# Soundness of the certificate checker

If `checkLeaf L T = some v`, then every feasible point of the leaf LP has objective at most `v`,
and `v < S`. Ingredients: the row relaxations (`Relax.lean`), weak duality with signed costs and
the free dual of the second-family equality, the exclusion rule (all costs `≥ 0`, negative
budget), the enumeration of case vectors, the bisection tree (children partition the parent
box), and the root box `[0, end_k]`, which contains every admissible `τ_k·TS` because
`end_k² > d_k TS²/S`.

The helpers live in `GradedNear.Cert.SoundAux`:
* list bookkeeping: the entries of `colCosts` and `budgets` are the per-row `colCost` and
  `rowBudget` terms of `RelaxHolds`, and `zipWith` sums are `Finset.range` sums
  (`colCosts_getD`, `budgets_getD`, `sum_zipWith`);
* `caseValue_sound`: weak duality for one case, given the relaxed constraint of every row;
* `not_excludable`: an excluded case contradicts the relaxed constraints at `x ≥ 0`;
* `exists_caseVector`: the actual case vector (`2` for order `≠ 1`, the tangent case supplied by
  `relax_tangent` for order `1`) is one of `caseVectors orders`;
* `checkBox_spec`, `checkBox_sound`: every case vector passes the fold, so the box value bounds
  the objective;
* `verifyTree_sound`, `verifyTree_lt`: induction over the bisection tree, with the box invariants
  (length `= rows.length`, lower ends `≥ 0`, `τ_k·TS` in the box);
* `le_rootEnd`: the root box contains `τ_k·TS`.
-/

@[expose] public section

namespace GradedNear.Cert

namespace SoundAux

/-! ### Generic list lemmas -/

theorem getD_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) (d : δ) (d1 : α) (d2 : β) (d3 : γ)
    (l1 : List α) (l2 : List β) (l3 : List γ) (i : ℕ) (h1 : i < l1.length) (h2 : i < l2.length)
    (h3 : i < l3.length) :
    (List.zipWith3 f l1 l2 l3).getD i d = f (l1.getD i d1) (l2.getD i d2) (l3.getD i d3) := by
  induction l1 generalizing l2 l3 i <;> cases l2 <;> cases l3 <;> cases i <;>
    simp_all [List.zipWith3]

theorem length_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) (l1 : List α) (l2 : List β)
    (l3 : List γ) (h2 : l2.length = l1.length) (h3 : l3.length = l1.length) :
    (List.zipWith3 f l1 l2 l3).length = l1.length := by
  induction l1 generalizing l2 l3 <;> cases l2 <;> cases l3 <;> simp_all [List.zipWith3]

/-- A `zipWith` sum against the duals `Z` (coerced to `List ℤ` through the list monad) is a
`Finset.range` sum. -/
theorem sum_zipWith_cast : ∀ (Z : List ℕ) (l : List ℤ) {n : ℕ} {g : ℕ → ℤ}, Z.length = n →
    (l.length = n ∧ ∀ k < n, l.getD k 0 = g k) →
    (List.zipWith (fun z c => z * c) (Z >>= fun a => pure (a : ℤ)) l).sum =
      ∑ k ∈ Finset.range n, (Z.getD k 0 : ℤ) * g k
  | [], [], _, _, rfl, _ => by simp
  | a :: Z, b :: l, _, g, rfl, ⟨hl, hg⟩ => by
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ, ← sum_zipWith_cast Z l rfl ⟨by simpa using hl, fun k hk => hg (k + 1) (by simpa using hk)⟩, ← hg 0 (by simp)]
    simp [add_comm]
  | [], _ :: _, _, _, rfl, ⟨h, _⟩ | _ :: _, [], _, _, rfl, ⟨h, _⟩ => by simp at h

/-! ### Costs and budgets -/

/-- The entries of `colCosts` are the per-row costs of `RelaxHolds`. -/
theorem colCosts_spec {L : Leaf} (hwf : wellFormed L = true) (j : Fin L.cols.length)
    {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length) {cs : List ℕ}
    (hcs : cs.length = L.rows.length) :
    (colCosts (L.cols.get j) box cs).length = L.rows.length ∧ ∀ k < L.rows.length,
      (colCosts (L.cols.get j) box cs).getD k 0 = colCost ((L.cols.get j).v.getD k 0)
        ((L.cols.get j).D.getD k 1) (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) := by
  simp [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨hv, hD⟩ := (hwf.1 _ (List.getElem_mem j.2)).1
  refine ⟨(length_zipWith3 _ _ _ _ (by simp [hv, hD, hbox]) (by rw [hcs, hbox])).trans hbox,
    fun k hk => ?_⟩
  rw [colCosts, getD_zipWith3 _ _ (0, 0) (0, 1) 0 _ _ _ k (by omega) (by simp; omega)
    (by omega)]
  grind

/-- The entries of `budgets` are the per-row budgets of `RelaxHolds`. -/
theorem budgets_spec {L : Leaf} {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length)
    {cs : List ℕ} (hcs : cs.length = L.rows.length) :
    (budgets L box cs).length = L.rows.length ∧ ∀ k < L.rows.length,
      (budgets L box cs).getD k 0 = rowBudget (L.rows.getD k ⟨1, []⟩) (box.getD k (0, 0)).1
        (box.getD k (0, 0)).2 (cs.getD k 0) := by
  unfold budgets
  refine ⟨length_zipWith3 _ _ _ _ hbox hcs, fun k hk => ?_⟩
  rw [getD_zipWith3 _ _ ⟨1, []⟩ (0, 0) 0 _ _ _ k hk (by omega) (by omega)]

/-! ### Weak duality for one case -/

/-- Weak duality in real form: column inequalities, the linear constraints and the relaxed near
rows, combined with nonnegative multipliers (and a free one `Q` for the equality). -/
theorem weak_duality {m n : ℕ} (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j)
    (G W C NH E : Fin m → ℝ) (c : Fin m → ℕ → ℝ) (bud : ℕ → ℝ) (z : ℕ → ℝ) (hz : ∀ k, 0 ≤ z k)
    (Y V U Q F C0 N0 E0 DSr : ℝ) (hY : 0 ≤ Y) (hV : 0 ≤ V) (hU : 0 ≤ U)
    (hcol : ∀ j, DSr * G j ≤
      Y * W j + V * C j + U * NH j + Q * E j + ∑ k ∈ Finset.range n, z k * c j k)
    (hW : ∑ j, W j * x j ≤ F) (hC : ∑ j, C j * x j ≤ C0) (hNH : ∑ j, NH j * x j ≤ N0)
    (hE : ∑ j, E j * x j = E0) (hrel : ∀ k < n, ∑ j, c j k * x j ≤ bud k) :
    DSr * ∑ j, G j * x j ≤
      Y * F + V * C0 + U * N0 + Q * E0 + ∑ k ∈ Finset.range n, z k * bud k := by
  have h1 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hcol j) (hx j)
  have h2 := Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_left (hrel k (Finset.mem_range.mp hk)) (hz k)
  simp [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, ← Finset.mul_sum, hE]
    at h1 h2
  rw [Finset.sum_comm] at h1
  simp [← Finset.mul_sum] at h1
  linarith [mul_le_mul_of_nonneg_left hW hY, mul_le_mul_of_nonneg_left hC hV,
    mul_le_mul_of_nonneg_left hNH hU]

/-- From `DS · Σ G x ≤ T` to the certified value `⌈T / DS⌉ + first + final`. -/
theorem obj_le_of {L : Leaf} {x : Fin L.cols.length → ℝ} {T : ℤ}
    (h : ((DS : ℤ) : ℝ) * ∑ j, ((L.cols.get j).G : ℝ) * x j ≤ (T : ℝ)) :
    objective L x ≤ ((ceilDiv T DS + L.first + L.final : ℤ) : ℝ) := by
  have h2 : (T : ℝ) ≤ (DS : ℝ) * (ceilDiv T DS : ℝ) := by
    have := Int.ediv_mul_le (-T) (show DS ≠ 0 by norm_num [DS])
    exact_mod_cast (show T ≤ DS * ceilDiv T DS by unfold ceilDiv; linarith)
  have := le_of_mul_le_mul_left (h.trans h2) (by norm_num [DS])
  unfold objective
  grind

/-- Weak duality for one case: if the relaxed constraint of every row holds for the case vector
`cs`, then the value certified by the duals bounds the objective. -/
theorem caseValue_sound {L : Leaf} (hwf : wellFormed L = true) {box : List (ℤ × ℤ)}
    (hbox : box.length = L.rows.length) {cs : List ℕ} (hcs : cs.length = L.rows.length)
    {du : Duals} {v : ℤ} (hv : caseValue L box cs du = some v)
    {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ} (hfeas : Feasible L x τ)
    (hrel : ∀ k < L.rows.length,
      RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0)) :
    objective L x ≤ v := by
  obtain ⟨hx, hW, hC, hNH, hE, -⟩ := hfeas
  unfold caseValue at hv
  split_ifs at hv with hcond
  cases hv
  refine obj_le_of ((weak_duality x hx _ _ _ _ _ _ _ (fun k => ((du.Z.getD k 0 : ℕ) : ℝ))
    (fun k => Nat.cast_nonneg _) du.Y du.V du.U ((du.P : ℝ) - du.M) _ _ _ _ _ (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun j => ?_) hW hC hNH hE hrel).trans_eq ?_)
  · have h1 := of_decide_eq_true (List.all_eq_true.mp hcond.2 _ (List.get_mem _ j))
    rw [sum_zipWith_cast _ _ hcond.1 (colCosts_spec hwf j hbox hcs)] at h1
    exact_mod_cast h1
  · rw [sum_zipWith_cast _ _ hcond.1 (budgets_spec hbox hcs)]
    push_cast
    rfl

/-! ### Exclusion -/

/-- A case whose relaxed constraints all hold at some `x ≥ 0` is not excludable. -/
theorem not_excludable {L : Leaf} (hwf : wellFormed L = true) {box : List (ℤ × ℤ)}
    (hbox : box.length = L.rows.length) {cs : List ℕ} (hcs : cs.length = L.rows.length)
    {x : Fin L.cols.length → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hrel : ∀ k < L.rows.length,
      RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0)) :
    excludable L box cs ≠ true := by
  intro hex
  obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hex
  rw [List.mem_range] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, (budgets_spec hbox hcs).2 k hk] at hk'
  refine absurd (hrel k hk) (not_le.2 ((mod_cast hk'.1 : _ < (0 : ℝ)).trans_le
    (Finset.sum_nonneg fun j _ => mul_nonneg ?_ (hx j))))
  have := hk'.2 _ (List.get_mem _ j)
  rw [(colCosts_spec hwf j hbox hcs).2 k hk] at this
  exact_mod_cast this

/-! ### Case vectors -/

/-- If every row of order `1` satisfies `P k 0 ∨ P k 1` and every other row satisfies `P k 2`,
some case vector satisfies `P` in every row. -/
theorem exists_caseVector (P : ℕ → ℕ → Prop) (os : List ℕ)
    (h : ∀ k < os.length, (os.getD k 0 = 1 → P k 0 ∨ P k 1) ∧ (os.getD k 0 ≠ 1 → P k 2)) :
    ∃ cs ∈ caseVectors os, cs.length = os.length ∧ ∀ k < os.length, P k (cs.getD k 0) := by
  induction os generalizing P with
  | nil => simp [caseVectors]
  | cons o os ih =>
    obtain ⟨cs, hcs, hlen, hP⟩ := ih (fun k c => P (k + 1) c)
      (by grind)
    have h0 := h 0 (by simp)
    suffices ∃ c, P 0 c ∧ c :: cs ∈ caseVectors (o :: os) from
      let ⟨c, hc, hm⟩ := this
      ⟨c :: cs, hm, by grind, by grind⟩
    grind [caseVectors]

/-! ### The fold over cases -/

theorem foldl_some {α : Type*} (f : Option ℤ → α → Option ℤ) (Q : α → ℤ → Prop)
    (hf : ∀ acc a m, f acc a = some m → ∃ m0, acc = some m0 ∧ m0 ≤ m ∧ Q a m)
    (hQ : ∀ a m1 m2, Q a m1 → m1 ≤ m2 → Q a m2) (l : List α) :
    ∀ (init : Option ℤ) (m : ℤ), l.foldl f init = some m →
      (∃ m0, init = some m0 ∧ m0 ≤ m) ∧ ∀ a ∈ l, Q a m := by
  induction l with
  | nil => grind
  | cons a l ih =>
    intro init m h
    obtain ⟨⟨m1, hm1, hm1le⟩, hl⟩ := ih _ _ h
    obtain ⟨m0, rfl, hm0, hQa⟩ := hf _ _ _ hm1
    exact ⟨⟨m0, rfl, hm0.trans hm1le⟩, List.forall_mem_cons.2 ⟨hQ _ _ _ hQa hm1le, hl⟩⟩

/-- The box invariant of a row: the lower end is `≥ 0` and the box contains `τ_k·TS`. -/
def BoxInv (τ : ℕ → ℝ) (k : ℕ) (p : ℤ × ℤ) : Prop :=
  0 ≤ p.1 ∧ (p.1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ p.2

/-- The value of a node bounds the objective at every feasible point whose thresholds lie in the
node's box. -/
theorem checkBox_sound {L : Leaf} (hwf : wellFormed L = true) {box : List (ℤ × ℤ)}
    (hbox : box.length = L.rows.length) {orders : List ℕ} {certs : List CaseCert} {m : ℤ}
    (h : checkBox L box orders certs = some m) {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ}
    (hfeas : Feasible L x τ) (hτ : ∀ k < L.rows.length, BoxInv τ k (box.getD k (0, 0))) :
    objective L x ≤ m := by
  unfold checkBox at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hord, hlen, -⟩ := hc
  obtain ⟨cs, hcs, hcl, hrel⟩ := exists_caseVector
    (fun k c => RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 c) orders (by
      intro k hk
      rw [hord] at hk
      obtain ⟨h0, ha, hb⟩ := hτ k hk
      exact ⟨fun _ => relax_tangent L hwf x hfeas.1 ha hb (hfeas.2.2.2.2.2 k hk).2.2,
        fun _ => relax_first L hwf x hfeas.1 h0 ha hb (hfeas.2.2.2.2.2 k hk).2.2⟩)
  rw [hord] at hcl hrel
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcs
  have := (foldl_some _ (fun (cc : List ℕ × CaseCert) m => excludable L box cc.1 = true ∨
      ∃ du v, caseValue L box cc.1 du = some v ∧ v ≤ m) ?_ ?_ _ _ _ h).2 _
    (List.getElem_mem (show i < ((caseVectors orders).zip certs).length by grind))
  · rw [List.getElem_zip] at this
    rcases this with hex | ⟨du, v, hv, hvm⟩
    · exact absurd hex (not_excludable hwf hbox hcl hfeas.1 hrel)
    · exact (caseValue_sound hwf hbox hcl hv hfeas hrel).trans (mod_cast hvm)
  · rintro (_ | m0) ⟨cv, _ | du⟩ m' hf <;> simp at hf <;> grind
  · grind

/-! ### The bisection tree -/

/-- Induction over the tree: every node value is `< S`, and on a box of the right length
satisfying the invariants, the value of the tree bounds the objective. -/
theorem verifyTree_sound {L : Leaf} (hwf : wellFormed L = true) (T : Tree) :
    ∀ (box : List (ℤ × ℤ)) (m : ℤ), verifyTree L T box = some m → m < S ∧ ∀ x τ,
      Feasible L x τ → box.length = L.rows.length →
        (∀ k < L.rows.length, BoxInv τ k (box.getD k (0, 0))) → objective L x ≤ m := by
  induction T with
  | split k mid l r ihl ihr =>
    intro box m h
    simp [verifyTree] at h
    split at h
    · rename_i a b hk
      split_ifs at h with hab
      obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m2, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
      obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
      refine ⟨max_lt (ihl _ _ h1).1 (ihr _ _ h3).1, fun x τ hfeas hlen hτ => ?_⟩
      have hset : ∀ p, BoxInv τ k p → ∀ i < L.rows.length, BoxInv τ i ((box.set k p).getD i (0, 0)) :=
        fun p hp i hi => by grind
      obtain ⟨h0, ha, hb⟩ := hτ k (hlen ▸ hkl)
      rw [List.getD_eq_getElem _ _ hkl, hkv] at h0 ha hb
      rcases le_total (τ k * TS) mid with hmid | hmid
      · exact ((ihl _ _ h1).2 x τ hfeas (by simp [hlen]) (hset _ ⟨h0, ha, hmid⟩)).trans
          (mod_cast le_max_left ..)
      · exact ((ihr _ _ h3).2 x τ hfeas (by simp [hlen]) (hset _ ⟨h0.trans hab.1.le, hmid, hb⟩)).trans
          (mod_cast le_max_right ..)
    · grind
  | node orders certs =>
    intro box m h
    obtain ⟨v, hv, h'⟩ := Option.bind_eq_some_iff.mp h
    grind [checkBox_sound]

/-! ### The root box -/

/-- The root end contains every admissible threshold: `(τ·TS)² ≤ d TS²/S < ⌊d TS²/S⌋ + 1 ≤
rootEnd²`. -/
theorem le_rootEnd {d : ℤ} {t : ℝ} (htd : t ^ 2 ≤ (d : ℝ) / S) :
    t * TS ≤ rootEnd d := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have h1 := Int.lt_ediv_add_one_mul_self (d * TS * TS) hS
  have h2 := Int.self_le_toNat (d * TS * TS / S)
  have h3 : (d * TS * TS / S).toNat + 1 ≤ rootEnd d * rootEnd d := by
    unfold rootEnd isqrtUp
    split_ifs with h
    · exact_mod_cast h.ge
    · exact_mod_cast (Nat.lt_succ_sqrt _).le
  have h0 : (0 : ℝ) ≤ rootEnd d := by unfold rootEnd; positivity
  have hr : (d : ℝ) * TS * TS < rootEnd d * rootEnd d * S := by
    exact_mod_cast (by nlinarith)
  rw [le_div_iff₀ S_pos] at htd
  by_contra hc
  nlinarith [mul_lt_mul_of_pos_right (mul_self_lt_mul_self h0 (not_le.1 hc))
    S_pos, mul_le_mul_of_nonneg_right htd (sq_nonneg (TS : ℝ))]

end SoundAux

/-- **Soundness of the checker.** If `checkLeaf L T = some val`, then every feasible point of the
leaf LP (`Feasible`: real column values `x ≥ 0` and thresholds `τ`) has objective at most
`val`. -/
theorem checkLeaf_sound {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x ≤ val := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  refine (SoundAux.verifyTree_sound hwf T _ _ h).2 x τ hfeas (by simp [rootBox]) fun k hk => ?_
  obtain ⟨h0, hd, -⟩ := hfeas.2.2.2.2.2 k hk
  rw [rootBox, List.getD_eq_getElem _ _ (by grind), List.getElem_map]
  rw [List.getD_eq_getElem _ _ hk] at hd
  exact ⟨le_rfl, by push_cast; exact mul_nonneg h0 (by norm_num [TS]), SoundAux.le_rootEnd hd⟩

/-- The value of an accepted certificate is below `S`, since every tree node's value is checked
to be `< S`. -/
theorem checkLeaf_lt {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val) :
    val < S := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  exact (SoundAux.verifyTree_sound hwf T _ _ h).1

/-- A certified leaf: every feasible point has objective `< 1` (in units of `S`). -/
theorem certified {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x < S :=
  lt_of_le_of_lt (checkLeaf_sound h x τ hfeas) (mod_cast checkLeaf_lt h)

end GradedNear.Cert
