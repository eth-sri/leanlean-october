
import GradedNear.Cert.Relax
import GradedNear.Tactics

/-!
# Soundness of the certificate checker

If `checkLeaf L T = some v`, then every feasible point of the leaf LP has objective at most `v`,
and `v < S`. Ingredients: the row relaxations (`Relax.lean`), weak duality with signed costs and
the free dual of the second-family equality, the exclusion rule (all costs `≥ 0`, negative
budget), the enumeration of case vectors, the bisection tree (children partition the parent
box), and the root box `[0, end_k]`, which contains every admissible `τ_k·TS` because
`end_k² > d_k TS²/S`.

The proof uses list bookkeeping (`colCosts_getD`, `budgets_getD`, `sum_zipWith`),
case-vector enumeration (`exists_caseVector`), and the fold invariant (`foldl_some`).
Weak duality and the exclusion contradiction are local to the node case of
`verifyTree_spec`; `le_rootEnd` supplies the root-box invariant.
-/

namespace GradedNear.Cert

namespace SoundAux

variable {L : Leaf} (hwf : wellFormed L = true) {col : Col} (hcol : col ∈ L.cols) {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length) {cs : List ℕ} (hcs : cs.length = L.rows.length)

/-! ### Generic list lemmas -/

@[simp] theorem zipWith3_eq {α β γ δ : Type*} (f : α → β → γ → δ)
    (l1 : List α) (l2 : List β) (l3 : List γ) :
    List.zipWith3 f l1 l2 l3 = List.zipWith (fun a bc => f a bc.1 bc.2) l1 (l2.zip l3) :=
  (List.zipWith_zipWith_right (fun a bc => f a bc.1 bc.2) Prod.mk l1 l2 l3).symm

theorem sum_zipWith (l1 l2 : List ℤ) (hlen : l2.length = l1.length) :
    (List.zipWith (· * ·) l1 l2).sum = ∑ k ∈ Finset.range l1.length, l1.getD k 0 * l2.getD k 0 := by
  induction l1 generalizing l2 with
  | nil => simp_all
  | cons a l1 ih => cases l2 <;> simp_all [Finset.sum_range_succ', add_comm]

/-! ### Well-formedness, costs and budgets -/

include hwf hcol in
theorem wf_col :
    col.v.length = L.rows.length ∧ col.D.length = L.rows.length := by
  simp_all only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] <;> grind

include hwf hcol hbox hcs in
/-- Entry `k` of `colCosts` is the cost of the column in row `k`, as in `RelaxHolds`. -/
theorem colCosts_getD {k : ℕ} (hk : k < L.rows.length) :
    (colCosts col box cs).getD k 0 = colCost (col.v.getD k 0) (col.D.getD k 1)
      (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) := by
  obtain ⟨hv, hD⟩ := wf_col hwf hcol
  simp_all [colCosts]

include hbox hcs in
/-- Entry `k` of `budgets` is the budget of row `k`, as in `RelaxHolds`. -/
theorem budgets_getD {k : ℕ} (hk : k < L.rows.length) :
    (budgets L box cs).getD k 0 = rowBudget (L.row k) (box.getD k (0, 0)).1
      (box.getD k (0, 0)).2 (cs.getD k 0) := by
  simp_all [budgets, Leaf.row]

/-! ### Weak duality for one case -/

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
       fun k hk => by grind
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have hext : ∀ c, P 0 c → ∀ k < (o :: os).length, P k ((c :: cs).getD k 0) := by grind
    by_cases ho : o = 1
    · rcases h0.1 ho with hp | hp <;>
        refine ⟨_ :: cs, ?_, by simp_all, hext _ hp⟩ <;> simp [caseVectors, ho, hcs]
    · exact ⟨2 :: cs, by simp [caseVectors, ho, hcs], by simp_all, hext 2 (h0.2 ho)⟩

/-! ### The fold over cases -/

theorem foldl_some {α : Type*} (f : Option ℤ → α → Option ℤ) (Q : α → ℤ → Prop)
    (hf : ∀ acc a m, f acc a = some m → ∃ m0, acc = some m0 ∧ m0 ≤ m ∧ Q a m)
    (hQ : ∀ a m1 m2, Q a m1 → m1 ≤ m2 → Q a m2) (l : List α) :
    ∀ (init : Option ℤ) (m : ℤ), l.foldl f init = some m →
      (∃ m0, init = some m0 ∧ m0 ≤ m) ∧ ∀ a ∈ l, Q a m := by
  induction l with
  | nil => simp_all
  | cons a l ih =>
    intro init m h
    obtain ⟨⟨m1, hm1, hm1le⟩, hl⟩ := ih _ _ h
    obtain ⟨m0, hinit, hm0, hQa⟩ := hf _ _ _ hm1
    have := hQ a _ _ hQa hm1le
    grind

/-! ### The bisection tree -/

include hwf in
/-- Induction over the tree: on a box of the right length with nonnegative lower ends that
contains every `τ_k·TS`, the value of the tree bounds the objective. -/
theorem verifyTree_spec (T : Tree) :
    ∀ (box : List (ℤ × ℤ)) (m : ℤ), verifyTree L T box = some m →
      m < S ∧ ∀ {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ}, Feasible L x τ →
        (box.length = L.rows.length ∧
  (∀ k < L.rows.length, 0 ≤ (box.getD k (0, 0)).1) ∧
  ∀ k < L.rows.length,
    ↑ (box.getD k (0, 0)).1 ≤ τ k * TS ∧ τ k * TS ≤ (box.getD k (0, 0)).2) →
        objective L x ≤ m := by
  induction T with
  | split k mid l r ihl ihr =>
    intro box m h
    simp [verifyTree] at h
    split at h
    · rename_i a b hk
      split_ifs at h with hab
      obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m2, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
      obtain ⟨hl1, hs1⟩ := ihl _ _ h1
      obtain ⟨hl2, hs2⟩ := ihr _ _ h3
      refine ⟨max_lt hl1 hl2, ?_⟩
      intro x τ hfeas hb
      obtain ⟨hlen, hlo, hτ⟩ := hb
      have ha0 : 0 ≤ a := by grind
      by_cases hmid : τ k * TS ≤ ↑mid
      · exact (hs1 hfeas (by grind)).trans (by bound)
      · have hmid' := (not_le.mp hmid).le
        exact (hs2 hfeas (by grind)).trans (by bound)
    · simp at h
  | node orders certs =>
    intro box m h

    obtain ⟨v, hv, h'⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h' with hvS
    cases h'
    refine ⟨hvS, ?_⟩
    intro x τ hfeas hb
    obtain ⟨hbox, hlo, hτ⟩ := hb
    unfold checkBox at hv
    dsimp only at hv
    split_ifs at hv with hc
    obtain ⟨hord, hcerts, -⟩ := hc
    have hx := hfeas.1

    obtain ⟨cs, hcs, hlen, hrel⟩ := exists_caseVector
      (fun k c => RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 c) orders (by
        intro k hk
        rw [hord] at hk
        obtain ⟨-, -, hr⟩ :=  hfeas.2.2.2.2.2  k hk
        obtain ⟨ha, hb⟩ := hτ k hk
        exact ⟨fun _ => relax_tangent L hwf x hx ha hb hr,
          fun _ => relax_first L hwf x hx (hlo k hk) ha hb hr⟩)
    rw [hord] at hlen hrel
    have obj_le_of {T : ℤ}
        (h : ↑DS * ∑ j, ↑ (L.col j).G * x j ≤ ↑T) :
        objective L x ≤ ((ceilDiv T DS + L.first + L.final : ℤ) : ℝ) := by
      have h2 : ↑T ≤ ↑DS * (ceilDiv T DS : ℝ) := by
        have := Int.ediv_mul_le (-T) (by decide : DS ≠ 0)
        unfold ceilDiv
        norm_cast
        linarith
      norm_num [DS, objective] at h h2 ⊢
      linarith

    have case_sound {du : Duals} {v : ℤ} (hv : caseValue L box cs du = some v)
         :
        objective L x ≤ v := by
      obtain ⟨hx, hW, hC, hNH, hE, -⟩ := hfeas
      unfold caseValue at hv
      split_ifs at hv with hcond
      rw [bind_pure_comp, List.map_eq_map] at hv hcond
      obtain ⟨hZ, hcols⟩ := hcond
      have hZm : (du.Z.map (Nat.cast : ℕ → ℤ)).length = L.rows.length := by simp_all
      obtain rfl := Option.some.inj hv
      apply obj_le_of
      rw [sum_zipWith _ _ (by simp [budgets, hbox, hlen, hZ]), hZm]
      have hcol (j : Fin L.cols.length) := by
        have hmem : L.col j ∈ L.cols := by simp_all
        obtain ⟨hv, hD⟩ := wf_col hwf hmem
        simp only [List.get_eq_getElem] at hv hD
        have h1 := List.all_eq_true.mp hcols _ hmem
        rw [decide_eq_true_eq, sum_zipWith _ _
          (by simp [colCosts, hv, hD, hbox, hlen, hZ]), hZm] at h1
        simp only [← Int.natCast_zero, List.getD_map] at h1
        exact (Int.cast_le (R := ℝ)).mpr h1
      push_cast at hcol
      simp only [← Int.natCast_zero, List.getD_map]
      push_cast
      have key := Finset.sum_le_sum (s := Finset.univ)
         fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hx j)
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc] at key
      rw [Finset.sum_comm] at key
      simp only [← Finset.mul_sum] at key
      refine key.trans ?_
      rw [hE]
      gcongr with k hk
      replace hk := Finset.mem_range.1 hk
      simpa only [RelaxHolds, colCosts_getD hwf (List.get_mem _ _) hbox hlen hk,
        budgets_getD hbox hlen hk] using hrel k hk

    have key := foldl_some _ (fun (cc : List ℕ × CaseCert) m =>
        excludable L box cc.1 = true ∨ ∃ du v, caseValue L box cc.1 du = some v ∧ v ≤ m)
      ?_ ?_ _ _ _ hv
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcs
      have hi' : i < ((caseVectors orders).zip certs).length := by simp_all
      have hcv := key.2 _ (List.getElem_mem hi')
      simp only [List.getElem_zip] at hcv
      rcases hcv with hex | ⟨du, v, hv, hvm⟩
      · exfalso
        obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hex
        rw [List.mem_range] at hk
        rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk'
        obtain ⟨hneg, hcost⟩ := hk'
        rw [budgets_getD hbox hlen hk] at hneg



        exact not_lt_of_ge ((Finset.sum_nonneg (s := Finset.univ) fun (j : Fin L.cols.length) _ => by
          have hmem : L.col j ∈ L.cols := by simp_all
          have h1 := hcost _ hmem
          rw [decide_eq_true_eq, colCosts_getD hwf hmem hbox hlen hk] at h1
          grind [mul_nonneg, Int.cast_nonneg]
        ).trans (hrel k hk)) (by exact_mod_cast hneg)
      · exact (case_sound hv).trans (by simp_all)
    · intro acc cc m' hf
      cases acc with
      | none => simp_all
      | some m0 =>
        rcases cc with ⟨cv, cert⟩
        cases cert with
        | excluded => simp_all
        | duals du => aesop
    grind

/-! ### The root box -/

/-- The root end contains every admissible threshold: `(τ·TS)² ≤ d TS²/S < ⌊d TS²/S⌋ + 1 ≤
rootEnd²`. -/
theorem le_rootEnd {d : ℤ} {t : ℝ} (ht : 0 ≤ t) (htd : t ^ 2 ≤ unscale d) :
    t * TS ≤ rootEnd d := by

  have h2 : d * TS * TS / S + 1 ≤ rootEnd d * rootEnd d := by
    refine (Int.add_le_add_right (Int.self_le_toNat _) 1).trans ?_
    unfold rootEnd
    norm_cast
    unfold isqrtUp
    split_ifs with h
    · simp_all
    · exact (Nat.lt_succ_sqrt _).le
  have h3 := (Int.lt_ediv_add_one_mul_self (d * TS * TS) RelaxAux.S_pos_int).trans_le (mul_le_mul_of_nonneg_right h2 RelaxAux.S_pos_int.le)
  have h3r : ↑d * TS * TS < (rootEnd d : ℝ) * rootEnd d * S := by exact_mod_cast h3
  have h4 := (le_div_iff₀ RelaxAux.S_pos).mp htd
  have hr : (0 : ℝ) ≤ rootEnd d := by unfold rootEnd; positivity
  norm_num [S, TS] at h3r h4 ⊢
  nlinarith

end SoundAux

variable {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
  (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ)

include h hfeas

/-- **Soundness of the checker.** If `checkLeaf L T = some val`, then every feasible point of the
leaf LP (`Feasible`: real column values `x ≥ 0` and thresholds `τ`) has objective at most
`val`. -/
theorem checkLeaf_sound :
    objective L x ≤ val := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  refine (SoundAux.verifyTree_spec hwf T _ _ h).2 hfeas ⟨by simp [rootBox], ?_, ?_⟩
  · intro k hk
    simp [rootBox, hk]
  · intro k hk
    obtain ⟨h0, hd, -⟩ := hfeas.2.2.2.2.2 k hk
    simpa [rootBox, Leaf.row, hk] using
      And.intro (mul_nonneg h0 (by norm_num [TS])) (SoundAux.le_rootEnd h0 hd)

omit hfeas in
/-- The value of an accepted certificate is below `S`, since every tree node's value is checked
to be `< S`. -/
theorem checkLeaf_lt :
    val < S := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  exact (SoundAux.verifyTree_spec hwf T _ _ h).1

/-- A certified leaf: every feasible point has objective `< 1` (in units of `S`). -/
theorem certified :
    objective L x < S :=
  lt_of_le_of_lt (checkLeaf_sound h x τ hfeas) (by exact_mod_cast checkLeaf_lt h)

end GradedNear.Cert
