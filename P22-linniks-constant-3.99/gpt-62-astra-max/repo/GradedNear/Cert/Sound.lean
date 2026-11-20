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

-/

@[expose] public section

namespace GradedNear.Cert

namespace SoundAux

abbrev Box := List (ℤ × ℤ)

/-- A split or root interval is admissible if its lower end is nonnegative and
it contains the threshold, expressed in ticks. -/
def covers (p : ℤ × ℤ) (t : ℝ) := 0 ≤ p.1 ∧ (p.1 : ℝ) ≤ t * TS ∧ t * TS ≤ p.2

def admits (L : Leaf) (box : Box) (τ : ℕ → ℝ) := box.length = L.rows.length ∧
  ∀ k < L.rows.length, covers (box.getD k (0, 0)) (τ k)

/-! ### Reading a checked row vector by index -/

open List (ofFn zipWith zipWith3)
open Finset
variable {α β γ δ : Type*} {n : ℕ}

lemma ofFn_getD {xs : List α} (d : α) (h : xs.length = n) :
    ofFn (fun k : Fin n => xs.getD k d) = xs := by
  subst n; simp

lemma zip_ofFn (f : α → β → γ) (x : Fin n → α) (y : Fin n → β) :
    zipWith f (ofFn x) (ofFn y) = ofFn fun k => f (x k) (y k) := by
  apply List.ext_getElem <;> simp

lemma zip3_ofFn (f : α → β → γ → δ) (x : Fin n → α) (y : Fin n → β) (z : Fin n → γ) :
    zipWith3 f (ofFn x) (ofFn y) (ofFn z) = ofFn fun k => f (x k) (y k) (z k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ, List.zipWith3, ih]

section Rows
variable {L : Leaf} {box : Box} {cs : List ℕ}
abbrev costAt (col : Col) (box : Box) (cs : List ℕ) (k : ℕ) :=
  colCost (featureAt col k) (diagonalAt col k) (box.getD k (0,0)).1 (box.getD k (0,0)).2 (cs.getD k 0)
abbrev budgetAt (L : Leaf) (box : Box) (cs : List ℕ) (k : ℕ) :=
  rowBudget (L.row k) (box.getD k (0,0)).1 (box.getD k (0,0)).2 (cs.getD k 0)

variable (hwf : wellFormed L = true) (hbox : box.length = L.rows.length)
    (hcs : cs.length = L.rows.length)

include hwf hbox hcs in
lemma costs_eq {col : Col} (hc : col ∈ L.cols) :
    colCosts col box cs = ofFn fun k : Fin L.rows.length => costAt col box cs k := by
  simp [wellFormed] at hwf
  obtain ⟨⟨hv, hD⟩, -⟩ := hwf.1 col hc
  unfold colCosts
  conv_lhs => rw [← ofFn_getD (0,0) hbox, ← ofFn_getD 0 hv, ← ofFn_getD 1 hD, ← ofFn_getD 0 hcs]
  simp [List.zip_eq_zipWith, zip_ofFn, zip3_ofFn, costAt]

include hbox hcs in
lemma budgets_eq : budgets L box cs = ofFn fun k : Fin L.rows.length => budgetAt L box cs k := by
  unfold budgets
  conv_lhs => rw [← ofFn_getD ⟨1, []⟩ (rfl : L.rows.length = _), ← ofFn_getD (0,0) hbox, ← ofFn_getD 0 hcs]
  rw [zip3_ofFn]

/-! ### Weak duality and exclusion -/

variable {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ}
    (hrel : ∀ k < L.rows.length, RelaxHolds L x k (box.getD k (0,0)).1 (box.getD k (0,0)).2 (cs.getD k 0))

/-- From `DS · Σ G x ≤ T` to the certified value. -/
lemma objective_le {T : ℤ} (h : (DS : ℝ) * ∑ j, ((L.cols.get j).G : ℝ) * x j ≤ T) :
    objective L x ≤ ((ceilDiv T DS + L.first + L.final : ℤ) : ℝ) := by
  have hDS : (0 : ℤ) < DS := by norm_num [DS]
  have he := Int.ediv_mul_le (-T) hDS.ne'
  have hceil : (T : ℝ) ≤ DS * (ceilDiv T DS : ℝ) := by exact_mod_cast (show T ≤ DS * ceilDiv T DS by unfold ceilDiv; linarith)
  have := le_of_mul_le_mul_left (h.trans hceil) (by exact_mod_cast hDS)
  unfold objective; push_cast; linarith

include hwf hbox hcs hrel in
/-- Sum the column certificates against the primal weights and then apply the row
constraints. Only the multiplier of the equality constraint may have either sign. -/
lemma caseValue_sound {du : Duals} {v : ℤ} (hv : caseValue L box cs du = some v)
    (hfeas : Feasible L x τ) : objective L x ≤ v := by
  obtain ⟨hx, hW, hC, hNH, hE, -⟩ := hfeas
  unfold caseValue at hv
  split_ifs at hv with hc
  obtain ⟨hZ, hcols⟩ := hc
  obtain rfl := Option.some.inj hv
  have dot (y : Fin L.rows.length → ℤ) :
      (zipWith (· * ·) (du.Z >>= fun a => pure (a : ℤ)) (ofFn y)).sum =
        ∑ k : Fin L.rows.length, (du.Z.getD k 0 : ℤ) * y k := by
    conv_lhs => rw [bind_pure_comp, ← ofFn_getD 0 hZ, List.map_eq_map, List.map_ofFn, zip_ofFn]
    simp [List.sum_ofFn]
  have col j := of_decide_eq_true (List.all_eq_true.mp hcols _ (List.get_mem L.cols j))
  simp only [costs_eq hwf hbox hcs (List.get_mem _ _), dot] at col
  have hcol j := (Int.cast_le (R := ℝ)).mpr (col j)
  push_cast at hcol
  apply objective_le
  rw [budgets_eq hbox hcs, dot]; push_cast
  rw [Finset.mul_sum]; simp_rw [← mul_assoc (DS : ℝ)]
  grw [hcol] <;> try apply hx
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, ← Finset.mul_sum, hE]
  rw [Finset.sum_comm (s := (univ : Finset (Fin L.cols.length))) (t := (univ : Finset (Fin L.rows.length)))]
  simp_rw [← Finset.mul_sum]
  bound

include hwf hbox hcs hrel in
/-- If every cost in the selected row is nonnegative, its negative budget contradicts feasibility. -/
lemma not_excludable (hx : ∀ j, 0 ≤ x j) : excludable L box cs ≠ true := by
  simp only [excludable, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, ne_eq, not_exists, not_and]
  intro k hk hneg hc
  simp [budgets_eq hbox hcs, hk] at hneg
  have hnn j : (0:ℝ) ≤ costAt (L.cols.get j) box cs k := by
    have h := hc _ (List.get_mem L.cols j)
    rw [costs_eq hwf hbox hcs (List.get_mem _ j)] at h
    aesop
  exact (by exact_mod_cast hneg : (budgetAt L box cs k : ℝ) < 0).not_ge ((sum_nonneg fun j _ => mul_nonneg (hnn j) (hx j)).trans (hrel k hk))

end Rows

/-! ### Case vectors -/

/-- If every row of order `1` satisfies `P k 0 ∨ P k 1` and every other row satisfies `P k 2`,
some case vector satisfies `P` in every row. -/
theorem exists_caseVector (P : ℕ → ℕ → Prop) (os : List ℕ)
    (h : ∀ k < os.length, (P k 0 ∨ P k 1) ∧ P k 2) :
    ∃ cs ∈ caseVectors os, cs.length = os.length ∧ ∀ k < os.length, P k (cs.getD k 0) := by
  induction os generalizing P with
  | nil => simp [caseVectors]
  | cons o os ih =>
    obtain ⟨cs, hcs, hlen, hP⟩ := ih (fun k c => P (k + 1) c)
      (fun k hk => by aesop)
    have chooseHead : ∃ c, (c :: cs) ∈ caseVectors (o :: os) ∧ P 0 c := by
      by_cases ho : o = 1 <;> simp [caseVectors, ho, hcs] <;> aesop
    obtain ⟨c, hc, hp⟩ := chooseHead
    refine ⟨c :: cs, hc, by simp [hlen], fun k hk => ?_⟩
    cases k <;> aesop

/-! ### The fold over cases -/

/-- An item establishes a fold invariant if its step establishes the invariant
for any accumulator and all later steps preserve it. -/
lemma foldl_member {f : β → α → β} {l : List α} {a : α} {P : β → Prop} (ha : a ∈ l)
    (hit : ∀ b, P (f b a)) (keep : ∀ b, P b → ∀ c, P (f b c)) (init : β) : P (l.foldl f init) := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem ha
  rw [List.foldl_append, List.foldl_cons]
  exact v.foldlRecOn f (hit _) fun b hb c _ => keep b hb c

/-- The value of a node bounds the objective at every feasible point whose thresholds lie in the
node's box. -/
theorem checkBox_sound {L : Leaf} (hwf : wellFormed L = true) {box : Box}
    {orders : List ℕ} {certs : List CaseCert} {m : ℤ} (h : checkBox L box orders certs = some m)
    {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ} (hfeas : Feasible L x τ)
    (hadm : admits L box τ) : objective L x ≤ m := by
  obtain ⟨hbox, hτ⟩ := hadm
  unfold checkBox at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hord, hcount, -⟩ := hc
  have hx := hfeas.1
  obtain ⟨cs, hcs, hlen, hrel⟩ := exists_caseVector
    (fun k c => RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 c) orders (by
      intro k hk
      rw [hord] at hk
      obtain ⟨-, -, hr⟩ := (hfeas.2.2.2.2.2) k hk
      obtain ⟨h0, ha, hb⟩ := hτ k hk
      exact RelaxAux.row_relaxations L hwf x k hx h0 ha hb hr)
  rw [hord] at hlen hrel
  rw [← List.map_fst_zip hcount.ge] at hcs
  obtain ⟨⟨cv, cc⟩, hmem, rfl⟩ := List.mem_map.mp hcs
  have hex := not_excludable hwf hbox hlen hrel hx
  have dual {du v} (hv : caseValue L box cv du = some v) := caseValue_sound hwf hbox hlen hrel hv hfeas
  apply foldl_member (P := fun acc : Option ℤ => ∀ v, acc = some v → objective L x ≤ v) hmem ?_ ?_ _ m h
  · intro b v hv
    cases b <;> cases cc <;> simp_all; aesop
  · rintro b hb ⟨c, cc⟩ v hv
    cases b <;> cases cc <;> simp_all; aesop

/-! ### The bisection tree -/

theorem getD_set_of_lt {box : Box} {k : ℕ} (hk : k < box.length) (p : ℤ × ℤ) (i : ℕ) :
    (box.set k p).getD i (0, 0) = if i = k then p else box.getD i (0, 0) := by
  by_cases hi : i = k
  · subst hi
    simp [hk]
  · simp [Ne.symm hi, hi]

/-- Both invariants of a successful tree, proved in the same traversal. -/
theorem verifyTree_spec {L : Leaf} (hwf : wellFormed L = true) (T : Tree) {box : Box} {m : ℤ}
    (h : verifyTree L T box = some m) : m < S ∧
    ∀ {x τ}, Feasible L x τ → admits L box τ → objective L x ≤ m := by
  induction T generalizing box m with
  | node orders certs =>
    obtain ⟨v, hv, hv'⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at hv' with hs
    cases hv'
    exact ⟨hs, fun hf hb => checkBox_sound hwf hv hf hb⟩
  | split k mid l r ihl ihr =>
    simp [verifyTree] at h
    split at h <;> try contradiction
    rename_i a b hk
    split_ifs at h with hab
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h₁, hl⟩ := ihl hu
    obtain ⟨h₂, hr⟩ := ihr hv
    refine ⟨max_lt h₁ h₂, fun {x τ} hf ⟨hlen, hτ⟩ => ?_⟩
    obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
    have hp := hτ k (hlen ▸ hkl)
    rw [List.getD_eq_getElem _ _ hkl, hkv] at hp
    have child (p : ℤ × ℤ) (hc : covers p (τ k)) : admits L (box.set k p) τ := by
      refine ⟨by simpa, fun i hi => ?_⟩
      rw [getD_set_of_lt hkl]; bound
    rcases le_total (τ k * TS) (mid : ℝ) with hmid | hmid
    · exact (hl hf (child _ ⟨hp.1, hp.2.1, hmid⟩)).trans (by simp)
    · exact (hr hf (child _ ⟨hp.1.trans hab.1.le, hmid, hp.2.2⟩)).trans (by simp)

/-! ### The root box -/

theorem isqrtUp_sq (n : ℕ) : n ≤ isqrtUp n * isqrtUp n := by
  unfold isqrtUp
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt n).le

/-- The root end contains every admissible threshold: `(τ·TS)² ≤ d TS²/S < ⌊d TS²/S⌋ + 1 ≤
rootEnd²`. -/
theorem le_rootEnd {d : ℤ} {t : ℝ} (htd : t ^ 2 ≤ (d : ℝ) / S) : t * TS ≤ rootEnd d := by
  let q := d * TS * TS / S
  let r := isqrtUp (q.toNat + 1)
  have h : (d : ℝ) * TS * TS < ((q : ℝ) + 1) * S := by
    exact_mod_cast Int.lt_ediv_add_one_mul_self (d * TS * TS) RelaxAux.S_pos_int
  have hq : (q : ℝ) ≤ q.toNat := by exact_mod_cast Int.self_le_toNat q
  have hr : (q.toNat : ℝ) + 1 ≤ (r : ℝ) * r := by exact_mod_cast isqrtUp_sq (q.toNat+1)
  change t * TS ≤ (r : ℝ)
  norm_num [S, TS] at h htd ⊢
  nlinarith

theorem rootBox_getD {L : Leaf} {k : ℕ} (hk : k < L.rows.length) :
    (rootBox L).getD k (0, 0) = (0, rootEnd (L.row k).d) := by
  unfold rootBox Leaf.row
  aesop

end SoundAux

variable {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ)

include h hfeas in
/-- **Soundness of the checker.** If `checkLeaf L T = some val`, then every feasible point of the
leaf LP (`Feasible`: real column values `x ≥ 0` and thresholds `τ`) has objective at most
`val`. -/
theorem checkLeaf_sound :
    objective L x ≤ val := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  apply (SoundAux.verifyTree_spec hwf T h).2 hfeas
  refine ⟨by simp [rootBox], fun k hk => ?_⟩
  rw [SoundAux.rootBox_getD hk]
  obtain ⟨h0, hd, -⟩ := hfeas.2.2.2.2.2 k hk
  exact ⟨le_rfl, by simpa using mul_nonneg h0 RelaxAux.TS_pos.le, SoundAux.le_rootEnd hd⟩

include h in
/-- The value of an accepted certificate is below `S`, since every tree node's value is checked
to be `< S`. -/
theorem checkLeaf_lt :
    val < S := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  exact (SoundAux.verifyTree_spec hwf T h).1

include h hfeas in
/-- A certified leaf: every feasible point has objective `< 1` (in units of `S`). -/
theorem certified :
    objective L x < S :=
  lt_of_le_of_lt (checkLeaf_sound h x τ hfeas) (by exact_mod_cast checkLeaf_lt h)

end GradedNear.Cert
