module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
import Mathlib.MeasureTheory.Measure.AddContent

public section

/-! # The diagonal form of Phillips' lemma

We work with real finitely additive charges on `ℕ`. The vector-valued result
uses norming functionals and only tests disjoint subfamily sums; in `ℓ∞` these
are the characteristic sequences of sets.
-/

open Filter Set Function Topology MeasureTheory
open scoped BigOperators

namespace Phillips

/-- Split the reservoir into disjoint infinite fibers. If none can be kept,
negative witnesses on all the fibers contradict the lower bound. -/
private theorem small_on_subsets (m : Set ℕ → ℝ)
    (ha : ∀ ⦃A B⦄, Disjoint A B → m (A ∪ B) = m A + m B)
    (hb : ∃ C, ∀ A, C ≤ m A) (S : Set ℕ) (hS : S.Infinite) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T ⊆ S, T.Infinite ∧ ∀ B ⊆ T, -δ ≤ m B := by
  classical
  let e := Nat.pairEquiv.toEmbedding.trans (hS.natEmbedding S)
  let g := e.trans (Function.Embedding.subtype _)
  by_contra! hn
  obtain ⟨C, hC⟩ := hb
  obtain ⟨N, hN⟩ := exists_nat_gt (-C / δ)
  choose B hB hlt using fun i : Fin N => hn (range fun j => g (i, j))
    (range_subset_iff.2 fun j => (e (i, j)).2)
    (infinite_range_of_injective fun _ _ h => congrArg Prod.snd (g.injective h))
  have hd : Pairwise (Disjoint on B) := fun i j hij =>
    (disjoint_range_iff.2 fun a b h => hij (Fin.ext (congrArg Prod.fst (g.injective h)))).mono (hB i) (hB j)
  have hring : IsSetRing (univ : Set (Set ℕ)) := by constructor <;> simp
  let M := hring.addContent_of_union m (by simpa using ha (A := ∅) (B := ∅) (by simp)) (fun _ _ h => ha h)
  have h := addContent_iUnion (m := M) (f := B) (by simp) hd (by simp)
  change m (⋃ i : Fin N, B i) = _ at h
  have hs := Finset.sum_le_card_nsmul Finset.univ (fun i => M (B i)) (-δ) fun i _ => (hlt i).le
  simp at hs
  linarith [(div_lt_iff₀ hδ).1 hN, hC (⋃ i : Fin N, B i)]

/-- The one-sided diagonal bound for bounded, finitely additive real charges. -/
theorem eventually_diagonal_lt (μ : ℕ → Set ℕ → ℝ)
    (ha : ∀ n ⦃A B⦄, Disjoint A B → μ n (A ∪ B) = μ n A + μ n B)
    (hb : ∀ n, ∃ C, ∀ A, C ≤ μ n A)
    (hμ : ∀ A, Tendsto (fun n => μ n A) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, μ n {n} < ε := by
  classical
  by_contra! hbad
  let D := {n | ε ≤ μ n {n}}
  have hD : D.Infinite := Nat.frequently_atTop_iff_infinite.1 hbad
  let δ := ε / 3
  have hδ : 0 < δ := by positivity
  let P := {s : Set ℕ // s.Infinite}
  -- At each step choose a bad row that is small on the previous indices,
  -- then thin the reservoir for that row.
  have step (F : Set ℕ) (s : P) : ∃ (n : ℕ) (t : P),
      n ∈ s.val ∧ -δ < μ n F ∧ t.val ⊆ s.val ∩ Ioi n ∧
      ∀ B ⊆ t.val, -δ ≤ μ n B := by
    have hf := Nat.frequently_atTop_iff_infinite.2 s.2
    obtain ⟨n, hn, hsmall⟩ := (hf.and_eventually ((hμ F).eventually_const_lt (neg_lt_zero.mpr hδ))).exists
    obtain ⟨t, ht, hti, hc⟩ := small_on_subsets (μ n) (ha n) (hb n) (s.val ∩ Ioi n)
      (by simpa [sdiff_eq] using s.2.sdiff (finite_Iic n)) hδ
    exact ⟨n, ⟨t, hti⟩, hn, hsmall, ht, hc⟩
  choose pick tail hmem hhead hsub htail using step
  let state : ℕ → Set ℕ × P := Nat.rec (∅, ⟨D, hD⟩)
    (fun _ p => (insert (pick p.1 p.2) p.1, tail p.1 p.2))
  let F (i : ℕ) := (state i).1
  let R (i : ℕ) := (state i).2.val
  let n (i : ℕ) := pick (F i) (state i).2
  have hnR (i) : n i ∈ R i := hmem (F i) (state i).2
  have hR (i) : R (i + 1) ⊆ R i ∩ Ioi (n i) := hsub (F i) (state i).2
  have hn : StrictMono n := strictMono_nat_of_lt_succ fun i => (hR i (hnR (i + 1))).2
  have hRa : Antitone R := antitone_nat_of_succ_le fun i _ hx => (hR i hx).1
  have hF (i : ℕ) : F i = n '' Iio i := by
    induction i with
    | zero => simp [F, state]
    | succ i ih =>
      rw [Iio_add_one_eq_Iic, ← Iio_insert, image_insert_eq, ← ih]
  obtain ⟨i, hi⟩ := (((hμ (range n)).comp hn.tendsto_atTop).eventually_lt_const hδ).exists
  have hTail : n '' Ioi i ⊆ R (i + 1) :=
    image_subset_iff.2 fun j hj => hRa (Nat.succ_le_of_lt hj) (hnR j)
  have hsplit : μ (n i) (range n) = μ (n i) {n i} + μ (n i) (F i) + μ (n i) (n '' Ioi i) := by
    rw [← image_univ, ← Iio_union_Ici (a := i + 1), image_union,
      ha _ (disjoint_image_of_injective hn.injective (by simp)), ← hF, Ici_add_one_eq_Ioi]
    change μ (n i) (insert (n i) (F i)) + _ = _
    rw [← singleton_union, ha _ (disjoint_singleton_left.2 (by simp [hF, hn.injective.mem_set_image]))]
  have h1 : -δ < μ (n i) (F i) := hhead (F i) (state i).2
  have h2 : -δ ≤ μ (n i) (n '' Ioi i) := htail (F i) (state i).2 _ hTail
  have h3 : ε ≤ μ (n i) {n i} := hRa (Nat.zero_le _) (hnR i)
  dsimp [δ] at h1 h2 hi
  linarith

variable {𝕜 E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The diagonal form of Phillips' lemma, for disjoint sums in a unit ball. -/
theorem norm_diagonal_tendsto_zero (P : Set ℕ → E) (hb : ∀ A, ‖P A‖ ≤ 1)
    (ha : ∀ ⦃A B⦄, Disjoint A B → P (A ∪ B) = P A + P B)
    (L : ℕ → E →L[𝕜] X) (hL : ∀ A, Tendsto (fun n => L n (P A)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖L n (P {n})‖) atTop (𝓝 0) := by
  choose φ hφ he using fun n => exists_dual_vector'' 𝕜 (L n (P {n}))
  let μ (n : ℕ) (A : Set ℕ) := RCLike.re (φ n (L n (P A)))
  have hm (n : ℕ) (A : Set ℕ) : ‖μ n A‖ ≤ ‖L n (P A)‖ := (RCLike.norm_re_le_norm _).trans
    (by simpa using (φ n).le_of_opNorm_le (hφ n) (L n (P A)))
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hl (n : ℕ) : ∃ C, ∀ A, C ≤ μ n A := ⟨-‖L n‖, fun A =>
    (abs_le.mp (by simpa [Real.norm_eq_abs] using (hm n A).trans ((L n).unit_le_opNorm _ (hb A)))).1⟩
  simpa [μ, he, Real.norm_of_nonneg (norm_nonneg _)] using eventually_diagonal_lt μ (fun n _ _ h => by simp [μ, ha h]) hl
    (fun A => squeeze_zero_norm (fun n => hm n A) (by simpa using (hL A).norm)) hε

end Phillips
