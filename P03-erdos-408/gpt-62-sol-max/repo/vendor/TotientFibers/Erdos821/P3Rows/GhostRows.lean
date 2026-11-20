module

public import Erdos821.S2.GhostTasks
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Data.Finset.Interval
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph
attribute [local instance] Classical.propDecidable

universe u v

private def PiProdTsumProp (ι : Type u) [Fintype ι] : Prop :=
  ∀ (β : ι → Type v) (f : (i : ι) → β i → ℝ),
    (∀ i x, 0 ≤ f i x) → (∀ i, Summable (f i)) →
      Summable (fun x : (i : ι) → β i => ∏ i, f i (x i)) ∧
        (∑' x : (i : ι) → β i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x

set_option maxHeartbeats 1000000 in
private theorem piProdTsum {ι : Type u} [Fintype ι]
    (β : ι → Type v) (f : (i : ι) → β i → ℝ)
    (h0 : ∀ i x, 0 ≤ f i x) (hs : ∀ i, Summable (f i)) :
    Summable (fun x : (i : ι) → β i => ∏ i, f i (x i)) ∧
      (∑' x : (i : ι) → β i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x := by
  classical
  refine Fintype.induction_empty_option
    (P := PiProdTsumProp) ?_ ?_ ?_ ι β f h0 hs
  · intro α γ _ e h γfam g hg0 hgs
    let : Fintype α := Fintype.ofEquiv γ e.symm
    let αfam : α → Type v := fun a => γfam (e a)
    let g' := fun a x => g (e a) x
    have hα := h αfam g' (by intro a x; exact hg0 (e a) x)
      (by intro a; exact hgs (e a))
    let E : ((b : γ) → γfam b) ≃ ((a : α) → αfam a) :=
      Equiv.piCongrLeft' γfam e.symm
    have hcomp : Summable (fun x : (b : γ) → γfam b =>
        ∏ a : α, g' a (E x a)) := (E.summable_iff).2 hα.1
    have hterm (x : (b : γ) → γfam b) :
        (∏ a : α, g' a (E x a)) = ∏ b : γ, g b (x b) := by
      apply Fintype.prod_equiv e
      intro a
      rfl
    constructor
    · convert hcomp using 1
      funext x
      exact (hterm x).symm
    · calc
        (∑' x : (b : γ) → γfam b, ∏ b : γ, g b (x b)) =
            ∑' x : (b : γ) → γfam b, ∏ a : α, g' a (E x a) := by
              apply tsum_congr
              intro x
              exact (hterm x).symm
        _ = ∑' y : (a : α) → αfam a, ∏ a : α, g' a (y a) :=
              E.tsum_eq (fun y : (a : α) → αfam a => ∏ a : α, g' a (y a))
        _ = ∏ a : α, ∑' x : αfam a, g' a x := hα.2
        _ = ∏ b : γ, ∑' x : γfam b, g b x := by
              apply Fintype.prod_equiv e
              intro a
              rfl
  · intro β f h0 hs
    have hfin : Summable (fun x : (i : PEmpty) → β i => ∏ i, f i (x i)) :=
      summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
    constructor
    · exact hfin
    · simp [tsum_fintype]
  · intro α _ ih β f h0 hs
    let β' : α → Type v := fun a => β (some a)
    let f' := fun a x => f (some a) x
    have hrest := ih β' f' (by intro a x; exact h0 (some a) x)
      (by intro a; exact hs (some a))
    let rest : ((a : α) → β (some a)) → ℝ := fun y => ∏ a, f' a (y a)
    let E : ((o : Option α) → β o) ≃ β none × ((a : α) → β (some a)) :=
      Equiv.piOptionEquivProd
    have hnonneg : ∀ p : β none × ((a : α) → β (some a)),
        0 ≤ f none p.1 * rest p.2 := by
      intro p
      exact mul_nonneg (h0 none p.1)
        (Finset.prod_nonneg fun a _ => h0 (some a) (p.2 a))
    have hrows : ∀ x : β none, Summable (fun y : (a : α) → β (some a) => f none x * rest y) := by
      intro x
      exact hrest.1.mul_left (f none x)
    have houter : Summable (fun x : β none => ∑' y : (a : α) → β (some a), f none x * rest y) := by
      have heq (x : β none) :
          (∑' y : (a : α) → β (some a), f none x * rest y) =
            f none x * ∑' y : (a : α) → β (some a), rest y :=
        hrest.1.tsum_mul_left (f none x)
      simpa only [heq] using
        (hs none).mul_right (∑' y : (a : α) → β (some a), rest y)
    have hprod : Summable (fun p : β none × ((a : α) → β (some a)) =>
        f none p.1 * rest p.2) :=
      (summable_prod_of_nonneg hnonneg).2 ⟨hrows, houter⟩
    have hcomp : Summable (fun x : (o : Option α) → β o =>
        f none (x none) * rest (fun a => x (some a))) := (E.summable_iff).2 hprod
    have hterm (x : (o : Option α) → β o) :
        (∏ o : Option α, f o (x o)) = f none (x none) * rest (fun a => x (some a)) := by
      simp [rest, f']
    constructor
    · convert hcomp using 1
      funext x
      exact hterm x
    · calc
        (∑' x : (o : Option α) → β o, ∏ o, f o (x o)) =
            ∑' x : (o : Option α) → β o, f none (x none) * rest (fun a => x (some a)) := by
              apply tsum_congr
              assumption
        _ = ∑' p : β none × ((a : α) → β (some a)), f none p.1 * rest p.2 :=
              E.tsum_eq (fun p : β none × ((a : α) → β (some a)) => f none p.1 * rest p.2)
        _ = ∑' x : β none, ∑' y : (a : α) → β (some a), f none x * rest y :=
              hprod.tsum_prod
        _ = (∑' x : β none, f none x) * (∑' y : (a : α) → β (some a), rest y) := by
              calc
                _ = ∑' x : β none, f none x * ∑' y : (a : α) → β (some a), rest y := by
                      apply tsum_congr
                      intro x
                      exact hrest.1.tsum_mul_left (f none x)
                _ = _ := (hs none).tsum_mul_right _
        _ = ∏ o : Option α, ∑' y, f o y := by
              have hrest' :
                  (∑' y : (a : α) → β (some a), rest y) =
                    ∏ a : α, ∑' y : β (some a), f (some a) y := by
                simpa [rest, f'] using hrest.2
              rw [hrest']
              simp

private theorem ghostBirthSeries_bound {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hμsum : (∑ a, μ a) ≤ 2)
    (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun c : Σ b : ℕ, Fin b → α =>
        x ^ c.1 / (c.1.factorial : ℝ) * ∏ i, μ (c.2 i)) ∧
      (∑' c : Σ b : ℕ, Fin b → α,
        x ^ c.1 / (c.1.factorial : ℝ) * ∏ i, μ (c.2 i)) ≤ Real.exp (2 * x) := by
  classical
  let f : (c : Σ b : ℕ, Fin b → α) → ℝ := fun c =>
    x ^ c.1 / (c.1.factorial : ℝ) * ∏ i, μ (c.2 i)
  have hf0 : ∀ c, 0 ≤ f c := by
    intro c
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun i _ => hμ (c.2 i)
  have hfiber (b : ℕ) : Summable (fun p : Fin b → α => f ⟨b, p⟩) :=
    summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
  let S : ℝ := ∑ a, μ a
  have hS  := hμsum
  have hsum (b : ℕ) :
      (∑' p : Fin b → α, f ⟨b, p⟩) = (x * S) ^ b / (b.factorial : ℝ) := by
    rw [tsum_fintype]
    simp only [f]
    calc
      (∑ p : Fin b → α, x ^ b / (b.factorial : ℝ) * ∏ i, μ (p i)) =
          (x ^ b / (b.factorial : ℝ)) * ∑ p : Fin b → α, ∏ i, μ (p i) := by
            rw [Finset.mul_sum]
      _ = (x * S) ^ b / (b.factorial : ℝ) := by
            rw [← Fintype.sum_pow μ b]
            ring
  have houter : Summable (fun b : ℕ => ∑' p : Fin b → α, f ⟨b, p⟩) := by
    simpa only [hsum] using Real.summable_pow_div_factorial (x * S)
  have hsumma  :=
    (summable_sigma_of_nonneg hf0).2 ⟨hfiber, houter⟩
  have htotal :
      (∑' c : Σ b : ℕ, Fin b → α, f c) = Real.exp (x * S) := by
    calc
      (∑' c : Σ b : ℕ, Fin b → α, f c) =
          ∑' b : ℕ, ∑' p : Fin b → α, f ⟨b, p⟩ :=
            Summable.tsum_sigma' hfiber hsumma
      _ = ∑' b : ℕ, (x * S) ^ b / (b.factorial : ℝ) := by
            apply tsum_congr
            exact hsum
      _ = Real.exp (x * S) := by
            rw [Real.exp_eq_exp_ℝ]
            exact (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) (x * S)).symm
  refine ⟨hsumma, ?_⟩
  rw [htotal]
  apply Real.exp_le_exp.mpr
  calc
    x * S ≤ x * 2 := mul_le_mul_of_nonneg_left hS hx
    _ = 2 * x := by ring

private theorem ghostDeletedPowerSum {α : Type*} [Fintype α] [DecidableEq α]
    (Z : Finset α) (a b : ℝ) :
    (∑ A : {A : Finset α // A ⊆ Z},
      b ^ A.1.card * a ^ (Z.card - A.1.card)) = (a + b) ^ Z.card := by
  classical
  let e  :=
    Equiv.subtypeEquivRight (fun A => (Finset.mem_powerset (s := A) (t := Z)).symm)

  calc
    _ = ∑ A : {A : Finset α // A ∈ Z.powerset},
        b ^ A.1.card * a ^ (Z.card - A.1.card) := by
          apply Fintype.sum_equiv e
          intro A
          rfl
    _ = ∑ A ∈ Z.powerset, b ^ A.card * a ^ (Z.card - A.card) := by
          simpa using Finset.sum_attach Z.powerset
            (fun A : Finset α => b ^ A.card * a ^ (Z.card - A.card))
    _ = (a + b) ^ Z.card := by
          simpa [add_comm] using Finset.sum_pow_mul_eq_add_pow b a Z

private theorem ghostDeletionFactor_bound {α : Type*} [Fintype α] [DecidableEq α]
    (Z : Finset α) (N : ℕ) (hZN : Z.card ≤ N) (a b v : ℝ)
    (hv : 0 < v) (hx0 : 0 ≤ a + b / v) (hx1 : a + b / v ≤ 1) :
    (∑' A : {A : Finset α // A ⊆ Z},
      a ^ (Z.card - A.1.card) * b ^ A.1.card * v ^ (N - A.1.card)) ≤ v ^ N := by
  classical
  rw [tsum_fintype]
  calc
    (∑ A : {A : Finset α // A ⊆ Z},
        a ^ (Z.card - A.1.card) * b ^ A.1.card * v ^ (N - A.1.card)) =
        v ^ N * ∑ A : {A : Finset α // A ⊆ Z},
          (b / v) ^ A.1.card * a ^ (Z.card - A.1.card) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A hA
            have hAle  := (Finset.card_le_card A.2).trans hZN
            have hvpow  :=
              pow_sub₀ v (ne_of_gt hv) hAle
            rw [hvpow]
            ring_nf
    _ = v ^ N * (a + b / v) ^ Z.card := by
          rw [ghostDeletedPowerSum]
    _ ≤ v ^ N * 1 := by
          exact mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) (pow_nonneg hv.le N)
    _ = v ^ N := by ring

section

variable (F : FixedData) (n : ℕ) (i : Fin (n + 1))

lemma visitQ_eq_q_or_sqrt :
    visitQ F.q n i = F.q ∨ visitQ F.q n i = Real.sqrt F.q := by
  unfold visitQ
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma visitQ_pos :
    0 < visitQ F.q n i := by
  rcases visitQ_eq_q_or_sqrt F n i with h | h
  · rw [h]; exact F.q_pos
  · rw [h]; exact Real.sqrt_pos.2 F.q_pos

lemma visitQ_lt_one :
    visitQ F.q n i < 1 := by
  rcases visitQ_eq_q_or_sqrt F n i with h | h
  · rw [h]; exact F.q_lt
  · rw [h]
    by_contra hnot
    have hge  := le_of_not_gt hnot
    have hs := Real.sq_sqrt (le_of_lt F.q_pos)
    have hp := mul_nonneg (Real.sqrt_nonneg F.q) (sub_nonneg.mpr hge)
    nlinarith [F.q_lt]

lemma eta_pos :
    0 < eta F n i := by
  unfold eta
  linarith [visitQ_lt_one F n i]

end

lemma visitQ_memory_damping (F : FixedData) (r : MemoryParameters F)
    (n : ℕ) (i : Fin (n + 1)) :
    visitQ F.q n i / r.rho ^ (2 : ℕ) +
      2 * max 1 F.vMax * eta F n i / (r.rho * r.v) < 1 := by
  rcases visitQ_eq_q_or_sqrt F n i with h | h
  · simpa [eta, h] using r.damping F.q (Or.inl rfl)
  · simpa [eta, h] using r.damping (Real.sqrt F.q) (Or.inr rfl)

lemma rowsDeleteMemoryIndices_card {P : PrimeGroups} {g : P.Group}
    (z : P.Memory g) (A : Finset (Fin z.card)) :
    (deleteMemoryIndices z A).card = z.card - A.card := by
  classical
  unfold deleteMemoryIndices
  rw [Multiset.coe_card, List.length_map, Finset.length_toList]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
  simp

lemma rowsZeroBirthBatch_card {P : PrimeGroups} {g : P.Group} {b : ℕ}
    (p : Fin b → P.Prime g) : (zeroBirthBatch p).card = b := by
  simp [zeroBirthBatch]

variable {P : PrimeGroups}

abbrev GhostBirthBatch (g : P.BigGroup) := Σ b : ℕ, Fin b → P.Prime g.val

abbrev GhostDeletedChoice {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup) :=
  {A : Finset (Fin ((s.2.2 g).card)) // A ⊆ zeroMemoryIndices (s.2.2 g)}

abbrev GhostGroupTransition {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup) :=
  GhostDeletedChoice s g × GhostBirthBatch g

/-- A row transition before its target memory is grouped with other choices. -/
abbrev GhostTransition {M : ℕ} (s : P.MemoryState M) :=
  (g : P.BigGroup) → GhostGroupTransition s g

def ghostTransitionDeleted {M : ℕ} {s : P.MemoryState M}
    (c : GhostTransition s) (g : P.BigGroup) := (c g).1.1

def ghostTransitionBirths {M : ℕ} {s : P.MemoryState M}
    (c : GhostTransition s) (g : P.BigGroup) := (c g).2

def ghostTransitionTarget {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : P.MemoryState M :=
  (s.1, s.2.1, fun g =>
    deleteMemoryIndices (s.2.2 g) (ghostTransitionDeleted c g) +
      zeroBirthBatch (ghostTransitionBirths c g).2)

lemma ghostTransitionTarget_card {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) (g : P.BigGroup) :
    ((ghostTransitionTarget s c).2.2 g).card =
      (s.2.2 g).card - (ghostTransitionDeleted c g).card +
        (ghostTransitionBirths c g).1 := by
  simp [ghostTransitionTarget, ghostTransitionDeleted, ghostTransitionBirths,
    rowsDeleteMemoryIndices_card, rowsZeroBirthBatch_card, Multiset.card_add]

def ghostTransitionAsChoice {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : GhostChoice s (ghostTransitionTarget s c) := by
  classical
  refine Prod.mk (fun g : P.BigGroup => ghostTransitionDeleted c g)
    (Sigma.mk (fun g : P.BigGroup =>
      (⟨(ghostTransitionBirths c g).1, ?_⟩ :
        Fin (((ghostTransitionTarget s c).2.2 g).card + 1)))
      (fun g : P.BigGroup => (ghostTransitionBirths c g).2))
  have hc := ghostTransitionTarget_card s c g
  omega

def ghostGroupRowFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  let A := c.1.1
  let b := (c.2).1
  ((visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - A.card) *
    (eta F n i / rho) ^ A.card *
    v ^ ((s.2.2 g).card - A.card)) *
    (((d * eta F n i * P.V g.val * v / rho) ^ b /
        (b.factorial : ℝ)) *
      ∏ j : Fin b, tiltedMu F P n g.val ((c.2).2 j))

def ghostGroupRevFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  let A := c.1.1
  let b := (c.2).1
  ((visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - A.card) *
    (eta F n i / rho) ^ A.card *
    (d * P.V g.val) ^ A.card *
    v ^ ((s.2.2 g).card - A.card)) *
    (((eta F n i * v / rho) ^ b /
        (b.factorial : ℝ)) *
      ∏ j : Fin b, tiltedMu F P n g.val ((c.2).2 j))

private theorem tiltedMu_nonneg (F : FixedData) (n : ℕ) (g : P.Group)
    (hV : 0 < P.V g) (hbase : ∀ p : P.Prime g, 0 < baselinePrime F n p.val)
    (p : P.Prime g) : 0 ≤ tiltedMu F P n g p := by
  have hp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (P.prime g p.val p.property).pos
  unfold tiltedMu
  positivity [hbase p]

/-- The two orientations place the multiplier on deletion or on birth, respectively. -/
private def ghostGroupFactor (F : FixedData) (n : ℕ) (r : MemoryParameters F)
    (a b : ℝ) (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  ((visitQ F.q n i / r.rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - c.1.1.card) *
    (a * eta F n i / r.rho) ^ c.1.1.card * r.v ^ ((s.2.2 g).card - c.1.1.card)) *
  ((b * eta F n i * r.v / r.rho) ^ c.2.1 / (c.2.1.factorial : ℝ) *
    ∏ j : Fin c.2.1, tiltedMu F P n g.val (c.2.2 j))

private theorem ghostGroupRowFactor_eq (F : FixedData) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) :
    ghostGroupRowFactor F n r.rho d r.v i s g c =
      ghostGroupFactor F n r 1 (d * P.V g.val) i s g c := by
  simp [ghostGroupRowFactor, ghostGroupFactor, mul_assoc, mul_left_comm]

private theorem ghostGroupRevFactor_eq (F : FixedData) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) :
    ghostGroupRevFactor F n r.rho d r.v i s g c =
      ghostGroupFactor F n r (d * P.V g.val) 1 i s g c := by
  simp only [ghostGroupRevFactor, ghostGroupFactor, one_mul, mul_div_assoc, mul_pow]
  ring

private theorem ghostGroupFactor_bounds
    (F : FixedData) (n : ℕ) (r : MemoryParameters F) (a b : ℝ)
    (ha : a ∈ Set.Icc 0 (2 * max 1 F.vMax)) (hb : b ∈ Set.Icc 0 (2 * max 1 F.vMax))
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (hV : 0 < P.V g.val) (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2) :
    (∀ c, 0 ≤ ghostGroupFactor F n r a b i s g c) ∧
    Summable (ghostGroupFactor F n r a b i s g) ∧
    (∑' c, ghostGroupFactor F n r a b i s g c) ≤
      r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
  classical
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hη := eta_pos F n i
  have hη1 : eta F n i ≤ 1 := by unfold eta; linarith [visitQ_pos F n i]
  have hv : 0 < r.v := by linarith [r.v_gt]
  have hρ := r.rho_pos
  have hμ0 := tiltedMu_nonneg F n g.val hV hbase
  let Z := zeroMemoryIndices (s.2.2 g)
  let α := visitQ F.q n i / r.rho ^ (2 : ℕ)
  let δ := a * eta F n i / r.rho
  let X := b * eta F n i * r.v / r.rho
  let D (A : GhostDeletedChoice s g) :=
    α ^ (Z.card - A.1.card) * δ ^ A.1.card * r.v ^ ((s.2.2 g).card - A.1.card)
  let B (c : GhostBirthBatch g) :=
    X ^ c.1 / (c.1.factorial : ℝ) * ∏ j : Fin c.1, tiltedMu F P n g.val (c.2 j)
  have hα : 0 ≤ α := by dsimp [α]; positivity [visitQ_pos F n i]
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hD0 (A : GhostDeletedChoice s g) : 0 ≤ D A := by dsimp [D]; positivity
  have hB0 (c : GhostBirthBatch g) : 0 ≤ B c := by
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ => hμ0 (c.2 j))
  have hdamp : α + δ / r.v ≤ 1 := by
    calc
      _ = α + a * eta F n i / (r.rho * r.v) := by rw [div_div]
      _ ≤ α + 2 * max 1 F.vMax * eta F n i / (r.rho * r.v) := by gcongr
      _ ≤ 1 := (visitQ_memory_damping F r n i).le
  have hZ : Z.card ≤ (s.2.2 g).card := by
    simpa using Finset.card_le_card (Finset.subset_univ Z)
  have hD : (∑' A, D A) ≤ r.v ^ (s.2.2 g).card :=
    ghostDeletionFactor_bound Z _ hZ α δ r.v hv (by positivity) hdamp
  have hB :=
    ghostBirthSeries_bound _ hμ0 hmu X hX
  have hsumD : Summable D := Summable.of_finite
  have hprod :=
    hsumD.mul_of_nonneg hB.1 hD0 hB0
  refine ⟨fun c => mul_nonneg (hD0 c.1) (hB0 c.2), hprod, ?_⟩
  change (∑' c : GhostGroupTransition s g, D c.1 * B c.2) ≤ _
  rw [← hsumD.tsum_mul_tsum hB.1 hprod]
  have hXle : X ≤ 2 * max 1 F.vMax * 1 * r.v / r.rho := by dsimp [X]; gcongr
  have hExp : Real.exp (2 * X) ≤ Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
    apply Real.exp_le_exp.mpr
    linear_combination 2 * hXle
  exact mul_le_mul hD (hB.2.trans hExp) (tsum_nonneg hB0) (by positivity)

private theorem ghostRate_bounds (F : FixedData) (d V : ℝ) (hd : d = 1 ∨ d = 2)
    (hV : 0 < V ∧ V ≤ F.vMax) :
    1 ∈ Set.Icc 0 (2 * max 1 F.vMax) ∧ d * V ∈ Set.Icc 0 (2 * max 1 F.vMax) := by
  have h1 := le_max_left (1 : ℝ) F.vMax
  have h2 := hV.2.trans (le_max_right 1 F.vMax)
  rcases hd with rfl | rfl <;> exact ⟨⟨by norm_num, by linarith⟩, ⟨by positivity [hV.1], by linarith⟩⟩

def ghostTransitionRowFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : ℝ :=
  ∏ g : P.BigGroup, ghostGroupRowFactor F n rho d v i s g (c g)

def ghostTransitionRevFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : ℝ :=
  ∏ g : P.BigGroup, ghostGroupRevFactor F n rho d v i s g (c g)

def ghostTransitionGroupRawWeight (F : FixedData) (n : ℕ) (rho : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  let A := c.1.1
  let b := c.2.1
  (-(eta F n i / rho)) ^ A.card *
    (visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - A.card) *
    ((b.factorial : ℝ)⁻¹) *
    (-(eta F n i * P.V g.val / rho)) ^ b *
    ∏ j : Fin b, tiltedMu F P n g.val (c.2.2 j)

section

variable (F : FixedData) (P : PrimeGroups) (n : ℕ)

private theorem ghostTransitionGroupRawWeight_abs (r : MemoryParameters F)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g)
    (hV : 0 < P.V g.val)
    (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    |ghostTransitionGroupRawWeight F n r.rho i s g c| =
      (eta F n i / r.rho) ^ c.1.1.card *
      (visitQ F.q n i / r.rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices (s.2.2 g)).card - c.1.1.card) *
      ((c.2.1.factorial : ℝ)⁻¹) *
      (eta F n i * P.V g.val / r.rho) ^ c.2.1 *
      ∏ j : Fin c.2.1, tiltedMu F P n g.val (c.2.2 j) := by
  classical
  have hμ := tiltedMu_nonneg F n g.val hV hbase
  have heta : 0 ≤ eta F n i / r.rho := div_nonneg (eta_pos F n i).le r.rho_pos.le
  have hq : 0 ≤ visitQ F.q n i / r.rho ^ (2 : ℕ) :=
    div_nonneg (visitQ_pos F n i).le (pow_nonneg r.rho_pos.le _)
  have hb  :=
    div_nonneg (mul_nonneg (eta_pos F n i).le hV.le) r.rho_pos.le
  have hf : 0 ≤ ((c.2.1.factorial : ℝ)⁻¹) := by positivity
  have hμp : 0 ≤ ∏ j : Fin c.2.1, tiltedMu F P n g.val (c.2.2 j) :=
    Finset.prod_nonneg fun j _ => hμ _
  have hnegA : |(-(eta F n i / r.rho))| = eta F n i / r.rho := by
    rw [abs_neg, abs_of_nonneg heta]
  have hnegB : |(-(eta F n i * P.V g.val / r.rho))| =
      eta F n i * P.V g.val / r.rho := by
    rw [abs_neg, abs_of_nonneg hb]
  simp [ghostTransitionGroupRawWeight, abs_mul, abs_pow, hnegA, hnegB,
    abs_of_nonneg hq, abs_of_nonneg hf, abs_of_nonneg hμp]

private theorem ghostChoiceWeight_transition_eq_prod (rho : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) :
    ghostChoiceWeight F n rho i (ghostTransitionAsChoice s c) =
      ∏ g : P.BigGroup, ghostTransitionGroupRawWeight F n rho i s g (c g) := by
  classical
  simp [ghostChoiceWeight, ghostTransitionAsChoice, ghostTransitionGroupRawWeight,
    ghostTransitionDeleted, ghostTransitionBirths, neg_div]
  rfl

end

private theorem ghostTransitionRowFactor_eq_kernelWeight
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostTransition s) :
    ghostTransitionRowFactor F n r.rho d r.v i s c =
      |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
        d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
          P.memoryWeight r.v (ghostTransitionTarget s c) := by
  classical
  let t := ghostTransitionTarget s c
  let ch := ghostTransitionAsChoice s c
  have hraw := ghostChoiceWeight_transition_eq_prod F P n r.rho i s c
  have habs : |ghostChoiceWeight F n r.rho i ch| =
      ∏ g : P.BigGroup, |ghostTransitionGroupRawWeight F n r.rho i s g (c g)| := by
    change |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| = _
    rw [hraw, Finset.abs_prod]
  have hgroup : ∀ g : P.BigGroup,
      ghostGroupRowFactor F n r.rho d r.v i s g (c g) =
        |ghostTransitionGroupRawWeight F n r.rho i s g (c g)| *
          d ^ (ghostTransitionBirths c g).1 * r.v ^ (t.2.2 g).card := by
    intro g
    have hrawg := ghostTransitionGroupRawWeight_abs F P n r i s g (c g)
      (hV g.val) (hbase g)
    rw [ghostGroupRowFactor, hrawg, ghostTransitionTarget_card]
    have hbpow :
        (d * eta F n i * P.V g.val * r.v / r.rho) ^ (c g).2.1 =
          (eta F n i * P.V g.val / r.rho) ^ (c g).2.1 *
            d ^ (c g).2.1 * r.v ^ (c g).2.1 := by
      ring
    rw [ghostTransitionBirths, ghostTransitionDeleted]
    rw [pow_add]
    rw [hbpow]
    ring_nf
  have hBcount : ghostBirthCount ch = ∑ g : P.BigGroup, (ghostTransitionBirths c g).1 := by
    rfl
  have hdPow : d ^ ghostBirthCount ch =
      ∏ g : P.BigGroup, d ^ (ghostTransitionBirths c g).1 := by
    rw [hBcount]
    exact (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun g : P.BigGroup => (ghostTransitionBirths c g).1) d).symm
  have hvPow : P.memoryWeight r.v t =
      ∏ g : P.BigGroup, r.v ^ (t.2.2 g).card := by
    change r.v ^ (∑ g : P.BigGroup, (t.2.2 g).card) = _
    exact (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun g : P.BigGroup => (t.2.2 g).card) r.v).symm
  calc
    ghostTransitionRowFactor F n r.rho d r.v i s c =
        ∏ g : P.BigGroup,
          (|ghostTransitionGroupRawWeight F n r.rho i s g (c g)| *
            d ^ (ghostTransitionBirths c g).1 * r.v ^ (t.2.2 g).card) := by
          unfold ghostTransitionRowFactor
          exact Finset.prod_congr rfl (fun g _ => hgroup g)
    _ = (∏ g : P.BigGroup, |ghostTransitionGroupRawWeight F n r.rho i s g (c g)|) *
          (∏ g : P.BigGroup, d ^ (ghostTransitionBirths c g).1) *
          (∏ g : P.BigGroup, r.v ^ (t.2.2 g).card) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = |ghostChoiceWeight F n r.rho i ch| * d ^ ghostBirthCount ch *
          P.memoryWeight r.v t := by
            rw [← habs, ← hdPow, ← hvPow]

private theorem ghostGroupRevFactor_eq_reversal_mul_row
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M) (c : GhostTransition s) (g : P.BigGroup)
    (hV : 0 < P.V g.val) :
    ghostGroupRevFactor F n r.rho d r.v i s g (c g) =
      (d * P.V g.val) ^ (((s.2.2 g).card : ℤ) -
        (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
        ghostGroupRowFactor F n r.rho d r.v i s g (c g) := by
  classical
  let a := (c g).1.1.card
  let b := (c g).2.1
  let V := P.V g.val
  let qpart := visitQ F.q n i / r.rho ^ (2 : ℕ)
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hDV : 0 < d * V := mul_pos hdpos hV
  have htarget : ((ghostTransitionTarget s c).2.2 g).card =
      (s.2.2 g).card - a + b := by
    simp [ghostTransitionTarget, ghostTransitionDeleted, ghostTransitionBirths, a, b,
      rowsDeleteMemoryIndices_card, rowsZeroBirthBatch_card, Multiset.card_add]
  have hExp : ((s.2.2 g).card : ℤ) -
      (((ghostTransitionTarget s c).2.2 g).card : ℤ) = (a : ℤ) - (b : ℤ) := by
    rw [htarget]
    have hZle : (zeroMemoryIndices (s.2.2 g)).card ≤ (s.2.2 g).card := by
      simpa using Finset.card_le_card
        (Finset.subset_univ (zeroMemoryIndices (s.2.2 g)))
    have hdel : a ≤ (s.2.2 g).card := by
      dsimp [a]
      exact (Finset.card_le_card (c g).1.2).trans hZle
    omega
  have hpow :
      (d * V) ^ (((s.2.2 g).card : ℤ) -
        (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
        (d * V) ^ b = (d * V) ^ a := by
    rw [hExp, zpow_sub₀ (ne_of_gt hDV)]
    simp only [zpow_natCast]
    field_simp [ne_of_gt hDV]
  have hbirth : d * eta F n i * V * r.v / r.rho =
      (d * V) * (eta F n i * r.v / r.rho) := by ring
  have hbirthpow : ((d * V) * (eta F n i * r.v / r.rho)) ^ b =
      (d * V) ^ b * (eta F n i * r.v / r.rho) ^ b := mul_pow _ _ _
  let hμprod : ℝ := ∏ j : Fin b, tiltedMu F P n g.val ((c g).2.2 j)
  have hrowFac :
      ghostGroupRowFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * r.v ^ ((s.2.2 g).card - a) *
            ((d * eta F n i * V * r.v / r.rho) ^ b /
              (b.factorial : ℝ) * hμprod) := by
    rfl
  have hrevFac :
      ghostGroupRevFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * (d * V) ^ a *
            r.v ^ ((s.2.2 g).card - a) *
              ((eta F n i * r.v / r.rho) ^ b /
                (b.factorial : ℝ) * hμprod) := by
    rfl
  have hbirthEq :
      (d * eta F n i * V * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod =
        (d * V) ^ b *
          ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod) := by
    ring
  have hrowToRev :
      ghostGroupRowFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * r.v ^ ((s.2.2 g).card - a) *
            ((d * V) ^ b *
              ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod)) := by
    rw [hrowFac, hbirthEq]
  calc
    ghostGroupRevFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * (d * V) ^ a *
            r.v ^ ((s.2.2 g).card - a) *
              ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod) := hrevFac
    _ = (d * V) ^ (((s.2.2 g).card : ℤ) -
          (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
        (qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * r.v ^ ((s.2.2 g).card - a) *
            ((d * V) ^ b *
              ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod))) := by
          rw [← hpow]
          ring
    _ = (d * V) ^ (((s.2.2 g).card : ℤ) -
          (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
          ghostGroupRowFactor F n r.rho d r.v i s g (c g) := by
            rw [hrowToRev]

private theorem ghostTransitionRevFactor_eq_reversal_kernelWeight
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostTransition s) :
    ghostTransitionRevFactor F n r.rho d r.v i s c =
      ghostReversalFactor d s (ghostTransitionTarget s c) *
        |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
        d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
        P.memoryWeight r.v (ghostTransitionTarget s c) := by
  classical
  calc
    ghostTransitionRevFactor F n r.rho d r.v i s c =
        ∏ g : P.BigGroup,
          ((d * P.V g.val) ^ (((s.2.2 g).card : ℤ) -
              (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
            ghostGroupRowFactor F n r.rho d r.v i s g (c g)) := by
          unfold ghostTransitionRevFactor
          apply Finset.prod_congr rfl
          intro g hg
          exact ghostGroupRevFactor_eq_reversal_mul_row F P n r d hd i s c g
            (hV g.val)
    _ = (∏ g : P.BigGroup, (d * P.V g.val) ^
            (((s.2.2 g).card : ℤ) -
              (((ghostTransitionTarget s c).2.2 g).card : ℤ))) *
          ghostTransitionRowFactor F n r.rho d r.v i s c := by
          rw [Finset.prod_mul_distrib]
          rfl
    _ = ghostReversalFactor d s (ghostTransitionTarget s c) *
          ghostTransitionRowFactor F n r.rho d r.v i s c := rfl
    _ = ghostReversalFactor d s (ghostTransitionTarget s c) *
          (|ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
            d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
            P.memoryWeight r.v (ghostTransitionTarget s c)) := by
          exact congrArg (fun x : ℝ => ghostReversalFactor d s
            (ghostTransitionTarget s c) * x)
            (ghostTransitionRowFactor_eq_kernelWeight F P n r d i s hV hbase c)
    _ = ghostReversalFactor d s (ghostTransitionTarget s c) *
          |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
            d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
            P.memoryWeight r.v (ghostTransitionTarget s c) := by ring

/-- Reconstruct the unrestricted per-group transition from a valid literal choice. -/
def ghostTransitionOfChoice {M : ℕ} (s t : P.MemoryState M)
    (c : GhostChoice s t) (hc : ghostChoiceValid c) : GhostTransition s :=
  fun g => (⟨c.1 g, (hc g).1⟩,
    ⟨(c.2.1 g).val, c.2.2 g⟩)

lemma ghostTransitionOfChoice_target {M : ℕ} (s t : P.MemoryState M)
    (hsides : s.1 = t.1 ∧ s.2.1 = t.2.1)
    (c : GhostChoice s t) (hc : ghostChoiceValid c) :
    ghostTransitionTarget s (ghostTransitionOfChoice s t c hc) = t := by
  apply Prod.ext
  · exact hsides.1
  · apply Prod.ext
    · exact hsides.2
    · funext g
      exact (hc g).2

private theorem ghostChoiceWeight_ofChoice
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    {M : ℕ} (s t : P.MemoryState M) (c : GhostChoice s t)
    (hc : ghostChoiceValid c) :
    ghostChoiceWeight F n rho i c =
      ghostChoiceWeight F n rho i
        (ghostTransitionAsChoice s (ghostTransitionOfChoice s t c hc)) := by
  rfl

private theorem ghostBirthCount_ofChoice
    {P : PrimeGroups} {M : ℕ} (s t : P.MemoryState M) (c : GhostChoice s t)
    (hc : ghostChoiceValid c) :
    ghostBirthCount c = ghostBirthCount
      (ghostTransitionAsChoice s (ghostTransitionOfChoice s t c hc)) := by
  rfl

structure GhostSupportedChoice {M : ℕ} (s : P.MemoryState M) where
  target : P.MemoryState M
  choice : GhostChoice s target
  valid : ghostChoiceValid choice
  sides : s.1 = target.1 ∧ s.2.1 = target.2.1

abbrev GhostSupportedChoiceAt {M : ℕ} (s t : P.MemoryState M) :=
  {c : GhostChoice s t // ghostChoiceValid c ∧
    s.1 = t.1 ∧ s.2.1 = t.2.1}

def ghostRowsChoiceTerm (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s t : P.MemoryState M)
    (c : GhostChoice s t) : ℝ :=
  |ghostChoiceWeight F n rho i c| * d ^ ghostBirthCount c * P.memoryWeight v t

private theorem sum_ite_eq_subtype_sum {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    (∑ x : α, if p x then f x else 0) = ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x : α, if p x then f x else 0) =
        ∑ x ∈ Finset.univ with p x, f x := by
          rw [Finset.sum_filter]
    _ = ∑ x : {x // p x}, f x.1 :=
      Finset.sum_subtype (Finset.univ.filter p) (by simp_all) f

lemma ghostRowTerm_eq_supportedChoiceSum
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (i : Fin (n + 1)) (s t : P.MemoryState (J + F.ell)) :
    absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t =
      ∑ c : GhostSupportedChoiceAt s t,
        ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 := by
  classical
  by_cases hside : s.1 = t.1 ∧ s.2.1 = t.2.1
  · simp only [absoluteScaledMemoryGhostKernel, ite_eq_left hside]
    have hmul :
        (∑ c : GhostChoice s t,
          if ghostChoiceValid c then
            |ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c else 0) *
            P.memoryWeight r.v t =
          ∑ c : GhostChoice s t,
            if ghostChoiceValid c then
              (|ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c) *
                P.memoryWeight r.v t else 0 := by
      calc
        _ = ∑ c : GhostChoice s t,
            (if ghostChoiceValid c then
              |ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c else 0) *
              P.memoryWeight r.v t :=
                Finset.sum_mul Finset.univ
                  (fun c : GhostChoice s t =>
                    if ghostChoiceValid c then
                      |ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c else 0)
                  (P.memoryWeight r.v t)
        _ = _ := by simp
    rw [hmul]
    calc
      _ = ∑ c : {c : GhostChoice s t // ghostChoiceValid c},
          (|ghostChoiceWeight F n r.rho i c.1| * d ^ ghostBirthCount c.1) *
            P.memoryWeight r.v t :=
          sum_ite_eq_subtype_sum (ghostChoiceValid (s := s) (t := t))
            (fun c => (|ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c) *
              P.memoryWeight r.v t)
      _ = ∑ c : GhostSupportedChoiceAt s t,
          ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 := by
          let e : {c : GhostChoice s t // ghostChoiceValid c} ≃ GhostSupportedChoiceAt s t :=
            Equiv.subtypeEquivRight (fun c => by simp [hside])
          simpa [e, GhostSupportedChoiceAt, ghostRowsChoiceTerm] using
            (Fintype.sum_equiv e
              (fun c : {c : GhostChoice s t // ghostChoiceValid c} =>
                (|ghostChoiceWeight F n r.rho i c.1| * d ^ ghostBirthCount c.1) *
                  P.memoryWeight r.v t)
              (fun c : GhostSupportedChoiceAt s t =>
                ghostRowsChoiceTerm F n r.rho d r.v i s t c.1)
              (by intro c; rfl))
  · have hempty : IsEmpty (GhostSupportedChoiceAt s t) :=
      ⟨fun c => hside c.2.2⟩
    let := hempty
    simp [absoluteScaledMemoryGhostKernel, hside, ghostRowsChoiceTerm]

def ghostSupportedChoiceTransition {M : ℕ} {s : P.MemoryState M}
    (e : GhostSupportedChoice s) : GhostTransition s :=
  ghostTransitionOfChoice s e.target e.choice e.valid

def ghostSupportedChoiceAtPackage {M : ℕ} {s t : P.MemoryState M}
    (c : GhostSupportedChoiceAt s t) : GhostSupportedChoice s :=
  ⟨t, c.1, c.2.1, c.2.2⟩

def ghostSupportedChoiceAtTransition {M : ℕ} {s t : P.MemoryState M}
    (c : GhostSupportedChoiceAt s t) : GhostTransition s :=
  ghostSupportedChoiceTransition (ghostSupportedChoiceAtPackage c)

section

variable (F : FixedData) (P : PrimeGroups)

private theorem ghostRowsChoiceTerm_eq_transitionRowFactor (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (i : Fin (n + 1))
    {M : ℕ} (s t : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostSupportedChoiceAt s t) :
    ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 =
      ghostTransitionRowFactor F n r.rho d r.v i s
        (ghostSupportedChoiceAtTransition c) := by
  classical
  have hc := c.2.1
  have hs := c.2.2
  have htarget := ghostTransitionOfChoice_target s t hs c.1 hc
  have hweight := ghostChoiceWeight_ofChoice F P n r.rho i s t c.1 hc
  have hcount := ghostBirthCount_ofChoice s t c.1 hc
  change ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 =
    ghostTransitionRowFactor F n r.rho d r.v i s
      (ghostTransitionOfChoice s t c.1 hc)
  rw [ghostTransitionRowFactor_eq_kernelWeight F P n r d i s hV hbase]
  unfold ghostRowsChoiceTerm
  rw [← hweight, ← hcount, htarget]

private theorem ghostReverseSupportedChoiceTerm_eq_transitionRevFactor
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s t : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostSupportedChoiceAt s t) :
    ghostReversalFactor d s t *
      ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 =
    ghostTransitionRevFactor F n r.rho d r.v i s
      (ghostSupportedChoiceAtTransition c) := by
  classical
  have hc := c.2.1
  have hs := c.2.2
  have htarget := ghostTransitionOfChoice_target s t hs c.1 hc
  have hweight := ghostChoiceWeight_ofChoice F P n r.rho i s t c.1 hc
  have hcount := ghostBirthCount_ofChoice s t c.1 hc
  change ghostReversalFactor d s t *
      (|ghostChoiceWeight F n r.rho i c.1| * d ^ ghostBirthCount c.1 *
        P.memoryWeight r.v t) =
    ghostTransitionRevFactor F n r.rho d r.v i s
      (ghostTransitionOfChoice s t c.1 hc)
  rw [ghostTransitionRevFactor_eq_reversal_kernelWeight F P n r d hd i s
    (fun g => hV g) hbase (ghostTransitionOfChoice s t c.1 hc)]
  rw [← hweight, ← hcount, htarget]
  ring

end

private theorem ghostTransitionOfChoice_injective_on_fixed_target
    {M : ℕ} (s t : P.MemoryState M)
    (c₁ c₂ : GhostChoice s t) (hc₁ : ghostChoiceValid c₁) (hc₂ : ghostChoiceValid c₂)
    (h : ghostTransitionOfChoice s t c₁ hc₁ = ghostTransitionOfChoice s t c₂ hc₂) :
    c₁ = c₂ := by
  classical
  rcases c₁ with ⟨del₁, ⟨b₁, p₁⟩⟩
  rcases c₂ with ⟨del₂, ⟨b₂, p₂⟩⟩
  have hfun : (fun g : P.BigGroup =>
      ((⟨del₁ g, (hc₁ g).1⟩,
        (⟨(b₁ g).val, p₁ g⟩ : GhostBirthBatch g)) : GhostGroupTransition s g)) =
      (fun g : P.BigGroup =>
      ((⟨del₂ g, (hc₂ g).1⟩,
        (⟨(b₂ g).val, p₂ g⟩ : GhostBirthBatch g)) : GhostGroupTransition s g)) := by
    assumption
  have hpoint (g : P.BigGroup) := congrFun hfun g
  have hdel : del₁ = del₂ := by
    funext g
    exact congrArg (fun q : GhostGroupTransition s g => q.1.1) (hpoint g)
  have hbatch (g : P.BigGroup) := congrArg (fun q : GhostGroupTransition s g => q.2) (hpoint g)
  have hb : b₁ = b₂ := by
    funext g
    apply Fin.ext
    exact congrArg Sigma.fst (hbatch g)
  cases hb
  have hp : p₁ = p₂ := by
    funext g j
    have hseq := (Sigma.mk.inj_iff.mp (hbatch g)).2
    exact congrFun (eq_of_heq hseq) j
  cases hdel
  cases hp
  rfl

private theorem ghostSupportedChoiceAtTransition_injective
    {M : ℕ} (s : P.MemoryState M) :
    Function.Injective (fun e : Σ t, GhostSupportedChoiceAt s t =>
      ghostSupportedChoiceAtTransition e.2) := by
  rintro ⟨t, c⟩ ⟨t', c'⟩ h
  have he := congrArg (ghostTransitionTarget s) h
  change ghostTransitionTarget s (ghostTransitionOfChoice s t c.1 c.2.1) =
    ghostTransitionTarget s (ghostTransitionOfChoice s t' c'.1 c'.2.1) at he
  rw [ghostTransitionOfChoice_target s t c.2.2, ghostTransitionOfChoice_target s t' c'.2.2] at he
  subst t'
  congr 1
  exact Subtype.ext (ghostTransitionOfChoice_injective_on_fixed_target s t c.1 c'.1 c.2.1 c'.2.1 h)

/-- Regroup the absolutely summable transition weights by their target memory. -/
private theorem ghostGroupedSum_bound {M : ℕ} (s : P.MemoryState M)
    (f : GhostTransition s → ℝ) (h0 : ∀ c, 0 ≤ f c) (hf : Summable f)
    (R : P.MemoryState M → ℝ) (hR : ∀ t,
      R t = ∑ c : GhostSupportedChoiceAt s t, f (ghostSupportedChoiceAtTransition c)) :
    Summable R ∧ (∑' t, R t) ≤ ∑' c, f c := by
  classical
  let e (x : Σ t, GhostSupportedChoiceAt s t) := ghostSupportedChoiceAtTransition x.2
  have hi : Function.Injective e := ghostSupportedChoiceAtTransition_injective s
  have hs : Summable (fun x => f (e x)) := hf.comp_injective hi
  have he (t) : R t = ∑' c : GhostSupportedChoiceAt s t, f (e ⟨t, c⟩) := by
    rw [tsum_fintype, hR]
  rw [funext he]
  refine ⟨hs.sigma, ?_⟩
  rw [← hs.tsum_sigma]
  exact hs.tsum_le_tsum_of_inj e hi (fun c _ => h0 c) (fun _ => le_rfl) hf

private theorem ghostTransition_bounds
    (F : FixedData) (r : MemoryParameters F) {M : ℕ} (s : P.MemoryState M)
    (f : (g : P.BigGroup) → GhostGroupTransition s g → ℝ)
    (hf : ∀ g, (∀ c, 0 ≤ f g c) ∧ Summable (f g) ∧
      (∑' c, f g c) ≤ r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho)) :
    (∀ c : GhostTransition s, 0 ≤ ∏ g, f g (c g)) ∧
    Summable (fun c : GhostTransition s => ∏ g, f g (c g)) ∧
    (∑' c : GhostTransition s, ∏ g, f g (c g)) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  obtain ⟨hs, heq⟩ := piProdTsum _ f (fun g => (hf g).1) fun g => (hf g).2.1
  refine ⟨fun c => Finset.prod_nonneg fun g _ => (hf g).1 _, hs, ?_⟩
  rw [heq]
  let E := Real.exp (4 * max 1 F.vMax * r.v / r.rho)
  calc
    _ ≤ ∏ g : P.BigGroup, r.v ^ (s.2.2 g).card * E :=
      Finset.prod_le_prod₀ (fun g _ => tsum_nonneg (hf g).1) (fun g _ => (hf g).2.2)
    _ = E ^ P.bigGroups.card * P.memoryWeight r.v s := by
      have hcard : Fintype.card P.BigGroup = P.bigGroups.card :=
        (Fintype.card_congr (Equiv.subtypeEquivRight (fun g : P.Group => by
          simp [PrimeGroups.bigGroups]))).trans (Fintype.card_coe P.bigGroups)
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp [PrimeGroups.memoryWeight, PrimeGroups.memorySize, hcard, mul_comm]

private theorem ghostRows_forward_bound
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    (s : P.MemoryState (J + F.ell)) :
    Summable (fun t => absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
      P.memoryWeight r.v t) ∧
    (∑' t, absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  have h := ghostTransition_bounds F r s (fun g => ghostGroupRowFactor F n r.rho d r.v i s g)
    (fun g => by
      have h := ghostRate_bounds F d (P.V g.val) hd (hV g.val)
      rw [funext (ghostGroupRowFactor_eq F n r d i s g)]
      exact ghostGroupFactor_bounds F n r _ _ h.1 h.2 i s g (hV g.val).1 (hbase g) (hmu g))
  obtain ⟨h0, hs, hb⟩ := h
  obtain ⟨hf, hf'⟩ := ghostGroupedSum_bound s (ghostTransitionRowFactor F n r.rho d r.v i s)
    h0 hs (fun t => absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) (fun t => by
      rw [ghostRowTerm_eq_supportedChoiceSum F P J n r d i s t]
      exact Finset.sum_congr rfl fun c _ => ghostRowsChoiceTerm_eq_transitionRowFactor
        F P n r d i s t (fun g => (hV g).1) hbase c)
  exact ⟨hf, hf'.trans hb⟩

private theorem ghostRows_reversed_bound
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    (s : P.MemoryState (J + F.ell)) :
    Summable (fun t => ghostReversalFactor d s t *
      absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ∧
    (∑' t, ghostReversalFactor d s t *
      absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  have h := ghostTransition_bounds F r s (fun g => ghostGroupRevFactor F n r.rho d r.v i s g)
    (fun g => by
      have h := ghostRate_bounds F d (P.V g.val) hd (hV g.val)
      rw [funext (ghostGroupRevFactor_eq F n r d i s g)]
      exact ghostGroupFactor_bounds F n r _ _ h.2 h.1 i s g (hV g.val).1 (hbase g) (hmu g))
  obtain ⟨h0, hs, hb⟩ := h
  obtain ⟨hf, hf'⟩ := ghostGroupedSum_bound s (ghostTransitionRevFactor F n r.rho d r.v i s)
    h0 hs (fun t => ghostReversalFactor d s t *
      absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) (fun t => by
      rw [mul_assoc, ghostRowTerm_eq_supportedChoiceSum F P J n r d i s t, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => ghostReverseSupportedChoiceTerm_eq_transitionRevFactor
        F P n r d hd i s t (fun g => (hV g).1) hbase c)
  exact ⟨hf, hf'.trans hb⟩

theorem GhostRowsTask_proof : GhostRowsTask := by
  intro F P J n r hV hbase hmu d hd i s
  have hforward := ghostRows_forward_bound F P J n r hV hbase hmu d hd i s
  have hreverse := ghostRows_reversed_bound F P J n r hV hbase hmu d hd i s
  exact ⟨hforward.1, hforward.2, hreverse.1, hreverse.2⟩



end Erdos821.S2Core
