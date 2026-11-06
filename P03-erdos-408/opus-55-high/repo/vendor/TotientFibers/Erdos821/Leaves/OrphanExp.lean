module

public import Erdos821.Blueprint.Graph
public import Erdos821.Blueprint.Analytic

@[expose] public section


attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

theorem fin_tail_filter (n : ℕ) (j : Fin n) :
    (Finset.univ.filter (fun i : Fin (n+1) => j.castSucc < i))
    = insert (Fin.last n) (Finset.image Fin.castSucc
      (Finset.univ.filter (fun i : Fin n => j < i))) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hi
    by_cases hlast : i = Fin.last n
    · omega
    · right
      have hex :=
        Fin.exists_castSucc_eq.mpr hlast
      grind
  grind

theorem fin_last_tail_empty (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n+1) => Fin.last n < i)) = ∅ := by
  grind

theorem fin_prefix {R : Type*} [CommRing R] (n : ℕ) (f : Fin n → R) :
    (∏ i, (1 - f i)) =
      1 - ∑ j, f j * ∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : (∏ i : Fin (n+1), (1 - f i))
        = (∏ i : Fin n, (1 - f i.castSucc)) * (1 - f (Fin.last n)) := by
      rw [Fin.prod_univ_castSucc]
    have htail : ∀ j : Fin n,
        (∏ i ∈ Finset.univ.filter (fun i : Fin (n+1) => j.castSucc < i), (1 - f i))
        = (∏ i ∈ Finset.univ.filter (fun i : Fin n => j < i), (1 - f i.castSucc))
          * (1 - f (Fin.last n)) := by
      intro j
      rw [fin_tail_filter n j]
      have hlast_not : Fin.last n ∉ Finset.image Fin.castSucc
          (Finset.univ.filter (fun i : Fin n => j < i)) := by
        intro hcon
        obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp hcon
        have hne : i0.castSucc ≠ Fin.last n := by
          intro hcontra
          have hex : ∃ k : Fin n, k.castSucc = Fin.last n := by grind
          have := (Fin.exists_castSucc_eq.mp hex)
          exact this rfl
        exact hne hi0
      rw [Finset.prod_insert hlast_not,
        Finset.prod_image (by simp)]
      ring
    have hempty : (∏ i ∈ Finset.univ.filter (fun i : Fin (n+1) => Fin.last n < i),
        (1 - f i)) = 1 := by
      rw [fin_last_tail_empty]
      exact Finset.prod_empty
    have hsum : (∑ j : Fin (n+1), f j * ∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i))
        = (∑ j : Fin n, f j.castSucc * (∏ i ∈ Finset.univ.filter (fun i => j < i), (1 - f i.castSucc)))
          * (1 - f (Fin.last n)) + f (Fin.last n) := by
      rw [Fin.sum_univ_castSucc]
      simp only [hempty, mul_one]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [htail j, mul_assoc]
    have ih' := ih (fun i : Fin n => f i.castSucc)
    grind

theorem fin_interval_stable (n : ℕ) (j i : Fin n) :
    (Finset.univ.filter (fun t : Fin (n+1) => j.castSucc < t ∧ t < i.castSucc))
    = Finset.image Fin.castSucc (Finset.univ.filter (fun t : Fin n => j < t ∧ t < i)) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨hlt, htu⟩ := ht
    have hne := ne_of_lt (lt_of_lt_of_le htu (Fin.le_last _))
    have hex := Fin.exists_castSucc_eq.mpr hne
    grind
  grind

theorem fin_tail_interval (n : ℕ) (j : Fin n) :
    (Finset.univ.filter (fun t : Fin (n+1) => j.castSucc < t ∧ t < Fin.last n))
    = Finset.image Fin.castSucc (Finset.univ.filter (fun t : Fin n => j < t)) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨hlt, htu⟩ := ht
    have hne := ne_of_lt htu
    have hex := Fin.exists_castSucc_eq.mpr hne
    grind
  grind

theorem fin_orphan {R : Type*} [CommRing R] (n : ℕ) (f : Fin n → R) :
    (∏ i, (1 - f i)) =
      1 - (∑ i, f i) +
        ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          f j * f i * ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i), (1 - f t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : (∏ i : Fin (n+1), (1 - f i))
        = (∏ i : Fin n, (1 - f i.castSucc)) * (1 - f (Fin.last n)) := by
      rw [Fin.prod_univ_castSucc]
    have hS : (∑ i : Fin (n+1), f i)
        = (∑ i : Fin n, f i.castSucc) + f (Fin.last n) := by
      rw [Fin.sum_univ_castSucc]
    have hinner : ∀ j : Fin n,
        (∑ i ∈ Finset.univ.filter (fun i : Fin (n+1) => j.castSucc < i),
          f j.castSucc * f i * ∏ t ∈ Finset.univ.filter (fun t : Fin (n+1) => j.castSucc < t ∧ t < i), (1 - f t))
        = (∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          f j.castSucc * f i.castSucc * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i), (1 - f t.castSucc))
          + f j.castSucc * f (Fin.last n) * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t), (1 - f t.castSucc) := by
      intro j
      rw [fin_tail_filter n j]
      have hlast_not : Fin.last n ∉ Finset.image Fin.castSucc
          (Finset.univ.filter (fun i : Fin n => j < i)) := by
        intro hcon
        obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp hcon
        have hne : i0.castSucc ≠ Fin.last n := by
          intro hcontra
          have hex : ∃ k : Fin n, k.castSucc = Fin.last n := by grind
          have := (Fin.exists_castSucc_eq.mp hex)
          exact this rfl
        exact hne hi0
      rw [Finset.sum_insert hlast_not, add_comm]
      congr 1
      · rw [Finset.sum_image (by simp)]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [fin_interval_stable n j i,
          Finset.prod_image (by simp)]
      · have hlast_prod : (∏ t ∈ Finset.univ.filter
            (fun t : Fin (n+1) => j.castSucc < t ∧ t < Fin.last n), (1 - f t))
            = ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t), (1 - f t.castSucc) := by
          rw [fin_tail_interval n j,
            Finset.prod_image (by simp)]
        simp_all
    have hempty_inner : (∑ i ∈ Finset.univ.filter (fun i : Fin (n+1) => Fin.last n < i),
        f (Fin.last n) * f i * ∏ t ∈ Finset.univ.filter (fun t : Fin (n+1) => Fin.last n < t ∧ t < i), (1 - f t)) = 0 := by
      rw [fin_last_tail_empty]
      exact Finset.sum_empty
    have hD : (∑ j : Fin (n+1), ∑ i ∈ Finset.univ.filter (fun i : Fin (n+1) => j < i),
          f j * f i * ∏ t ∈ Finset.univ.filter (fun t : Fin (n+1) => j < t ∧ t < i), (1 - f t))
        = (∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          f j.castSucc * f i.castSucc * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i), (1 - f t.castSucc))
          + f (Fin.last n) * (∑ j : Fin n, f j.castSucc * ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t), (1 - f t.castSucc)) := by
      rw [Fin.sum_univ_castSucc, hempty_inner, add_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hinner j]
      ring
    have hpref := fin_prefix n (fun i : Fin n => f i.castSucc)
    grind

variable {p n : ℕ} [NeZero p]

theorem single_avg_swap (h : Fin n → ZMod p) (η : Fin n → ℝ) :
    (∑ r : ZMod p, ∑ i : Fin n, η i * (if r + h i = 0 then (1:ℝ) else 0))
    = ∑ i : Fin n, η i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  have h1 : (∑ r : ZMod p, (if r + h i = 0 then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single (-h i)]
    · simp
    · grind
    · simp
  simp_all

theorem avg_one2 : ((p : ℝ)⁻¹ * ∑ _r : ZMod p, (1 : ℝ)) = 1 := by
  simp

theorem double_residue_sum2 (h : Fin n → ZMod p) (η : Fin n → ℝ)
    (j : Fin n) (i : Fin n) :
    (∑ r : ZMod p,
      ((if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
          (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))))
    = ((if h j = h i then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
          (1 - η t * (if h t = h j then (1:ℝ) else 0))) := by
  by_cases heq : h j = h i
  · have hprod : ∀ r : ZMod p,
        (if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0)
        = (if r + h i = 0 then (1:ℝ) else 0) := by
      intro r
      by_cases hr : r + h i = 0
      · simp_all
      · simp_all
    simp only [hprod]
    rw [ite_eq_left heq, one_mul]
    rw [Finset.sum_eq_single (-h i)]
    · grind
    · grind
    simp
  · rw [ite_eq_right heq, zero_mul]
    apply Finset.sum_eq_zero
    grind

theorem double_avg_swap2 (h : Fin n → ZMod p) (η : Fin n → ℝ) :
    (∑ r : ZMod p, ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j < i),
      η j * η i *
        (((if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
          (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))))
    = ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j < i),
      η j * η i *
        (((if h j = h i then (1:ℝ) else 0) *
        ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
          (1 - η t * (if h t = h j then (1:ℝ) else 0)))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [← Finset.mul_sum]
  congr 1
  exact double_residue_sum2 h η j i

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Graph

theorem orphan_expansion (p n : ℕ) [NeZero p] (η : Fin n → ℝ) (h : Fin n → ZMod p) :
    ((p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i, (1 - η i * if r + h i = 0 then 1 else 0)) =
      1 - (p : ℝ)⁻¹ * ∑ i, η i + (p : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          η j * η i * (if h j = h i then 1 else 0) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
              (1 - η t * if h t = h j then 1 else 0) := by
  have hfin : ∀ r : ZMod p,
      (∏ i, (1 - η i * (if r + h i = 0 then (1:ℝ) else 0)))
      = 1 - (∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)) := by
    intro r
    have hh := Erdos821.GraphLemmas.fin_orphan n (fun i => η i * (if r + h i = 0 then (1:ℝ) else 0))
    simpa [mul_assoc] using hh
  -- sum over r
  have hsum : (∑ r : ZMod p, ∏ i, (1 - η i * (if r + h i = 0 then (1:ℝ) else 0)))
      = (∑ _r : ZMod p, (1:ℝ)) - (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))) := by
    calc (∑ r : ZMod p, ∏ i, (1 - η i * (if r + h i = 0 then (1:ℝ) else 0)))
        = ∑ r : ZMod p, (1 - (∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
          (∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
            (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
            (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
            ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
              (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))) := by
          apply Finset.sum_congr rfl
          intro r _
          exact hfin r
      _ = ((∑ _r : ZMod p, (1:ℝ)) - (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
          (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
            (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
            (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
            ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
              (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- factor double sum summands to match double_avg_swap2 form
  have hDrew : (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))
      = (∑ r : ZMod p, ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => j < i),
        η j * η i *
          (((if r + h j = 0 then (1:ℝ) else 0) * (if r + h i = 0 then (1:ℝ) else 0) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))))) := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hS := Erdos821.GraphLemmas.single_avg_swap h η
  have hD := Erdos821.GraphLemmas.double_avg_swap2 h η
  have h1 := Erdos821.GraphLemmas.avg_one2 (p := p)
  -- combine: multiply by (p:ℝ)⁻¹ and distribute
  calc ((p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i, (1 - η i * if r + h i = 0 then 1 else 0))
      = (p:ℝ)⁻¹ * ((∑ _r : ZMod p, (1:ℝ)) - (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0)))) := by
        grind
    _ = ((p:ℝ)⁻¹ * ∑ _r : ZMod p, (1:ℝ)) - (p:ℝ)⁻¹ * (∑ r : ZMod p, ∑ i, η i * (if r + h i = 0 then (1:ℝ) else 0)) +
        (p:ℝ)⁻¹ * (∑ r : ZMod p, ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j < i),
          (η j * (if r + h j = 0 then (1:ℝ) else 0)) *
          (η i * (if r + h i = 0 then (1:ℝ) else 0)) *
          ∏ t ∈ Finset.univ.filter (fun t => j < t ∧ t < i),
            (1 - η t * (if r + h t = 0 then (1:ℝ) else 0))) := by
        ring
    _ = 1 - (p:ℝ)⁻¹ * ∑ i, η i + (p:ℝ)⁻¹ *
        ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),
          η j * η i * (if h j = h i then 1 else 0) *
            ∏ t ∈ Finset.univ.filter (fun t : Fin n => j < t ∧ t < i),
              (1 - η t * if h t = h j then 1 else 0) := by
        rw [h1, hS, hDrew, hD]
        ring_nf

end Erdos821.Blueprint.Graph
