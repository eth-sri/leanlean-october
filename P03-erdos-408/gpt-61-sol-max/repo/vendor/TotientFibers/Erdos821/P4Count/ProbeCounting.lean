module
public import Mathlib.Tactic

public import Erdos821.P4Probe.CountingTasks
public import Erdos821.S34.Hoeffding
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Count

noncomputable section

abbrev RowFamily (s M ) := Fin s → Finset (Fin M)

def rowsToFinset {s M } (A : RowFamily s M) : Finset (Fin s × Fin M) :=
  Finset.univ.filter (fun z => z.2 ∈ A z.1)

def finsetToRows {s M } (S : Finset (Fin s × Fin M)) : RowFamily s M :=
  fun i => Finset.univ.filter (fun a => (i, a) ∈ S)

section
variable {s M : ℕ} (A : RowFamily s M)

lemma mem_rowsToFinset     (z : Fin s × Fin M) :
    z ∈ rowsToFinset A ↔ z.2 ∈ A z.1 := by
  simp [rowsToFinset]

lemma rowsToFinset_finsetToRows   (S : Finset (Fin s × Fin M)) :
    rowsToFinset (finsetToRows S) = S := by
  ext z
  simp [rowsToFinset, finsetToRows]

lemma finsetToRows_rowsToFinset     :
    finsetToRows (rowsToFinset A) = A := by
  funext i
  ext a
  simp [finsetToRows, rowsToFinset]

lemma sum_powerset_eq_rows  
    (f : Finset (Fin s × Fin M) → ℝ) (g : RowFamily s M → ℝ)
    (hfg : ∀ S, S ⊆ (Finset.univ : Finset (Fin s × Fin M)) →
      f S = g (finsetToRows S)) :
    (∑ S ∈ (Finset.univ : Finset (Fin s × Fin M)).powerset, f S) =
      ∑ A ∈ (Finset.univ : Finset (RowFamily s M)), g A := by
  classical
  apply Finset.sum_bij (fun S _ => finsetToRows S)
  · intro S hS
    simp
  · grind [rowsToFinset, finsetToRows, rowsToFinset_finsetToRows]
  · intro A hA
    refine ⟨rowsToFinset A, Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    exact finsetToRows_rowsToFinset A
  · intro S hS
    exact hfg S (Finset.mem_powerset.mp hS)

end

noncomputable def permFinsetOfCardEq {M } (A B : Finset (Fin M))
    (h : A.card = B.card) : Equiv.Perm (Fin M) := by
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using h)
  exact Equiv.extendSubtype e

section
variable {s M : ℕ}

lemma map_permFinsetOfCardEq   (A B : Finset (Fin M))
     h  :
    A.map (permFinsetOfCardEq A B h).toEmbedding = B := by
  classical
  unfold permFinsetOfCardEq
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using h)
  change A.map (Equiv.extendSubtype e).toEmbedding = B
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Equiv.extendSubtype_mem e a ha
  · intro hx
    let a : A := e.symm ⟨x, hx⟩
    refine ⟨a, a.2, ?_⟩
    change Equiv.extendSubtype e a = x
    rw [Equiv.extendSubtype_apply_of_mem]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

lemma rowsToFinset_map    A 
     π  :
    (rowsToFinset A).map
        (Erdos821.P4Probe.rowPermutation s M π).toEmbedding =
      rowsToFinset (fun i => (A i).map (π i).toEmbedding) := by
  classical
  ext z
  simp only [Finset.mem_map, mem_rowsToFinset,
    Erdos821.P4Probe.rowPermutation]
  constructor
  · rintro ⟨⟨i, a⟩, ha, hz⟩
    aesop
  · intro hb
    rcases hb with ⟨a, ha, hz⟩
    refine ⟨(z.1, a), ?_, ?_⟩
    · change a ∈ A z.1
      exact ha
    simp_all

lemma energy_eq_of_rowCard_eq  
    (E : Finset (Fin s × Fin M) → ℝ)
    (hinv : ∀ (π : Fin s → Equiv.Perm (Fin M)) S,
      E (S.map (Erdos821.P4Probe.rowPermutation s M π).toEmbedding) = E S)
     A B  (hcard : ∀ i, (A i).card = (B i).card) :
    E (rowsToFinset A) = E (rowsToFinset B) := by
  let π : Fin s → Equiv.Perm (Fin M) := fun i =>
    permFinsetOfCardEq (A i) (B i) (hcard i)
  have hmapi : ∀ i, (A i).map (π i).toEmbedding = B i := by
    solve_by_elim [map_permFinsetOfCardEq]
  calc
    E (rowsToFinset A) =
        E ((rowsToFinset A).map
          (Erdos821.P4Probe.rowPermutation s M π).toEmbedding) :=
            (hinv π (rowsToFinset A)).symm
    _ = E (rowsToFinset B) := by
      rw [rowsToFinset_map]
      exact congrArg E (congrArg rowsToFinset (funext hmapi))

end

def rowProfile {s M } (A : RowFamily s M) : Fin s → Fin (M + 1) :=
  fun i => ⟨(A i).card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ (A i))⟩

abbrev FullFiber {s M } (k ) :=
  {A : RowFamily s M // rowProfile A = k}

noncomputable def fullFiberEquiv {s M : ℕ} (k : Fin s → Fin (M + 1)) :
    FullFiber k ≃ ∀ i, {A : Finset (Fin M) //
      A ∈ (Finset.univ : Finset (Fin M)).powersetCard (k i).val} where
  toFun A i := ⟨A.val i, by
    aesop
  ⟩
  invFun B := ⟨fun i => (B i).val, by
    funext i
    apply Fin.ext
    exact (Finset.mem_powersetCard.mp (B i).property).2
  ⟩
  left_inv A := by
    apply Subtype.ext
    funext i
    rfl
  right_inv B := by
    funext i
    apply Subtype.ext
    rfl

lemma card_fullFiber {s M : ℕ} (k : Fin s → Fin (M + 1)) :
    Fintype.card (FullFiber k) = ∏ i, Nat.choose M (k i).val := by
  rw [Fintype.card_congr (fullFiberEquiv k)]
  simp [Fintype.card_pi]

def allowedCoords (J ell ) : Finset (Fin (J + ell)) :=
  (Finset.univ : Finset (Fin J)).map (Fin.castLEEmb (by omega))

def probeCoords (m J ell : ℕ) : Finset (Fin (J + ell)) :=
  Finset.univ.filter (fun a => a.val < m)

def probePoints {s J ell } (block : Finset (Fin s)) (m : ℕ) :
    Finset (Fin s × Fin (J + ell)) :=
  Finset.univ.filter (fun z => z.1 ∈ block ∧ z.2.val < m)

def tailPoints {s ell } (J ) : Finset (Fin s × Fin (J + ell)) :=
  Finset.univ.filter (fun z => J ≤ z.2.val)

def rowChoices {s J ell } (block : Finset (Fin s)) (m : ℕ)
    (i : Fin s) (j : ℕ)  :=
  ((Finset.univ : Finset (Fin (J + ell))).powersetCard j).filter
    (fun A => A ⊆ allowedCoords J ell ∧ (i ∈ block → probeCoords m J ell ⊆ A))

def selectedRows {s J ell } (block : Finset (Fin s)) (m : ℕ)
    (A : RowFamily s (J + ell))  :=
  ∀ i, A i ⊆ allowedCoords J ell ∧ (i ∈ block → probeCoords m J ell ⊆ A i)

section
variable {m s J ell : ℕ} (a : Fin (J + ell)) (hm : m ≤ J + ell)

lemma mem_allowedCoords     :
    a ∈ allowedCoords J ell ↔ a.val < J := by
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨b, _, hb⟩
    bound
  · intro ha
    refine Finset.mem_map.mpr ⟨⟨a.val, ha⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl

lemma card_allowedCoords  J ell  : (allowedCoords J ell).card = J := by
  simp [allowedCoords]

lemma mem_probeCoords     :
    a ∈ probeCoords m J ell ↔ a.val < m := by
  simp [probeCoords]

lemma probeCoords_subset_allowedCoords   (hmJ : m ≤ J) :
    probeCoords m J ell ⊆ allowedCoords J ell := by
  grind [mem_probeCoords, mem_allowedCoords]

lemma selectedRows_iff   (block : Finset (Fin s))  m 
    (S : Finset (Fin s × Fin (J + ell))) :
    (probePoints block m ⊆ S ∧ Disjoint (tailPoints J) S) ↔
      selectedRows block m (finsetToRows S) := by
  classical
  constructor
  · rintro ⟨hprobe, htail⟩ i
    constructor
    · intro a ha
      have hS : (i, a) ∈ S := by simpa [finsetToRows] using ha
      have hnot : (i, a) ∉ tailPoints J :=
        (Finset.disjoint_right.mp htail) hS
      grind [mem_allowedCoords, hnot, tailPoints]
    grind [mem_probeCoords, probePoints, finsetToRows]
  · intro h
    constructor
    · intro z hz
      rcases z with ⟨i, a⟩
      have hz' := Finset.mem_filter.mp hz
      have hi := hz'.2.1
      have ha : a.val < m := hz'.2.2
      have hrow := (h i).2 hi
      have hmem : a ∈ probeCoords m J ell := by
        rw [mem_probeCoords]
        exact ha
      grind [finsetToRows]
    · apply Finset.disjoint_right.mpr
      intro z hzS hzT
      rcases z with ⟨i, a⟩
      have hrow : a ∈ finsetToRows S i := by
        simpa [finsetToRows] using hzS
      have ha := (h i).1 hrow
      grind [mem_allowedCoords, tailPoints]

lemma probeCoords_eq_map     :
    probeCoords m J ell =
      (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hm) := by
  ext a
  rw [mem_probeCoords, Finset.mem_map]
  constructor
  · intro ha
    refine ⟨⟨a.val, ha⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  aesop

include hm in
lemma card_probeCoords     :
    (probeCoords m J ell).card = m := by
  rw [probeCoords_eq_map hm]
  simp

end

section
variable {s J ell : ℕ} (block : Finset (Fin s)) (m : ℕ) (i : Fin s) (j : ℕ) (hi : i ∈ block)

include hi in
lemma rowChoices_eq_block      
          :
    rowChoices block m i j =
      ((allowedCoords J ell).powersetCard j).filter
        (fun A => probeCoords m J ell ⊆ A) := by
  grind [rowChoices]

lemma rowChoices_eq_outside      
        (hi : i ∉ block) :
    rowChoices block m i j = (allowedCoords J ell).powersetCard j := by
  grind [rowChoices]

include hi in
lemma card_rowChoices_block      
          (hmJ : m ≤ J)
    (hmj : m ≤ j) :
    (rowChoices (s := s) (J := J) (ell := ell) block m i j).card =
      Nat.choose (J - m) (j - m) := by
  rw [rowChoices_eq_block block m i j hi]
  rw [Finset.card_filter_powersetCard_subset
    (probeCoords m J ell) (allowedCoords J ell) j
    (probeCoords_subset_allowedCoords hmJ) (by
      grind [card_probeCoords])]
  grind [card_allowedCoords, card_probeCoords]

include hi in
lemma card_rowChoices_block_zero    
           
    (hm : m ≤ J + ell) (hjm : j < m) :
    (rowChoices (s := s) (J := J) (ell := ell) block m i j).card = 0 := by
  rw [rowChoices_eq_block block m i j hi]
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨A, hA⟩
  have hparts := Finset.mem_filter.mp hA
  have hcard := (Finset.mem_powersetCard.mp hparts.1).2
  have hle := Finset.card_le_card hparts.2
  rw [card_probeCoords hm] at hle
  omega

lemma rowChoices_card_le      
    (hm : 1 ≤ m) (he : 1 ≤ ell) (hmJ : m ≤ J)
    (hM : (m + ell) * (m + ell - 1) ≤ J + ell)
     i   j  (hj : j ≤ J + ell) :
    ((rowChoices (s := s) (J := J) (ell := ell) block m i j).card : ℝ) ≤
      (if i ∈ block then 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell else 1) *
        (Nat.choose (J + ell) j : ℝ) := by
  classical
  by_cases hi : i ∈ block
  · simp only [ite_eq_left hi]
    by_cases hmj : m ≤ j
    · by_cases hjJ : j ≤ J
      · rw [card_rowChoices_block (s := s) (J := J) (ell := ell)
          block m i j hi hmJ hmj]
        have hml : m + ell ≤ J + ell := by omega
        have hje : j + ell ≤ J + ell := by omega
        have hf := Erdos821.S34.Proofs.hoeffding_fraction
          (J + ell) m ell j hml hmj hje
        have hnum : (J + ell) - m - ell = J - m := by omega
        rw [hnum] at hf
        have hb := Erdos821.S34.Proofs.hoeffding_fraction_bound
          (J + ell) m ell j hm he hM (by omega)
        have hratio :
            (Nat.choose (J - m) (j - m) : ℝ) /
              Nat.choose (J + ell) j ≤ 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell :=
          hf.trans_le hb
        have hden : 0 < (Nat.choose (J + ell) j : ℝ) := by
          exact_mod_cast Nat.choose_pos (by omega)
        exact (div_le_iff₀ hden).mp hratio
      · rw [card_rowChoices_block (s := s) (J := J) (ell := ell)
          block m i j hi hmJ hmj]
        have hzero : Nat.choose (J - m) (j - m) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          omega
        simp [hzero]
        positivity
    · have hzero := card_rowChoices_block_zero (s := s) (J := J) (ell := ell)
        block m i j hi (by omega) (by omega)
      rw [hzero]
      have hnum : (0 : ℝ) ≤ 2 * (ell : ℝ) ^ ell := by positivity
      have hden : (0 : ℝ) ≤ (m : ℝ) ^ ell := by positivity
      have hchoose : (0 : ℝ) ≤ (Nat.choose (J + ell) j : ℝ) := by positivity
      simpa using mul_nonneg (div_nonneg hnum hden) hchoose
  · simp only [ite_eq_right hi, one_mul]
    rw [rowChoices_eq_outside (s := s) (J := J) (ell := ell) block m i j hi]
    have hsub :
        (allowedCoords J ell).powersetCard j ⊆
          (Finset.univ : Finset (Fin (J + ell))).powersetCard j :=
      Finset.powersetCard_mono (Finset.subset_univ _)
    have hcard := Finset.card_le_card hsub
    have hcard' :
        ((allowedCoords J ell).powersetCard j).card ≤
          ((Finset.univ : Finset (Fin (J + ell))).powersetCard j).card := hcard
    exact_mod_cast (by simpa [Finset.card_powersetCard, card_allowedCoords] using hcard')

end

abbrev SelectedFiber {s J ell } (block ) (m )
    (k ) :=
  {A : RowFamily s (J + ell) // rowProfile A = k ∧ selectedRows block m A}

noncomputable def selectedFiberEquiv {s J ell : ℕ} (block : Finset (Fin s))
    (m : ℕ) (k : Fin s → Fin (J + ell + 1)) :
    SelectedFiber block m k ≃ ∀ i, {A : Finset (Fin (J + ell)) //
      A ∈ rowChoices block m i (k i).val} where
  toFun A i := ⟨A.val i, by
    have hcard := congrArg Fin.val (congrFun A.property.1 i)
    change (A.val i).card = (k i).val at hcard
    simp only [rowChoices, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, hcard⟩, A.property.2 i⟩
  ⟩
  invFun B := ⟨fun i => (B i).val, by
    constructor
    · funext i
      apply Fin.ext
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp (B i).property).1).2
    · intro i
      exact (Finset.mem_filter.mp (B i).property).2
  ⟩
  left_inv A := by
    apply Subtype.ext
    funext i
    rfl
  right_inv B := by
    funext i
    apply Subtype.ext
    rfl

lemma card_selectedFiber {s J ell : ℕ}  block   m 
    (k : Fin s → Fin (J + ell + 1)) :
    Fintype.card (SelectedFiber block m k) =
      ∏ i, (rowChoices (s := s) (J := J) (ell := ell) block m i (k i).val).card := by
  rw [Fintype.card_congr (selectedFiberEquiv block m k)]
  simp [Fintype.card_pi, Fintype.card_coe]

def canonicalRows {s M } (k : Fin s → Fin (M + 1)) : RowFamily s M :=
  fun i => (Finset.univ : Finset (Fin (k i).val)).map
    (Fin.castLEEmb (by omega : (k i).val ≤ M))

lemma canonicalRows_card {s M : ℕ} (k : Fin s → Fin (M + 1)) (i : Fin s) :
    (canonicalRows k i).card = (k i).val := by
  simp [canonicalRows]

def profileFinset {s M } (k : Fin s → Fin (M + 1))  :=
  Finset.univ.filter (fun A => rowProfile A = k)

def selectedProfileFinset {s J ell } (block : Finset (Fin s)) (m : ℕ)
    (k : Fin s → Fin (J + ell + 1))  :=
  Finset.univ.filter (fun A => rowProfile A = k ∧ selectedRows block m A)

noncomputable def fullFiberFinsetEquiv {s M : ℕ} (k : Fin s → Fin (M + 1)) :
    FullFiber k ≃ ↥(profileFinset k) where
  toFun A := ⟨A.val, by simp [profileFinset, A.property]⟩
  invFun A := ⟨A.val, by simpa [profileFinset] using A.property⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl

lemma card_profileFinset {s M : ℕ} (k : Fin s → Fin (M + 1)) :
    (profileFinset k).card = Fintype.card (FullFiber k) := by
  calc
    (profileFinset k).card = Fintype.card ↥(profileFinset k) := by simp
    _ = Fintype.card (FullFiber k) :=
      (Fintype.card_congr (fullFiberFinsetEquiv k)).symm

noncomputable def selectedFiberFinsetEquiv {s J ell : ℕ}
    (block : Finset (Fin s)) (m : ℕ) (k : Fin s → Fin (J + ell + 1)) :
    SelectedFiber block m k ≃ ↥(selectedProfileFinset block m k) where
  toFun A := ⟨A.val, by simp [selectedProfileFinset, A.property]⟩
  invFun A := ⟨A.val, by simpa [selectedProfileFinset] using A.property⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl

section
variable {s J ell : ℕ} (block : Finset (Fin s)) (m : ℕ) (hm : 1 ≤ m) (he : 1 ≤ ell) (hmJ : m ≤ J) (hM : (m + ell) * (m + ell - 1) ≤ J + ell) (k : Fin s → Fin (J + ell + 1)) {M : ℕ}

lemma card_selectedProfileFinset    
        :
    (selectedProfileFinset block m k).card =
      Fintype.card (SelectedFiber block m k) := by
  calc
    (selectedProfileFinset block m k).card =
        Fintype.card ↥(selectedProfileFinset block m k) := by simp
    _ = Fintype.card (SelectedFiber block m k) :=
      (Fintype.card_congr (selectedFiberFinsetEquiv block m k)).symm

include hm he hmJ hM in
lemma selectedFiber_card_le    
           
     
      :
    (Fintype.card (SelectedFiber block m k) : ℝ) ≤
      (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
        (Fintype.card (FullFiber k) : ℝ) := by
  classical
  let β : ℝ := 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell
  have hprod :
      (∏ i : Fin s, (rowChoices (s := s) (J := J) (ell := ell)
          block m i (k i).val).card : ℝ) ≤
        ∏ i : Fin s,
          (if i ∈ block then β else 1) *
            (Nat.choose (J + ell) (k i).val : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    grind [rowChoices_card_le]
  have hsplit :
      (∏ i : Fin s,
        (if i ∈ block then β else 1) * (Nat.choose (J + ell) (k i).val : ℝ)) =
        (∏ i : Fin s, if i ∈ block then β else 1) *
          ∏ i : Fin s, (Nat.choose (J + ell) (k i).val : ℝ) :=
    Finset.prod_mul_distrib
  have hfactor :
      (∏ i : Fin s, if i ∈ block then β else (1 : ℝ)) = β ^ block.card := by
    rw [Finset.prod_ite]
    simp
  have hsel :
      (Fintype.card (SelectedFiber block m k) : ℝ) =
        ∏ i : Fin s,
          ((rowChoices (s := s) (J := J) (ell := ell)
            block m i (k i).val).card : ℝ) := by
    rw [card_selectedFiber]
    simp only [Nat.cast_prod]
  have hfull :
      (Fintype.card (FullFiber k) : ℝ) =
        ∏ i : Fin s, (Nat.choose (J + ell) (k i).val : ℝ) := by
    rw [card_fullFiber]
    simp
  grind

lemma selectedProfileFinset_eq_filter  
          :
    selectedProfileFinset block m k =
      (profileFinset k).filter (selectedRows block m) := by
  ext A
  simp [selectedProfileFinset, profileFinset, and_comm]

lemma profileSum_total  
    (E : Finset (Fin s × Fin M) → ℝ)
    (hinv : ∀ (π : Fin s → Equiv.Perm (Fin M)) S,
      E (S.map (Erdos821.P4Probe.rowPermutation s M π).toEmbedding) = E S)
     k  :
    (∑ A ∈ profileFinset k, E (rowsToFinset A)) =
      (profileFinset k).card • E (rowsToFinset (canonicalRows k)) := by
  apply Finset.sum_eq_card_nsmul
  intro A hA
  have hprof : rowProfile A = k := (Finset.mem_filter.mp hA).2
  apply energy_eq_of_rowCard_eq E hinv A (canonicalRows k)
  intro i
  have hcard := congrArg Fin.val (congrFun hprof i)
  change (A i).card = (k i).val at hcard
  rw [canonicalRows_card]
  exact hcard

end

section
variable {s J ell : ℕ} (E : Finset (Fin s × Fin (J + ell)) → ℝ) (hnonneg : ∀ S, 0 ≤ E S) (hinv : ∀ (π : Fin s → Equiv.Perm (Fin (J + ell))) S,
      E (S.map (Erdos821.P4Probe.rowPermutation s (J + ell) π).toEmbedding) = E S) (block : Finset (Fin s)) (m : ℕ) (hm : 1 ≤ m) (he : 1 ≤ ell) (hmJ : m ≤ J) (hM : (m + ell) * (m + ell - 1) ≤ J + ell) (k : Fin s → Fin (J + ell + 1)) {M : ℕ}

include hinv in
lemma profileSum_selected  
     
     
          :
    (∑ A ∈ profileFinset k,
      if selectedRows block m A then E (rowsToFinset A) else 0) =
      (selectedProfileFinset block m k).card •
        E (rowsToFinset (canonicalRows k)) := by
  calc
    (∑ A ∈ profileFinset k,
      if selectedRows block m A then E (rowsToFinset A) else 0) =
        ∑ A ∈ (profileFinset k).filter (selectedRows block m), E (rowsToFinset A) :=
          (Finset.sum_filter (s := profileFinset k)
            (p := selectedRows block m) (f := fun A => E (rowsToFinset A))).symm
    _ = ∑ A ∈ selectedProfileFinset block m k, E (rowsToFinset A) := by
      rw [selectedProfileFinset_eq_filter]
    _ = (selectedProfileFinset block m k).card •
          E (rowsToFinset (canonicalRows k)) := by
      apply Finset.sum_eq_card_nsmul
      intro A hA
      have hprof : rowProfile A = k := (Finset.mem_filter.mp hA).2.1
      apply energy_eq_of_rowCard_eq E hinv A (canonicalRows k)
      intro i
      have hcard := congrArg Fin.val (congrFun hprof i)
      change (A i).card = (k i).val at hcard
      rw [canonicalRows_card]
      exact hcard

include hnonneg hinv hm he hmJ hM in
lemma profileContribution_le  
     
     
     
           
       
      :
    (∑ A ∈ profileFinset k,
      if selectedRows block m A then E (rowsToFinset A) else 0) ≤
      (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
        ∑ A ∈ profileFinset k, E (rowsToFinset A) := by
  have hcount :
      ((selectedProfileFinset block m k).card : ℝ) ≤
        (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ((profileFinset k).card : ℝ) := by
    simpa [card_selectedProfileFinset, card_profileFinset] using
      selectedFiber_card_le block m hm he hmJ hM k
  let e : ℝ := E (rowsToFinset (canonicalRows k))
  have he0 : 0 ≤ e := by dsimp [e]; exact hnonneg _
  rw [profileSum_selected E hinv block m k, profileSum_total E hinv k]
  simp only [nsmul_eq_mul]
  calc
    ((selectedProfileFinset block m k).card : ℝ) * e =
        ((selectedProfileFinset block m k).card : ℝ) * e := rfl
    _ ≤ ((2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ((profileFinset k).card : ℝ)) * e :=
        mul_le_mul_of_nonneg_right hcount he0
    _ = (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          (((profileFinset k).card : ℝ) * e) := by ring

lemma sum_eq_profileFibers   (f : RowFamily s M → ℝ) :
    (∑ A ∈ (Finset.univ : Finset (RowFamily s M)), f A) =
      ∑ k : Fin s → Fin (M + 1), ∑ A ∈ profileFinset k, f A := by
  classical
  have h := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (RowFamily s M))) (g := rowProfile) (f := f)
  simpa [profileFinset] using h.symm

end

end
end Erdos821.P4Count

theorem Erdos821.P4Probe.ProbeCountingTask_proof :
    Erdos821.P4Probe.ProbeCountingTask := by
  classical
  intro s J ell m block E hm he hmJ hM hnonneg hinv
  change
    (∑ S ∈ (Finset.univ : Finset (Fin s × Fin (J + ell))).powerset,
      if Erdos821.P4Count.probePoints block m ⊆ S ∧
          Disjoint (Erdos821.P4Count.tailPoints J) S then E S else 0) ≤
      (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
        ∑ S ∈ (Finset.univ : Finset (Fin s × Fin (J + ell))).powerset, E S
  have hleft :
      (∑ S ∈ (Finset.univ : Finset (Fin s × Fin (J + ell))).powerset,
        if Erdos821.P4Count.probePoints block m ⊆ S ∧
            Disjoint (Erdos821.P4Count.tailPoints J) S then E S else 0) =
        ∑ A ∈ (Finset.univ : Finset
            (Erdos821.P4Count.RowFamily s (J + ell))),
          if Erdos821.P4Count.selectedRows block m A then
            E (Erdos821.P4Count.rowsToFinset A) else 0 := by
    apply Erdos821.P4Count.sum_powerset_eq_rows
    intro S hS
    rw [Erdos821.P4Count.rowsToFinset_finsetToRows]
    grind [Erdos821.P4Count.selectedRows_iff, Erdos821.P4Count.probePoints, Disjoint, Erdos821.P4Count.tailPoints, Erdos821.P4Count.selectedRows, Erdos821.P4Count.finsetToRows]
  have htotal :
      (∑ S ∈ (Finset.univ : Finset (Fin s × Fin (J + ell))).powerset, E S) =
        ∑ A ∈ (Finset.univ : Finset
            (Erdos821.P4Count.RowFamily s (J + ell))),
          E (Erdos821.P4Count.rowsToFinset A) := by
    grind [Erdos821.P4Count.sum_powerset_eq_rows, Erdos821.P4Count.rowsToFinset_finsetToRows]
  have hfamily :
      (∑ A ∈ (Finset.univ : Finset
          (Erdos821.P4Count.RowFamily s (J + ell))),
        if Erdos821.P4Count.selectedRows block m A then
          E (Erdos821.P4Count.rowsToFinset A) else 0) ≤
        (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ∑ A ∈ (Finset.univ : Finset
              (Erdos821.P4Count.RowFamily s (J + ell))),
            E (Erdos821.P4Count.rowsToFinset A) := by
    let fsel : Erdos821.P4Count.RowFamily s (J + ell) → ℝ := fun A =>
      if Erdos821.P4Count.selectedRows block m A then
        E (Erdos821.P4Count.rowsToFinset A) else 0
    let ftotal : Erdos821.P4Count.RowFamily s (J + ell) → ℝ := fun A =>
      E (Erdos821.P4Count.rowsToFinset A)
    change (∑ A ∈ (Finset.univ : Finset
          (Erdos821.P4Count.RowFamily s (J + ell))), fsel A) ≤
        (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ∑ A ∈ (Finset.univ : Finset
            (Erdos821.P4Count.RowFamily s (J + ell))), ftotal A
    calc
      (∑ A ∈ (Finset.univ : Finset
          (Erdos821.P4Count.RowFamily s (J + ell))), fsel A) =
        ∑ k : Fin s → Fin (J + ell + 1),
          ∑ A ∈ Erdos821.P4Count.profileFinset k, fsel A :=
            Erdos821.P4Count.sum_eq_profileFibers fsel
      _ ≤
        ∑ k : Fin s → Fin (J + ell + 1),
          (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
            ∑ A ∈ Erdos821.P4Count.profileFinset k, ftotal A := by
              apply Finset.sum_le_sum
              intro k hk
              simpa [fsel, ftotal] using
                Erdos821.P4Count.profileContribution_le E hnonneg hinv
                  block m hm he hmJ hM k
      _ = (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ∑ k : Fin s → Fin (J + ell + 1),
            ∑ A ∈ Erdos821.P4Count.profileFinset k, ftotal A := by
              rw [Finset.mul_sum]
      _ = (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ∑ A ∈ (Finset.univ : Finset
              (Erdos821.P4Count.RowFamily s (J + ell))), ftotal A := by
              rw [← Erdos821.P4Count.sum_eq_profileFibers ftotal]
  rw [hleft, htotal]
  exact hfamily
