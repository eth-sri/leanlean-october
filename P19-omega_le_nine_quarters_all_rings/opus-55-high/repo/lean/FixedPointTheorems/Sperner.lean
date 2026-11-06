
import Mathlib



open Finset

/-- Vertex `j` of the Kuhn simplex with base `b` and ordering `σ`. -/
def kv {m : ℕ} (b : Fin m → ℕ) (σ : Equiv.Perm (Fin m)) (j : ℕ) (k : Fin m) : ℕ :=
  b k + if (σ k : ℕ) < j then 1 else 0

lemma door_parity (m : ℕ) (ℓ : ℕ → ℕ) (h : ∀ j, ℓ j ≤ m) :
    (#{i ∈ range (m + 1) | ∀ c < m, ∃ j ≤ m, j ≠ i ∧ ℓ j = c} : ZMod 2) =
      if ∀ c ≤ m, ∃ j ≤ m, ℓ j = c then 1 else 0 := by
  have hD : ∀ k ≤ m, (∀ c < m, ∃ j ≤ m, j ≠ k ∧ ℓ j = c) →
      ((range (m + 1)).erase k).image ℓ = range m ∧ Set.InjOn ℓ ((range (m + 1)).erase k) := by
    intro k hk hd
    have hs : range m ⊆ ((range (m + 1)).erase k).image ℓ := fun c hc => by grind
    have hc : #(((range (m + 1)).erase k).image ℓ) ≤ #(range m) :=
      card_image_le.trans (by grind)
    have e := eq_of_subset_of_card_le hs hc
    grind
  split_ifs with hc
  · obtain ⟨i, hi, hl⟩ := hc m le_rfl
    rw [show {i ∈ range (m + 1) | ∀ c < m, ∃ j ≤ m, j ≠ i ∧ ℓ j = c} = {i} from ?_]; · simp
    ext k
    simp
    refine ⟨fun ⟨hk, hd⟩ => by_contra fun hki => ?_, ?_⟩
    · have := (hD k (by omega) hd).1 ▸ mem_image_of_mem ℓ (mem_erase.2 ⟨Ne.symm hki, mem_range.2 (by omega)⟩)
      simp [hl] at this
    rintro rfl
    exact ⟨by omega, fun c hc' => (hc c hc'.le).imp fun j ⟨hj, h'⟩ => ⟨hj, by grind, h'⟩⟩
  by_cases he : ∃ i ≤ m, ∀ c < m, ∃ j ≤ m, j ≠ i ∧ ℓ j = c
  · obtain ⟨i, hi, hd⟩ := he
    obtain ⟨e, -⟩ := hD i hi hd
    have hli := lt_of_le_of_ne (h i) fun hl => hc fun c hc' => hc'.lt_or_eq.elim
      (fun h' => (hd c h').imp fun j ⟨hj, _, h''⟩ => ⟨hj, h''⟩) fun h' => ⟨i, hi, hl.trans h'.symm⟩
    obtain ⟨j, hj, hjl⟩ := mem_image.1 (e ▸ mem_range.2 hli : ℓ i ∈ _)
    rw [mem_erase, mem_range] at hj
    rw [show {i ∈ range (m + 1) | ∀ c < m, ∃ j ≤ m, j ≠ i ∧ ℓ j = c} = {i, j} from ?_]
    · rw [card_pair hj.1.symm]; decide
    ext k; simp
    refine ⟨fun ⟨hk, hdk⟩ => by_contra fun hk' => ?_, ?_⟩
    · simp at hk'
      exact hj.1 ((hD k (by omega) hdk).2 (mem_erase.2 ⟨Ne.symm hk'.2, mem_range.2 hj.2⟩)
        (mem_erase.2 ⟨Ne.symm hk'.1, mem_range.2 (by omega)⟩) hjl)
    rintro (rfl | rfl) <;> grind
  rw [filter_eq_empty_iff.2 fun i hi hd => he ⟨i, by grind, hd⟩]; rfl

theorem sperner (p : ℕ) (hp : 0 < p) (m : ℕ) (L : (Fin m → ℕ) → ℕ) (h0 : ∀ x, L x ≤ m)
    (h1 : ∀ x (k : Fin m), x k = 0 → L x + k + 1 ≠ m) (h2 : ∀ x (k : Fin m), x k = p → L x + k < m) :
    (#{s ∈ Fintype.piFinset (fun _ => range p) ×ˢ (univ : Finset (Equiv.Perm (Fin m))) |
      ∀ c ≤ m, ∃ j ≤ m, L (kv s.1 s.2 j) = c} : ZMod 2) = 1 := by
  induction m with
  | zero =>
    rw [filter_true_of_mem fun s _ c hc => ⟨0, le_rfl, by grind⟩]
    simp
  | succ n ih =>
    let N : ((Fin (n + 1) → ℕ) × Equiv.Perm (Fin (n + 1))) × ℕ → ((Fin (n + 1) → ℕ) × Equiv.Perm (Fin (n + 1))) × ℕ :=
      fun x => if x.2 = 0 then ((fun k => x.1.1 k + if (x.1.2 k : ℕ) = 0 then 1 else 0,
          x.1.2.trans (finRotate _).symm), n + 1)
        else if x.2 = n + 1 then ((fun k => x.1.1 k - if (x.1.2 k : ℕ) = n then 1 else 0,
          x.1.2.trans (finRotate _)), 0)
        else ((x.1.1, x.1.2.trans (Equiv.swap (Fin.ofNat _ (x.2 - 1)) (Fin.ofNat _ x.2))), x.2)
    have hinv : ∀ b σ i, i < n + 2 → (i = n + 1 → ∀ k, (σ k : ℕ) = n → b k ≠ 0) → N (N ((b, σ), i)) = ((b, σ), i) := by
      intro b σ i hi hb
      rcases (show i = 0 ∨ i = n + 1 ∨ (0 < i ∧ i < n + 1) by omega) with rfl | rfl | hi
      · simp only [N, ite_true, Nat.add_one_ne_zero, ite_false]
        ext k <;> simp only [Equiv.trans_apply, Fin.ext_iff, coe_finRotate, finRotate_symm_apply,
          Fin.coe_sub_one, Fin.val_last, Fin.val_zero] <;> split_ifs <;> omega
      · simp only [N, ite_true, Nat.add_one_ne_zero, ite_false]
        ext k <;> simp only [Equiv.trans_apply, Fin.ext_iff, coe_finRotate, 
          Fin.val_last, Equiv.symm_apply_apply] <;> split_ifs <;>
          have := hb rfl k <;> first | omega | simp_all
      ext <;> simp [N, hi.1.ne', hi.2.ne]
    have hv : ∀ b σ i, i < n + 2 → (i = n + 1 → ∀ k, (σ k : ℕ) = n → b k ≠ 0) → ∀ j ≤ n + 1, j ≠ i →
        ∃ j' ≤ n + 1, j' ≠ (N ((b, σ), i)).2 ∧ kv (N ((b, σ), i)).1.1 (N ((b, σ), i)).1.2 j' = kv b σ j := by
      intro b σ i hi hb j hj hji
      rcases (show i = 0 ∨ i = n + 1 ∨ (0 < i ∧ i < n + 1) by omega) with rfl | rfl | hi
      · refine ⟨j - 1, by omega, by grind, funext fun k => ?_⟩
        simp only [N, kv, ite_true, Equiv.trans_apply, finRotate_symm_apply,
          Fin.coe_sub_one, Fin.val_zero, Fin.ext_iff]
        split_ifs <;> omega
      · refine ⟨j + 1, by omega, by grind, funext fun k => ?_⟩
        simp only [N, kv, ite_true, Nat.add_one_ne_zero, ite_false, Equiv.trans_apply, coe_finRotate, Fin.ext_iff, Fin.val_last]
        grind
      refine ⟨j, hj, by simp [N, hi.1.ne', hi.2.ne, hji], funext fun k => ?_⟩
      simp only [N, kv, hi.1.ne', hi.2.ne, ite_false, Equiv.trans_apply, Equiv.swap_apply_def, Fin.ext_iff, Fin.val_ofNat]
      split_ifs <;> simp only [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : i < n + 1), Nat.mod_eq_of_lt (by omega : i - 1 < n + 1)] at * <;> omega
    let bd : ((Fin (n + 1) → ℕ) × Equiv.Perm (Fin (n + 1))) × ℕ → Prop := fun x =>
      (x.2 = 0 ∧ ∃ k, (x.1.2 k : ℕ) = 0 ∧ p ≤ x.1.1 k + 1) ∨ (x.2 = n + 1 ∧ ∃ k, (x.1.2 k : ℕ) = n ∧ x.1.1 k = 0)
    have key : ∀ b σ i, (∀ k, b k < p) → i < n + 2 → ¬ bd ((b, σ), i) → (∀ k, (N ((b, σ), i)).1.1 k < p) ∧
        (N ((b, σ), i)).2 < n + 2 ∧ ¬ bd (N ((b, σ), i)) ∧ N ((b, σ), i) ≠ ((b, σ), i) := by
      intro b σ i hb hi hbd
      rcases (show i = 0 ∨ i = n + 1 ∨ (0 < i ∧ i < n + 1) by omega) with rfl | rfl | hi
      · refine ⟨fun k => ?_, by grind, ?_, fun h => by grind⟩
        · grind
        simp only [bd, N, ite_true, not_or, not_and, not_exists, Equiv.trans_apply, finRotate_symm_apply, Fin.coe_sub_one, Fin.ext_iff, Fin.val_zero]
        grind
      · grind
      refine ⟨fun k => by simp [N, hi.1.ne', hi.2.ne, hb], by simp [N, hi.1.ne', hi.2.ne]; omega, by simp [bd, N, hi.1.ne', hi.2.ne], fun h => ?_⟩
      have := congrArg (fun y => y.1.2 (σ.symm (Fin.ofNat _ i))) h
      simp only [N, hi.1.ne', hi.2.ne, ite_false, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_right, Fin.ext_iff, Fin.val_ofNat] at this
      rw [Nat.mod_eq_of_lt (by grind), Nat.mod_eq_of_lt (by grind)] at this
      omega
    have VI : ∀ (b' : Fin n → ℕ) e j, kv (Fin.cons (p - 1) b') (Equiv.Perm.decomposeFin.symm (0, e)) (j + 1) =
        Fin.cons p (kv b' e j) := by
      intro b' e j; funext k
      refine Fin.cases ?_ (fun k => ?_) k <;>
        simp [kv, Equiv.Perm.decomposeFin_symm_apply_succ] <;> omega
    let D := {x ∈ ((Fintype.piFinset fun _ : Fin (n + 1) => range p) ×ˢ (univ : Finset (Equiv.Perm (Fin (n + 1))))) ×ˢ range (n + 2) |
      ∀ c < n + 1, ∃ j ≤ n + 1, j ≠ x.2 ∧ L (kv x.1.1 x.1.2 j) = c}
    have key' : ∀ x ∈ {x ∈ D | ¬ bd x}, N x ∈ {x ∈ D | ¬ bd x} ∧ N (N x) = x ∧ N x ≠ x := by
      rintro ⟨⟨b, σ⟩, i⟩ hx
      simp [D, mem_filter, mem_product, Fintype.mem_piFinset, mem_range, mem_univ, and_true] at hx ⊢
      obtain ⟨⟨⟨hb, hi⟩, hd⟩, hbd⟩ := hx
      obtain ⟨h1, h2, h3, h4⟩ := key b σ i hb hi hbd
      have hb' := fun h k hk h0 => hbd (Or.inr ⟨h, k, hk, h0⟩)
      refine ⟨⟨⟨⟨h1, h2⟩, fun c hc => ?_⟩, h3⟩, hinv b σ i hi hb', h4⟩
      obtain ⟨j, hj, hji, rfl⟩ := hd c hc
      obtain ⟨j', hj', hj'', e⟩ := hv b σ i hi hb' j hj hji
      grind
    rw [natCast_card_filter, ← sum_congr rfl fun s _ => door_parity (n + 1) (fun j => L (kv s.1 s.2 j)) fun j => h0 _]
    simp only [natCast_card_filter]
    rw [← sum_product', ← sum_filter, ← sum_filter_add_sum_filter_not _ bd]
    rw [sum_involution (fun x _ => N x) (fun _ _ => rfl) (fun x hx _ => (key' x hx).2.2) (fun x hx => (key' x hx).1)
      (fun x hx => (key' x hx).2.1), add_zero, sum_const, nsmul_one]
    rw [← ih (fun y => L (Fin.cons p y)) (fun y => by have := h2 (Fin.cons p y) 0 rfl; simp at this; omega)
      (fun y k hk => by have := h1 (Fin.cons p y) k.succ hk; simp at this; omega)
      (fun y k hk => by have := h2 (Fin.cons p y) k.succ hk; simp at this; omega)]
    have M : ∀ b' e, ((Fin.cons (p - 1) b', Equiv.Perm.decomposeFin.symm (0, e)), 0) ∈ {x ∈ D | bd x} ↔
        (b', e) ∈ {s ∈ (Fintype.piFinset fun _ : Fin n => range p) ×ˢ (univ : Finset (Equiv.Perm (Fin n))) |
          ∀ c ≤ n, ∃ j ≤ n, L (Fin.cons p (kv s.1 s.2 j)) = c} := by
      intro b' e
      simp only [D, bd, mem_filter, mem_product, Fintype.mem_piFinset, mem_range, mem_univ, and_true, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
      exact ⟨fun ⟨⟨⟨⟨_, hb⟩, _⟩, hd⟩, _⟩ => ⟨hb, fun c hc => (hd c (by omega)).elim fun j ⟨hj, hj0, hl⟩ =>
        ⟨j - 1, by omega, by grind⟩⟩, fun ⟨hb, hd⟩ =>
        ⟨⟨⟨⟨by omega, hb⟩, by omega⟩, fun c hc => (hd c (by omega)).elim fun j ⟨hj, hl⟩ =>
        ⟨j + 1, by omega, by omega, by grind⟩⟩, .inl ⟨trivial, 0, by simp, by simp; omega⟩⟩⟩
    have S : ∀ x ∈ {x ∈ D | bd x}, ∃ b' e, x = ((Fin.cons (p - 1) b', Equiv.Perm.decomposeFin.symm (0, e)), 0) := by
      rintro ⟨⟨b, σ⟩, i⟩ hx
      simp only [D, bd, mem_filter, mem_product, Fintype.mem_piFinset, mem_range, mem_univ, and_true] at hx
      obtain ⟨⟨⟨hb, -⟩, hd⟩, ⟨rfl, k, hk, hpk⟩ | ⟨rfl, k, hk, hk0⟩⟩ := hx
      · obtain ⟨j, hj, hj0, hl⟩ := hd n (by omega)
        obtain rfl : k = 0 := Fin.ext (by
          rw [Fin.val_zero]; have := h2 _ k (show kv b σ j k = p by simp [kv]; have := hb k; split_ifs <;> omega); omega)
        obtain ⟨⟨q, e⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective σ
        simp at hk
        refine ⟨Fin.tail b, e, ?_⟩
        rw [show p - 1 = b 0 by grind, Fin.cons_self_tail]; simp [hk]
      obtain ⟨j, hj, hjn, hl⟩ := hd (n - k) (by omega)
      exact (h1 (kv b σ j) k (by simp only [kv]; split_ifs <;> omega) (by grind)).elim
    refine congrArg Nat.cast (card_nbij' (fun y => ((Fin.cons (p - 1) y.1, Equiv.Perm.decomposeFin.symm (0, y.2)), 0))
      (fun x => (Fin.tail x.1.1, (Equiv.Perm.decomposeFin x.1.2).2)) (fun y hy => (M y.1 y.2).2 hy) (fun x hx => ?_)
      (fun y _ => by simp) (fun x hx => ?_)).symm
    all_goals obtain ⟨b', e, rfl⟩ := S x hx; simpa using (M b' e).1 hx

theorem fixed_point_unit_cube {m : ℕ} (f : C(Set.Icc (0 : Fin m → ℝ) 1, Set.Icc (0 : Fin m → ℝ) 1)) :
    ∃ x, f x = x := by
  by_contra! hne
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (f.continuous.dist continuous_id).continuousOn
  have hδ := dist_pos.2 (hne x)
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous f.continuous) _ (half_pos hδ)
  obtain ⟨p, hp⟩ := exists_nat_gt (max (1 / η) (2 / dist (f x) x))
  have hp0 := lt_of_le_of_lt (by positivity) hp
  have h1p : 1 / (p : ℝ) < η := by
    rw [div_lt_iff₀ hp0]; have := (le_max_left _ _).trans_lt hp; rwa [div_lt_iff₀ hη, mul_comm] at this
  have h2p : 1 / (p : ℝ) < dist (f x) x / 2 := by
    rw [div_lt_iff₀ hp0]; have := (le_max_right _ _).trans_lt hp; rw [div_lt_iff₀ hδ] at this; linarith
  let y : (Fin m → ℕ) → Set.Icc (0 : Fin m → ℝ) 1 := fun a =>
    ⟨fun k => min (a k / p) 1, fun k => by positivity, fun k => min_le_right _ _⟩
  let C a (k : Fin m) : Prop := (f (y a)).1 k < (y a).1 k ∨ p ≤ a k
  let S a := {c | c = m ∨ ∃ k : Fin m, m - 1 - k = c ∧ C a k}
  have hL a : sInf (S a) ∈ S a := Nat.sInf_mem ⟨m, .inl rfl⟩
  have hL' a k (h : C a k) : sInf (S a) ≤ m - 1 - k := Nat.sInf_le (.inr ⟨k, rfl, h⟩)
  have hp1 : 0 < p := mod_cast hp0
  have := sperner p hp1 m (fun a => sInf (S a)) (fun a => Nat.sInf_le (.inl rfl)) (fun a k hk he => by
    rcases hL a with h | ⟨k', h, hc | hc⟩
    · omega
    · obtain rfl : k' = k := Fin.ext (by omega)
      have := (f (y a)).2.1 k'
      simp [y, hk] at hc this; linarith
    obtain rfl : k' = k := Fin.ext (by omega)
    simp [hk] at hc; omega) fun a k hk => by have := hL' a k (.inr hk.ge); omega
  obtain ⟨⟨b, σ⟩, hs⟩ := card_pos.1 (Nat.pos_of_ne_zero fun h => by rw [h] at this; exact zero_ne_one this)
  obtain ⟨-, hs⟩ := mem_filter.1 hs
  dsimp only at hs
  obtain ⟨j0, -, hj0⟩ := hs m le_rfl
  have hg j j' k : |(y (kv b σ j)).1 k - (y (kv b σ j')).1 k| ≤ 1 / p := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), ← sub_div, abs_div, abs_of_pos hp0]
    gcongr; simp [kv]; split_ifs <;> norm_num
  refine (hx (Set.mem_univ (y (kv b σ j0)))).not_gt ((dist_pi_lt_iff hδ).2 fun k => ?_)
  obtain ⟨jk, -, hjk⟩ := hs (m - 1 - k) (by omega)
  have h0 : ¬ C (kv b σ j0) k := fun h => by have := hL' _ k h; omega
  have hk : C (kv b σ jk) k := by
    rcases hL (kv b σ jk) with h | ⟨k', h, hc⟩
    · omega
    obtain rfl : k' = k := Fin.ext (by omega); exact hc
  have hd := hu (show dist (y (kv b σ jk)) (y (kv b σ j0)) < η by
    rw [Subtype.dist_eq, dist_pi_lt_iff hη]; exact fun k => (hg _ _ k).trans_lt h1p)
  have h3 := (dist_le_pi_dist _ _ k).trans_lt hd
  have h4 := hg jk j0 k
  have h5 : (f (y (kv b σ jk))).1 k ≤ (y (kv b σ jk)).1 k := by
    rcases hk with hk | hk
    · exact hk.le
    have := (f (y (kv b σ jk))).2.2 k
    simp [y, min_eq_right ((one_le_div hp0).2 (mod_cast hk : (p : ℝ) ≤ kv b σ jk k))] at this ⊢; exact this
  simp [Real.dist_eq, id] at h3 ⊢
  rw [abs_of_nonneg (by grind)]
  linarith [abs_lt.1 h3, abs_le.1 h4]
