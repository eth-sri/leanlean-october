module

public import RequestProject.RACGMedian

@[expose] public section

noncomputable section
namespace FiniteChains.RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

def IsRDesc (x : CayGroup A) (s : V) : Prop := clen A (x * gen A s) < clen A x

theorem isRDesc_iff_isDesc (x : CayGroup A) (s : V) : IsRDesc A x s ↔ IsDesc A x⁻¹ s := by
  rw [IsRDesc, IsDesc, ← clen_inv A (x * gen A s), mul_inv_rev, gen_inv, clen_inv A x]

theorem rdesc_rel {x : CayGroup A} {s r : V} (hsr : s ≠ r) (hs : IsRDesc A x s)
    (hr : IsRDesc A x r) : A.rel s r :=
  desc_rel A hsr ((isRDesc_iff_isDesc A x s).1 hs) ((isRDesc_iff_isDesc A x r).1 hr)

theorem exists_rdesc {x : CayGroup A} (hx : x ≠ 1) : ∃ s : V, IsRDesc A x s :=
  let ⟨s, hs⟩ := exists_desc A (x := x⁻¹) (by simpa using hx)
  ⟨s, (isRDesc_iff_isDesc A x s).2 hs⟩

def Commuting (T : Set V) : Prop := ∀ ⦃s⦄, s ∈ T → ∀ ⦃r⦄, r ∈ T → s ≠ r → A.rel s r

def specialSub (T : Set V) : Subgroup (CayGroup A) := Subgroup.closure (gen A '' T)

theorem cword_mem_specialSub {T : Set V} : ∀ {l : List V}, (∀ a ∈ l, a ∈ T) →
    cword A l ∈ specialSub A T
  | [], _ => by simp
  | a :: t, hl => by
      rw [cword_cons]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, hl a (by simp), rfl⟩)
        (cword_mem_specialSub fun b hb => hl b (by simp [hb]))

theorem exists_cword_of_mem_specialSub {T : Set V} {u : CayGroup A} (hu : u ∈ specialSub A T) :
    ∃ l : List V, (∀ a ∈ l, a ∈ T) ∧ cword A l = u := by
  classical
  refine Subgroup.closure_induction (p := fun v _ => ∃ l : List V, (∀ a ∈ l, a ∈ T) ∧
    cword A l = v) ?_ ⟨[], by simp, by simp⟩ ?_ ?_ hu
  · rintro _ ⟨s, hs, rfl⟩; exact ⟨[s], by simpa using hs, by simp⟩
  · rintro _ _ _ _ ⟨l, hl, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨l ++ m, fun a ha => (List.mem_append.1 ha).elim (hl a) (hm a),
      Subtype.ext (wordPerm_append A l m)⟩
  · rintro _ _ ⟨l, hl, rfl⟩
    exact ⟨l.reverse, fun a ha => hl a (List.mem_reverse.1 ha),
      Subtype.ext (wordPerm_reverse A l)⟩

theorem gen_mul_cword_erase {T : Set V} (hT : Commuting A T) {s : V} (hs : s ∈ T) :
    ∀ l : List V, (∀ a ∈ l, a ∈ T) → l.Nodup → s ∈ l →
      gen A s * cword A l = cword A (l.erase s)
  | [], _, _, h => absurd h (by simp)
  | a :: t, hl, hnd, hmem => by
      by_cases hat : a = s
      · subst hat; simp [cword_cons, ← mul_assoc, gen_mul_gen]
      · have hst : s ∈ t := (List.mem_cons.1 hmem).resolve_left (Ne.symm hat)
        have hcomm : gen A s * gen A a = gen A a * gen A s := by
          simpa using cword_ceq A (CEq.of_swap (Swap.head (hT hs (hl a (by simp)) (Ne.symm hat)) []))
        rw [cword_cons, ← mul_assoc, hcomm, mul_assoc,
          gen_mul_cword_erase hT hs t (fun b hb => hl b (by simp [hb])) hnd.of_cons hst,
          ← cword_cons, List.erase_cons_tail (by simpa using hat)]

theorem exists_nodup_cword {T : Set V} (hT : Commuting A T) {u : CayGroup A}
    (hu : u ∈ specialSub A T) :
    ∃ l : List V, (∀ a ∈ l, a ∈ T) ∧ l.Nodup ∧ cword A l = u := by
  classical
  obtain ⟨l, hl, rfl⟩ := exists_cword_of_mem_specialSub A hu
  clear hu
  induction l with
  | nil => exact ⟨[], by simp, by simp, rfl⟩
  | cons a t ih =>
      obtain ⟨m, hm, hnd, hmt⟩ := ih fun b hb => hl b (by simp [hb])
      have ha : a ∈ T := hl a (by simp)
      by_cases hmem : a ∈ m
      · exact ⟨m.erase a, fun b hb => hm b (List.mem_of_mem_erase hb), hnd.erase a,
          by rw [← gen_mul_cword_erase A hT ha m hm hnd hmem, hmt, cword_cons]⟩
      · exact ⟨a :: m, fun b hb => (List.mem_cons.1 hb).elim (· ▸ ha) (hm b),
          by simpa using ⟨hmem, hnd⟩, by rw [cword_cons, hmt, cword_cons]⟩

theorem not_isDesc_cword_mul {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsDesc A x s) {s : V} (hs : s ∈ T) :
    ∀ l : List V, (∀ a ∈ l, a ∈ T) → s ∉ l → ¬ IsDesc A (cword A l * x) s
  | [], _, _ => by simpa using hx s hs
  | a :: t, hl, hsl => fun hcon => by
      have hrel := hT hs (hl a (by simp)) (fun h => hsl (by simp [h]))
      rw [cword_cons, mul_assoc] at hcon
      exact not_isDesc_cword_mul hT hx hs t (fun b hb => hl b (by simp [hb]))
        (fun h => hsl (by simp [h])) (by simpa [gen_mul_gen_mul] using desc_gen_mul_of_rel A hrel hcon)

theorem clen_cword_mul {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsDesc A x s) :
    ∀ l : List V, (∀ a ∈ l, a ∈ T) → l.Nodup →
      clen A (cword A l * x) = l.length + clen A x
  | [], _, _ => by simp
  | a :: t, hl, hnd => by
      have hnot := not_isDesc_cword_mul A hT hx (hl a (by simp)) t
        (fun b hb => hl b (by simp [hb])) (List.nodup_cons.1 hnd).1
      rw [cword_cons, mul_assoc, clen_gen_mul_of_not_desc A hnot,
        clen_cword_mul hT hx t (fun b hb => hl b (by simp [hb])) hnd.of_cons]
      simp [Nat.add_right_comm]

theorem clen_lt_of_mem_specialSub {T : Set V} (hT : Commuting A T) {x : CayGroup A}
    (hx : ∀ s ∈ T, ¬ IsRDesc A x s) {u : CayGroup A} (hu : u ∈ specialSub A T) (hu1 : u ≠ 1) :
    clen A x < clen A (x * u) := by
  obtain ⟨l, hl, hnd, hlu⟩ := exists_nodup_cword A hT (Subgroup.inv_mem _ hu)
  have hlen : 0 < l.length := List.length_pos_iff.2 (by rintro rfl; exact inv_ne_one.2 hu1 (hlu ▸ cword_nil A))
  have hsum := clen_cword_mul A hT (fun s hs hc => hx s hs ((isRDesc_iff_isDesc A x s).2 hc)) l hl hnd
  rw [hlu] at hsum
  rw [← clen_inv A (x * u), mul_inv_rev, ← clen_inv A x]
  omega

theorem earlier_of_rdesc {T : Set V} {x : CayGroup A} {s : V} (hs : s ∈ T) (h : IsRDesc A x s) :
    x⁻¹ * (x * gen A s) ∈ specialSub A T ∧ x * gen A s ≠ x ∧
      clen A (x * gen A s) < clen A x :=
  ⟨by rw [inv_mul_cancel_left]; exact Subgroup.subset_closure ⟨s, hs, rfl⟩,
    fun hc => by unfold IsRDesc at h; rw [hc] at h; omega, h⟩

theorem exists_rdesc_iff_exists_earlier {T : Set V} (hT : Commuting A T) (x : CayGroup A) :
    (∃ y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧ y ≠ x ∧ clen A y ≤ clen A x) ↔
      ∃ s ∈ T, IsRDesc A x s := by
  refine ⟨fun ⟨y, hy, hne, hle⟩ => ?_, fun ⟨s, hs, hsd⟩ =>
    let ⟨h1, h2, h3⟩ := earlier_of_rdesc A hs hsd; ⟨x * gen A s, h1, h2, le_of_lt h3⟩⟩
  by_contra hcon; push_neg at hcon
  have hlt := clen_lt_of_mem_specialSub A hT hcon hy (fun h => hne (inv_mul_eq_one.1 h).symm)
  rw [mul_inv_cancel_left] at hlt; omega

theorem existsUnique_shortest_coset {T : Set V} (hT : Commuting A T) (x : CayGroup A) :
    ∃! y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧ ∀ s ∈ T, ¬ IsRDesc A y s := by
  classical
  have hne : ∃ n : ℕ, ∃ y : CayGroup A, x⁻¹ * y ∈ specialSub A T ∧ clen A y = n :=
    ⟨clen A x, x, by rw [inv_mul_cancel]; exact Subgroup.one_mem _, rfl⟩
  obtain ⟨y, hyc, hylen⟩ := Nat.find_spec hne
  have hymin (z : CayGroup A) (hz : x⁻¹ * z ∈ specialSub A T) : clen A y ≤ clen A z :=
    hylen ▸ Nat.find_le ⟨z, hz, rfl⟩
  have hcoset (z : CayGroup A) : y⁻¹ * z ∈ specialSub A T ↔ x⁻¹ * z ∈ specialSub A T :=
    ⟨fun h => by rw [show x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) by group]; exact Subgroup.mul_mem _ hyc h,
     fun h => by rw [show y⁻¹ * z = (x⁻¹ * y)⁻¹ * (x⁻¹ * z) by group]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyc) h⟩
  have hyd : ∀ s ∈ T, ¬ IsRDesc A y s := fun s hs hsd => by
    obtain ⟨h1, -, h3⟩ := earlier_of_rdesc A hs hsd
    exact absurd (hymin _ ((hcoset _).1 h1)) (by omega)
  refine ⟨y, ⟨hyc, hyd⟩, fun z ⟨hzc, hzd⟩ => ?_⟩
  by_contra hne'
  have hyz : y⁻¹ * z ∈ specialSub A T := (hcoset z).2 hzc
  have hzy : z⁻¹ * y ∈ specialSub A T := by simpa using Subgroup.inv_mem _ hyz
  have hlt1 := clen_lt_of_mem_specialSub A hT hyd hyz (fun hc => hne' (inv_mul_eq_one.1 hc).symm)
  have hlt2 := clen_lt_of_mem_specialSub A hT hzd hzy (fun hc => hne' (inv_mul_eq_one.1 hc))
  rw [mul_inv_cancel_left] at hlt1 hlt2; omega
