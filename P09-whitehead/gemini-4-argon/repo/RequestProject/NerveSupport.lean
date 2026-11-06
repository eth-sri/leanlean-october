module

public import RequestProject.NervePrism

@[expose] public section

namespace FiniteChains.Nerve

universe u

open FreeAbelianGroup

section

variable {X : Type u}

theorem mem_closure_image_of_iff (S : Set X) (x : FreeAbelianGroup X) :
    x ∈ AddSubgroup.closure (FreeAbelianGroup.of '' S) ↔ ∀ y ∈ x.support, y ∈ S := by
  classical
  refine ⟨fun hx => AddSubgroup.closure_induction (p := fun z _ => ∀ y ∈ z.support, y ∈ S)
    (by rintro _ ⟨l, hl, rfl⟩ y hy; rw [support_of, Finset.mem_singleton] at hy; exact hy ▸ hl)
    (by simp)
    (fun u v _ _ hu hv y hy => (Finset.mem_union.1 (support_add u v hy)).elim (hu y) (hv y))
    (fun u _ hu y hy => hu y (by rwa [support_neg] at hy)) hx, fun h => ?_⟩
  rw [← (equivFinsupp X).symm_apply_apply x]
  change ∀ y ∈ (equivFinsupp X x).support, y ∈ S at h
  generalize equivFinsupp X x = f at h ⊢
  induction f using Finsupp.induction with
  | zero => simp
  | @single_add a b f ha hb ih =>
      have hsup := Finsupp.support_single_add ha hb
      have hsingle : (equivFinsupp X).symm (Finsupp.single a b) = b • of a :=
        (equivFinsupp X).injective (by simp [equivFinsupp])
      rw [map_add, hsingle]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
          (Set.mem_image_of_mem _ (h a (hsup ▸ Finset.mem_cons_self _ _)))) b)
        (ih fun y hy => h y (hsup ▸ Finset.mem_cons_of_mem hy))

end

variable {P Q : Type u} [Preorder P]

def IncLists (A : P → Prop) : Set (List P) :=
  {l : List P | List.IsChain (· ≤ ·) l ∧ ∀ a ∈ l, A a}

def IncOn (A : P → Prop) : AddSubgroup (Ch P) :=
  AddSubgroup.closure (FreeAbelianGroup.of '' IncLists A)

theorem mem_incOn_iff {A : P → Prop} (x : Ch P) :
    x ∈ IncOn A ↔ ∀ l ∈ x.support, List.IsChain (· ≤ ·) l ∧ ∀ a ∈ l, A a :=
  mem_closure_image_of_iff _ x

theorem of_mem_incOn {A : P → Prop} {l : List P} (hl : List.IsChain (· ≤ ·) l)
    (hA : ∀ a ∈ l, A a) : FreeAbelianGroup.of l ∈ IncOn A :=
  AddSubgroup.subset_closure ⟨l, ⟨hl, hA⟩, rfl⟩

theorem mem_inc_iff (x : Ch P) :
    x ∈ Inc P ↔ ∀ l ∈ x.support, List.IsChain (· ≤ ·) l := by
  rw [Inc, show {x : Ch P | ∃ l : List P, List.IsChain (· ≤ ·) l ∧ x = of l} =
    of '' {l : List P | List.IsChain (· ≤ ·) l} by ext; simp [eq_comm]]
  exact mem_closure_image_of_iff _ x

theorem incOn_le_inc (A : P → Prop) : IncOn A ≤ Inc P :=
  fun x hx => (mem_inc_iff x).2 fun l hl => ((mem_incOn_iff x).1 hx l hl).1

theorem incOn_mono {A B : P → Prop} (h : ∀ p, A p → B p) : IncOn A ≤ IncOn B :=
  fun x hx => (mem_incOn_iff x).2 fun l hl =>
    let ⟨hc, hA⟩ := (mem_incOn_iff x).1 hx l hl
    ⟨hc, fun a ha => h a (hA a ha)⟩

theorem incOn_congr {A B : P → Prop} (h : ∀ p, A p ↔ B p) : IncOn A = IncOn B :=
  le_antisymm (incOn_mono fun p => (h p).1) (incOn_mono fun p => (h p).2)

theorem incOn_inf (A B : P → Prop) :
    IncOn A ⊓ IncOn B = IncOn (fun p => A p ∧ B p) := by
  ext x
  simp only [AddSubgroup.mem_inf, mem_incOn_iff]
  exact ⟨fun ⟨hA, hB⟩ l hl => ⟨(hA l hl).1, fun a ha => ⟨(hA l hl).2 a ha, (hB l hl).2 a ha⟩⟩,
    fun h => ⟨fun l hl => ⟨(h l hl).1, fun a ha => ((h l hl).2 a ha).1⟩,
      fun l hl => ⟨(h l hl).1, fun a ha => ((h l hl).2 a ha).2⟩⟩⟩

theorem consList_bdryOn_mem_incOn (A : P → Prop) :
    ∀ (l pre : List P), List.IsChain (· ≤ ·) (pre ++ l) → (∀ a ∈ pre ++ l, A a) →
      consList pre (bdryOn l) ∈ IncOn A
  | [], _, _, _ => by simp
  | a :: t, pre, hchain, hall => by
      rw [bdryOn_cons, map_sub, consList_of, consList_consMap]
      refine AddSubgroup.sub_mem _
        (of_mem_incOn (isChain_append_of_isChain_append_cons hchain) fun b hb => ?_)
        (consList_bdryOn_mem_incOn A t (pre ++ [a]) (by simpa using hchain)
          fun b hb => hall b (by simpa using hb))
      rcases List.mem_append.1 hb with h | h
      · exact hall b (List.mem_append_left _ h)
      · exact hall b (List.mem_append_right _ (List.mem_cons_of_mem _ h))

theorem bdry_mem_incOn {A : P → Prop} {x : Ch P} (hx : x ∈ IncOn A) : bdry x ∈ IncOn A := by
  refine AddSubgroup.closure_induction (p := fun y _ => bdry y ∈ IncOn A) ?_ (by simp)
    (fun _ _ _ _ hy hz => by simpa using AddSubgroup.add_mem _ hy hz)
    (fun _ _ hy => by simpa using AddSubgroup.neg_mem _ hy) hx
  rintro _ ⟨l, ⟨hl, hA⟩, rfl⟩
  simpa using consList_bdryOn_mem_incOn A l [] (by simpa using hl) (by simpa using hA)

theorem forall_mem_or_of_unmixed {A B U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {l : List P} (hl : List.IsChain (· ≤ ·) l) (hlU : ∀ a ∈ l, U a) :
    (∀ a ∈ l, A a) ∨ (∀ a ∈ l, B a) := by
  classical
  by_cases hA : ∀ a ∈ l, A a
  · exact .inl hA
  · push Not at hA
    obtain ⟨c₀, hc₀l, hc₀⟩ := hA
    have hpw : l.Pairwise (fun x y : P => x ≤ y ∨ y ≤ x) :=
      (List.IsChain.pairwise hl).imp Or.inl
    let : Std.Symm (fun x y : P => x ≤ y ∨ y ≤ x) := ⟨fun _ _ h => h.symm⟩
    refine .inr fun c hc => ?_
    have hpair : c₀ ≤ c ∨ c ≤ c₀ :=
      if h : c₀ = c then .inl h.le else hpw.forall hc₀l hc h
    rcases hpair with h | h
    · exact (hmix c₀ c h (hlU c₀ hc₀l) (hlU c hc)).resolve_left (fun h1 => hc₀ h1.1) |>.2
    · exact (hmix c c₀ h (hlU c hc) (hlU c₀ hc₀l)).resolve_left (fun h1 => hc₀ h1.2) |>.1

theorem exists_split_of_unmixed {A B U : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {z : Ch P} (hz : z ∈ IncOn U) :
    ∃ a ∈ IncOn A, ∃ b ∈ IncOn B, z = a + b := by
  refine AddSubgroup.closure_induction
    (p := fun y _ => ∃ a ∈ IncOn A, ∃ b ∈ IncOn B, y = a + b) ?_
    ⟨0, AddSubgroup.zero_mem _, 0, AddSubgroup.zero_mem _, by simp⟩
    (by rintro _ _ _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a + a', AddSubgroup.add_mem _ ha ha', b + b', AddSubgroup.add_mem _ hb hb', by abel⟩)
    (by rintro _ _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨-a, AddSubgroup.neg_mem _ ha, -b, AddSubgroup.neg_mem _ hb, by abel⟩) hz
  rintro _ ⟨l, ⟨hl, hlU⟩, rfl⟩
  rcases forall_mem_or_of_unmixed hmix hl hlU with h | h
  · exact ⟨of l, of_mem_incOn hl h, 0, AddSubgroup.zero_mem _, by simp⟩
  · exact ⟨0, AddSubgroup.zero_mem _, of l, of_mem_incOn hl h, by simp⟩

def AcyclicIn (A : P → Prop) : Prop :=
  ∀ x ∈ IncOn A, bdry x = 0 → ∃ y ∈ IncOn A, bdry y = x

theorem acyclicIn_congr {A B : P → Prop} (h : ∀ p, A p ↔ B p) (hA : AcyclicIn A) :
    AcyclicIn B := by
  unfold AcyclicIn at hA ⊢; rwa [← incOn_congr h]

theorem acyclicIn_union_of_unmixed {A B U : P → Prop}
    (hU : ∀ p, U p ↔ (A p ∨ B p))
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hA : AcyclicIn A) (hB : AcyclicIn B) (hJ : AcyclicIn (fun p => A p ∧ B p)) :
    AcyclicIn U := by
  intro z hz hcyc
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_split_of_unmixed hmix hz
  have hsum : bdry a + bdry b = 0 := by rwa [← map_add]
  have htJ : bdry a ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    refine ⟨bdry_mem_incOn ha, ?_⟩
    rw [show bdry a = -bdry b by linear_combination (norm := abel) hsum]
    exact AddSubgroup.neg_mem _ (bdry_mem_incOn hb)
  obtain ⟨u, hu, hdu⟩ := hJ (bdry a) htJ (by simp [bdry_bdry])
  obtain ⟨p, hp, hdp⟩ := hA (a - u)
    (AddSubgroup.sub_mem _ ha (incOn_mono (fun _ hp => hp.1) hu))
    (by rw [map_sub, hdu, sub_self])
  obtain ⟨q, hq, hdq⟩ := hB (b + u)
    (AddSubgroup.add_mem _ hb (incOn_mono (fun _ hp => hp.2) hu))
    (by rw [map_add, hdu]; linear_combination (norm := abel) hsum)
  exact ⟨p + q, AddSubgroup.add_mem _
    (incOn_mono (fun r hr => (hU r).2 (.inl hr)) hp)
    (incOn_mono (fun r hr => (hU r).2 (.inr hr)) hq),
    by rw [map_add, hdp, hdq]; abel⟩

variable (A : P → Prop)

theorem cmap_val_mem_incOn {x : Ch {p : P // A p}} (hx : x ∈ Inc {p : P // A p}) :
    cmap Subtype.val x ∈ IncOn A := by
  refine AddSubgroup.closure_induction (p := fun y _ => cmap Subtype.val y ∈ IncOn A)
    ?_ (by simp)
    (fun _ _ _ _ hy hz => by simpa using AddSubgroup.add_mem _ hy hz)
    (fun _ _ hy => by simpa using AddSubgroup.neg_mem _ hy) hx
  rintro _ ⟨l, hl, rfl⟩
  rw [cmap_of]
  refine of_mem_incOn (List.isChain_map_of_isChain Subtype.val (fun _ _ h => h) hl) ?_
  intro a ha; obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact b.2

theorem exists_preimage_of_mem_incOn {x : Ch P} (hx : x ∈ IncOn A) :
    ∃ x' ∈ Inc {p : P // A p}, cmap Subtype.val x' = x := by
  refine AddSubgroup.closure_induction
    (p := fun y _ => ∃ y' ∈ Inc {p : P // A p}, cmap Subtype.val y' = y) ?_
    ⟨0, AddSubgroup.zero_mem _, by simp⟩
    (by rintro _ _ _ _ ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩
        exact ⟨y' + z', AddSubgroup.add_mem _ hy' hz', by simp⟩)
    (by rintro _ _ ⟨y', hy', rfl⟩
        exact ⟨-y', AddSubgroup.neg_mem _ hy', by simp⟩) hx
  rintro _ ⟨l, ⟨hl, hA⟩, rfl⟩
  have hchain : List.IsChain (· ≤ ·) ((l.attachWith A hA).map (Subtype.val : {p // A p} → P)) := by
    have hmap : (l.attachWith A hA).map Subtype.val = l := by simp
    rw [hmap]; exact hl
  exact ⟨of (l.attachWith A hA),
    of_mem_inc (List.isChain_of_isChain_map (f := Subtype.val) (fun _ _ h => h) hchain),
    by simp⟩

omit [Preorder P] in
theorem cmap_val_injective (hne : ∃ p : P, A p) :
    Function.Injective (cmap (Subtype.val : {p : P // A p} → P)) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  let r : P → {p : P // A p} := fun p => if h : A p then ⟨p, h⟩ else ⟨p₀, hp₀⟩
  have hcomp : r ∘ (Subtype.val : {p : P // A p} → P) = id := funext fun q => dif_pos q.2
  have h (z : Ch {p : P // A p}) : cmap r (cmap Subtype.val z) = z :=
    ext_apply (F := (cmap r).comp (cmap Subtype.val)) (G := .id _)
      (fun l => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, cmap_of,
          AddMonoidHom.id_apply, List.map_map, hcomp, List.map_id]) z
  intro x y hxy
  simpa [h] using congrArg (cmap r) hxy

theorem acyclicIn_of_subtype (hne : ∃ p : P, A p)
    (hsub : ∀ x ∈ Inc {p : P // A p}, bdry x = 0 →
      ∃ y ∈ Inc {p : P // A p}, bdry y = x) :
    AcyclicIn A := by
  intro x hx hcyc
  obtain ⟨x', hx', rfl⟩ := exists_preimage_of_mem_incOn A hx
  obtain ⟨y', hy', hdy'⟩ := hsub x' hx'
    (cmap_val_injective A hne (by rw [cmap_bdry, hcyc, map_zero]))
  exact ⟨cmap Subtype.val y', cmap_val_mem_incOn A hy', by rw [← cmap_bdry, hdy']⟩
