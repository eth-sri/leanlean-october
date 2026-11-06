module

public import RequestProject.ChamberZChain
public import RequestProject.ChamberZPi1
public import RequestProject.OrderComplexPi1Transfer
public import RequestProject.CombCoveringLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

def InZBaseAt (w : CayGroup A) : Zpos A X M att → Prop
  | .inl _ => False
  | .inr wx => wx.1.1 = w

theorem inZBaseAt_imp_inZChamber {w : CayGroup A} {z : Zpos A X M att}
    (h : InZBaseAt w z) : InZChamber w z := by
  cases z with
  | inl _ => exact h.elim
  | inr _ => exact h

@[simp] theorem inZBaseAt_zNew (w : {w : CayGroup A // M w}) (x : X) :
    InZBaseAt (att := att) w.1 (zNew w x) := rfl

def zBaseRetr (w : CayGroup A) : {z : Zpos A X M att // InZBaseAt w z} → X
  | ⟨.inl _, h⟩ => h.elim
  | ⟨.inr wx, _⟩ => wx.2

@[simp] theorem zBaseRetr_zNew (w : {w : CayGroup A // M w}) (x : X) :
    zBaseRetr (att := att) w.1 ⟨zNew w x, inZBaseAt_zNew w x⟩ = x := rfl

theorem zBaseRetr_monotone (w : CayGroup A) :
    Monotone (zBaseRetr (A := A) (X := X) (M := M) (att := att) w) := by
  rintro ⟨_ | _, hz⟩ ⟨_ | _, hz'⟩ h
  · exact hz.elim
  · exact hz.elim
  · exact hz'.elim
  · exact h.2

theorem injIn_zchamber_base {w : CayGroup A} (hw : M w) :
    InjIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) (InZBaseAt w) := by
  refine injIn_of_monotone_retraction (fun _ hz => inZBaseAt_imp_inZChamber hz)
    (fun z => (zChamberRetr hw z).1) (fun _ _ h => zChamberRetr_monotone hw h) ?_ ?_
  · intro z; obtain ⟨x, hx⟩ := zChamberRetr_mem hw z
    show InZBaseAt w (zChamberRetr hw z).1; rw [hx]; rfl
  · rintro ⟨_ | _, _⟩ hb; exact hb.elim; rfl

variable [Fintype V]

theorem connectedIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    ConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  connectedIn_of_isConnected
    (isConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_isConnected hw))

theorem simplyConnectedIn_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    SimplyConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  simplyConnectedIn_of_simplyConnected
    (simplyConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_simplyConnected hw))

theorem exists_zJSet {w : CayGroup A} (hw : w ≠ 1) :
    ∃ z : Zpos A X M att, ZJSet w z :=
  ⟨((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).1,
    ((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).2⟩

theorem injIn_zupto_insert {w0 : CayGroup A} (hw0 : M w0) (n : ℕ)
    (hprev : RACG.clen A w0 ≤ n → InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n)
      (InZBaseAt w0)) :
    ∀ S : Set (CayGroup A), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      (RACG.clen A w0 ≤ n ∨ w0 ∈ S) →
      InjIn (fun z : Zpos A X M att => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z) (InZBaseAt w0) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro _ hbase
      exact injIn_congr_left (by simp)
        (hprev (hbase.resolve_right (Set.notMem_empty w0)))
  | @insert x S hxS hSfin ih =>
      intro hlen hbase
      have hxlen : RACG.clen A x = n + 1 := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := fun h => by rw [h, clen_one] at hxlen; omega
      let Prev (z : Zpos A X M att) : Prop := ZUpto n z ∨ ∃ y ∈ S, InZChamber y z
      have hup {z z' : Zpos A X M att} (hzz' : z ≤ z') : Prev z → Prev z'
        | .inl h => .inl (zUpto_up hzz' h)
        | .inr ⟨y, hy, hyz⟩ => .inr ⟨y, hy, inZChamber_of_le hzz' hyz⟩
      have hinter (z : Zpos A X M att) : (Prev z ∧ InZChamber x z) ↔ ZJSet x z :=
        ⟨fun ⟨hprev', hzx⟩ => by
          rcases hprev' with ⟨y, hy, hyz⟩ | ⟨y, hyS, hyz⟩
          · exact (mem_shorter_zchamber_iff hzx).1 ⟨y, by omega, hyz⟩
          · exact (mem_earlier_zchamber_iff hzx).1 ⟨y, fun hxy => hxS (hxy ▸ hyS),
              by rw [hlen y (Set.mem_insert_of_mem _ hyS), hxlen], hyz⟩,
         fun hJ =>
          let ⟨y, _, hyz⟩ := (mem_shorter_zchamber_iff (zJSet_imp_inZChamber hJ)).2 hJ
          ⟨.inl ⟨y, by omega, hyz⟩, zJSet_imp_inZChamber hJ⟩⟩
      obtain ⟨j0, hj0⟩ := exists_zJSet (X := X) (M := M) (att := att) hx1
      have hmain : InjIn (fun z : Zpos A X M att => Prev z ∨ InZChamber x z) (InZBaseAt w0) := by
        by_cases hin : RACG.clen A w0 ≤ n ∨ w0 ∈ S
        · refine injIn_trans (fun z hz => hin.elim
              (fun h => .inl ⟨w0, h, inZBaseAt_imp_inZChamber hz⟩)
              (fun h => .inr ⟨w0, h, inZBaseAt_imp_inZChamber hz⟩))
            (injIn_union_of_unmixed (B := InZChamber x) (J := ZJSet x)
              (fun a b hab ha _ => ha.imp (fun h => ⟨h, hup hab h⟩) (fun h => ⟨h, inZChamber_of_le hab h⟩))
              (fun z => (hinter z).symm) (connectedIn_zJSet hx1) (simplyConnectedIn_zJSet hx1) hj0)
            (ih (fun y hy => hlen y (Set.mem_insert_of_mem _ hy)) hin)
        · have hw0x : w0 = x := by
            rcases hbase with h | h
            · exact absurd (.inl h) hin
            · exact (Set.mem_insert_iff.1 h).resolve_right fun h => hin (.inr h)
          subst hw0x
          refine injIn_trans (fun _ => inZBaseAt_imp_inZChamber)
            (injIn_union_of_unmixed (B := Prev) (J := ZJSet w0)
              (fun a b hab ha _ => (ha.imp (fun h => ⟨h, hup hab h⟩)
                (fun h => ⟨h, inZChamber_of_le hab h⟩)).symm)
              (fun z => by rw [← hinter z]; exact and_comm)
              (connectedIn_zJSet hx1) (simplyConnectedIn_zJSet hx1) hj0)
            (injIn_zchamber_base hw0)
      refine injIn_congr_left (fun z => ⟨?_, ?_⟩) hmain
      · rintro ((h | ⟨y, hy, hyz⟩) | h)
        · exact .inl h
        · exact .inr ⟨y, Set.mem_insert_of_mem _ hy, hyz⟩
        · exact .inr ⟨x, Set.mem_insert _ _, h⟩
      · rintro (h | ⟨y, hy, hyz⟩)
        · exact .inl (.inl h)
        · rcases Set.mem_insert_iff.1 hy with rfl | hy
          · exact .inr hyz
          · exact .inl (.inr ⟨y, hy, hyz⟩)

theorem injIn_zupto {w0 : CayGroup A} (hw0 : M w0) :
    ∀ n : ℕ, RACG.clen A w0 ≤ n →
      InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n) (InZBaseAt w0)
  | 0, h => by
      have hw1 : w0 = 1 := (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 h)
      subst hw1
      exact injIn_congr_left (fun z => (zUpto_zero_iff z).symm) (injIn_zchamber_base hw0)
  | n + 1, h => by
      have hstep := injIn_zupto_insert hw0 n (injIn_zupto hw0 n)
        {x : CayGroup A | RACG.clen A x = n + 1} (level_finite A (n + 1)) (fun _ hy => hy)
        (by rcases Nat.lt_or_ge (RACG.clen A w0) (n + 1) with _ | _
            · exact .inl (by omega)
            · exact .inr (by dsimp; omega))
      refine injIn_congr_left (fun z => ⟨?_, ?_⟩) hstep
      · rintro (⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩)
        · exact ⟨y, by omega, hyz⟩
        · exact ⟨y, le_of_eq hy, hyz⟩
      · rintro ⟨y, hy, hyz⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with _ | _
        · exact .inl ⟨y, by omega, hyz⟩
        · exact .inr ⟨y, by dsimp; omega, hyz⟩

theorem injIn_zpos {w0 : CayGroup A} (hw0 : M w0) :
    InjIn (fun _ : Zpos A X M att => True) (InZBaseAt w0) := by
  intro v l hv hp hl hnull
  obtain ⟨n, hn⟩ := exists_htpyIn_of_htpy
    (D := fun n => ZUpto (A := A) (X := X) (M := M) (att := att) n)
    (fun m n hmn z ⟨y, hy, hyz⟩ => ⟨y, hy.trans hmn, hyz⟩)
    (fun z => ⟨zlen z, zUpto_zlen z⟩) (htpyIn_true_iff.mp hnull)
  exact injIn_zupto hw0 (max n (RACG.clen A w0)) (le_max_right _ _) v l hv hp hl
    (HtpyIn.mono (fun _ ⟨y, hy, hyz⟩ => ⟨y, hy.trans (le_max_left _ _), hyz⟩) hn)

theorem pi1Map_zNew_injective_uncond (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
        (zNew_monotone w)) x) :=
  pi1Map_injective_of_injIn (Bp := InZBaseAt w.1) (injIn_zpos w.2)
    (zNew_monotone w) (inZBaseAt_zNew w)
    (zBaseRetr_monotone (A := A) (X := X) (M := M) (att := att) w.1)
    (zBaseRetr_zNew w) x

theorem pi1Map_zNew_covering_injective {W : Comb.Complex2}
    (q : Comb.Hom (orderCx (Zpos A X M att)) W) (hq : Comb.IsCovering q)
    (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      ((Comb.pi1Map q (zNew (A := A) (X := X) (M := M) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
          (zNew_monotone w)) x)) :=
  (Comb.pi1Map_injective_of_isCovering hq _).comp (pi1Map_zNew_injective_uncond w x)
