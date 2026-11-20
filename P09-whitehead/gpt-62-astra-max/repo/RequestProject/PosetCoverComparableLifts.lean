module

public import RequestProject.PosetCoverUpTransform

@[expose] public section

/-! Lift a comparable map from a previously chosen lift, preserving its sheet. -/
namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [Preorder R]
  {f : P → Q} (hf : IsPosetCover f)

variable (a : R → P)

variable (b : R → Q)

variable (hab : ∀ x, b x ≤ f (a x)) (x : R)

noncomputable def lowerMapLift :=
  Classical.choose (hf.down (a x) (b x) (hab x))

omit [Preorder R] in
theorem lowerMapLift_spec :
    hf.lowerMapLift a b hab x ≤ a x ∧ f (hf.lowerMapLift a b hab x) = b x :=
  (Classical.choose_spec (hf.down _ _ (hab x))).1

theorem lowerMapLift_monotone
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, b x ≤ f _) :
    Monotone (hf.lowerMapLift a b hab) := by
  intro x y hxy
  have hx := hf.lowerMapLift_spec a b hab x
  have hy := hf.lowerMapLift_spec a b hab y
  obtain ⟨c, hxc, hcy, hfc⟩ := hf.exists_interval_lift (hx.1.trans (ha hxy)) _
    (hx.2 ▸ hb hxy) (hab y)
  exact hf.down_inj hcy hy.1 (hfc.trans hy.2.symm) ▸ hxc

variable (hab : ∀ x, f (a x) ≤ b x) (x : R)

noncomputable def upperMapLift :=
  Classical.choose (hf.up (a x) (b x) (hab x))

omit [Preorder R] in
theorem upperMapLift_spec :
    a x ≤ hf.upperMapLift a b hab x ∧ f (hf.upperMapLift a b hab x) = b x :=
  (Classical.choose_spec (hf.up _ _ (hab x))).1

theorem upperMapLift_monotone
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, f _ ≤ b x) :
    Monotone (hf.upperMapLift a b hab) := by
  intro x y hxy
  have hx := hf.upperMapLift_spec a b hab x
  have hy := hf.upperMapLift_spec a b hab y
  obtain ⟨c, hxc, hcy, hfc⟩ := hf.exists_interval_lift ((ha hxy).trans hy.1) _
    (hab x) (hy.2 ▸ hb hxy)
  exact hf.up_inj hxc hx.1 (hfc.trans hx.2.symm) ▸ hcy

/-- A constant endpoint lifts to a map constant on every comparability component. -/
theorem upperMapLift_constant_comparable (ha : Monotone a)
    (b : Q) (hab : ∀ x, f _ ≤ b) {x y : R} (hxy : x ≤ y) :
    hf.upperMapLift a _ hab x = hf.upperMapLift a _ hab y := by
  have hx := hf.upperMapLift_spec a _ hab x
  have hy := hf.upperMapLift_spec a _ hab y
  exact hf.up_inj hx.1 ((ha hxy).trans hy.1) (hx.2.trans hy.2.symm)

include hf in
/-- Relabelling the base by an order isomorphism preserves actual interval lifting. -/
theorem postcomp_orderIso {S : Type u} [PartialOrder S] (e : Q ≃o S) :
    IsPosetCover (fun x => e (f x)) := by
  refine ⟨e.monotone.comp hf.mono, e.surjective.comp hf.surj, ?_, ?_⟩
  · intro a q h
    obtain ⟨b, hb, huniq⟩ := hf.up a _ (by
      simpa only [e.symm_apply_apply] using e.symm.monotone h)
    refine ⟨b, ⟨hb.1, by simp_all⟩, ?_⟩
    grind [e.symm_apply_apply]
  · intro a q h
    obtain ⟨b, hb, huniq⟩ := hf.down a _ (by
      simpa only [e.symm_apply_apply] using e.symm.monotone h)
    refine ⟨b, ⟨hb.1, by simp_all⟩, ?_⟩
    grind [e.symm_apply_apply]

end FiniteChains.Comb.IsPosetCover
