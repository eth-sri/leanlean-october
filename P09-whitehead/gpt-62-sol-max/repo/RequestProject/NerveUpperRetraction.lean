module

public import RequestProject.NerveBoundaryReflection
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-! Both chain comparisons for a genuine monotone upper retraction. -/
namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P]

theorem cmap_eq_of_eqOn_incOn {B : P → Prop} (f g : P → Q)
    (he : ∀ p, B p → f p = g p) (c : Ch P) (hc : c ∈ IncOn B) : cmap f c = cmap g c := by
  refine AddMonoidHom.eqOn_closure ?_ hc
  rintro _ ⟨l, hl, rfl⟩
  simp only [cmap_of, List.map_congr_left (fun p hp => he p (hl.2 p hp))]

theorem reflectsBoundsIn_of_retraction {U B : P → Prop}
    (hBU : ∀ p, B p → U p) (ρ : {p : P // U p} → {p : P // U p})
    (hmono : Monotone ρ) (hbase : ∀ p, B (ρ p).1)
    (hfix : ∀ p : {p : P // U p}, B p.1 → ρ p = p) (n : ℕ) :
    ReflectsBoundsIn U B n := by
  classical
  let r  := fun p => if h : U p then (ρ ⟨p, h⟩).1 else p
  have hr (p : {p : P // U p}) : r p.1 = (ρ p).1 := by simp [r, p.2]
  have hrfix (p : P) (hp : B p) : r p = p := by
    have h := hfix ⟨p, hBU p hp⟩ hp
    simpa [r, dif_pos (hBU p hp)] using congrArg Subtype.val h
  intro c hc _ hbound
  obtain ⟨y, hy, hdy⟩ := hbound
  have hryn : cmap r y ∈ IncOn B := by
    obtain ⟨y', hy', rfl⟩ := exists_preimage_of_mem_incOn U hy
    rw [cmap_comp]
    have he : (r ∘ (Subtype.val : {p : P // U p} → P)) =
        (Subtype.val : {p : P // U p} → P) ∘ ρ := funext hr
    rw [he]
    exact cmap_mem_incOn_of_maps
      (f := Subtype.val ∘ ρ) (fun _ _ h => hmono h) hbase hy'
  refine ⟨cmap r y, hryn, ?_⟩
  rw [← cmap_bdry, hdy]
  simpa only [cmap_id] using cmap_eq_of_eqOn_incOn r id hrfix c hc

end FiniteChains.Nerve
