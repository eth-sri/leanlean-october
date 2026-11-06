import RequestProject.NerveBoundaryReflection


/-! Both chain comparisons for a genuine monotone upper retraction. -/
namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P]

theorem cmap_eq_of_eqOn_incOn (f g : P → Q)
    (he : ∀ p, B p → f p = g p) c (hc : c ∈ IncOn B) : cmap f c = cmap g c := by
  refine AddSubgroup.closure_induction (p := fun z _ => cmap f z = cmap g z)
    ?_ ?_ ?_ ?_ hc
  · rintro z ⟨l, hl, rfl⟩
    rw [cmap_of, cmap_of]
    congr 1
    exact List.map_congr_left (fun p hp => he p (hl.2 p hp))
  · simp
  · simp_all
  simp

theorem reflectsBoundsIn_of_retraction {U B}
    (hBU : ∀ p, B p → U p) ρ
    (hmono : Monotone ρ) (hbase : ∀ p, B (ρ p).1)
    (hfix : ∀ p : {p : P // U p}, B p.1 → ρ p = p) n :
    ReflectsBoundsIn U B n := by
  classical
  let r := fun p => if h : U p then (ρ ⟨p, h⟩).1 else p
  have hr (p : {p : P // U p}) : r p.1 = (ρ p).1 := by grind
  have hrfix (p : P) (hp : B p) : r p = p := by
    simp_all
  intro c hc _ hbound
  obtain ⟨y, hy, hdy⟩ := hbound
  have hryn : cmap r y ∈ IncOn B := by
    obtain ⟨y', hy', rfl⟩ := exists_preimage_of_mem_incOn U hy
    rw [cmap_comp]
    have he : (r ∘ Subtype.val) =
        Subtype.val ∘ ρ := funext hr
    rw [he]
    exact cmap_mem_incOn_of_maps
      (f := Subtype.val ∘ ρ) (by aesop) hbase hy'
  refine ⟨cmap r y, hryn, ?_⟩
  rw [← cmap_bdry, hdy]
  simpa [cmap_id] using cmap_eq_of_eqOn_incOn r id hrfix c hc

/-- Pushing a cycle up to the retract changes it by a finite prism boundary. -/
theorem acyclicRelIn_of_upper_retraction (hne : ∃ p, U p)
    (ρ : {p : P // U p} → {p : P // U p}) (hmono : Monotone ρ)
    (hle : ∀ p, p ≤ ρ p) (hbase : ∀ p, B (ρ p).1) : AcyclicRelIn U B := by
  intro c hc hcyc
  obtain ⟨c', hc', rfl⟩ := exists_preimage_of_mem_incOn U hc
  have hcyc' : bdry c' = 0 := by
    apply cmap_val_injective U hne
    rw [cmap_bdry, hcyc, map_zero]
  have hp := bdry_prism_add_prism_bdry id ρ c'
  rw [hcyc', map_zero, add_zero, cmap_id] at hp
  have hpi :=
    prism_mem_inc monotone_id hmono hle hc'
  refine ⟨cmap Subtype.val (cmap ρ c'), ?_, -cmap Subtype.val (prism id ρ c'),
    AddSubgroup.neg_mem _ (cmap_val_mem_incOn U hpi), ?_, ?_⟩
  · rw [cmap_comp]
    exact cmap_mem_incOn_of_maps
      (f := Subtype.val ∘ ρ) (by aesop) hbase hc'
  · simp [← cmap_bdry, hcyc', map_zero]
  · rw [map_neg, ← cmap_bdry, hp, map_sub]
    abel
