module

public import Chazelle.Machine.Structured
public import Chazelle.Programs.RamSimp


/-! A static write check for structured RAM code. The same checker handles register-only
code, code that can store, and code with separate write sets for the two register banks. -/

namespace Chazelle.Machine

@[expose] public section

/-- An instruction predicate holds throughout a statement, in both branches of each test. -/
@[write_check] def Stmt.check (ok : Instr → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => ok i
  | .seq s t | .ifLtN _ _ s t | .ifLtR _ _ s t => check ok s && check ok t
  | .whileLtN _ _ s | .whileLtR _ _ s => check ok s

theorem Stmt.check_mono {ok more : Instr → Bool} (hm : ∀ i, ok i = true → more i = true)
    {s : Stmt} (hs : s.check ok = true) : s.check more = true := by
  induction s <;> simp_all [Stmt.check]

/-- A reflexive, transitive relation preserved by each checked instruction relates the
endpoints of an entire execution. -/
theorem Exec.rel_of_check {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (e : Exec P W s c c' k) {ok : Instr → Bool} (hs : s.check ok = true)
    (R : Config → Config → Prop) (hrefl : ∀ c, R c c)
    (ht : ∀ {a b d}, R a b → R b d → R a d)
    (hi : ∀ {i a b}, i.effect P a = some b → ok i = true → R a b) : R c c' := by
  induction e <;> simp only [Stmt.check, Bool.and_eq_true] at hs <;>
    first
    | exact hrefl _
    | exact hi (by assumption) hs
    | solve_by_elim [ht]
    | solve_by_elim [ht, hs.1, hs.2]

/-- Which natural/real registers and non-register fields an instruction may change. -/
structure Footprint where
  natReg : ℕ → Bool
  realReg : ℕ → Bool
  natMem : Bool
  realMem : Bool
  emits : Bool

@[write_check] def Footprint.allows (F : Footprint) : Instr → Bool
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => F.natReg r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _
  | .loadR r _ | .readX r _ | .readY r _ => F.realReg r
  | .storeN _ _ => F.natMem
  | .storeR _ _ => F.realMem
  | .emit _ _ _ => F.emits
  | _ => false

/-- Fields outside the write footprint agree. -/
structure Footprint.Keeps (F : Footprint) (c d : Config) : Prop where
  nr : ∀ r, F.natReg r = false → d.nreg r = c.nreg r
  rr : ∀ r, F.realReg r = false → d.rreg r = c.rreg r
  nm : F.natMem = false → d.nmem = c.nmem
  rm : F.realMem = false → d.rmem = c.rmem
  out : F.emits = false → d.output = c.output

theorem Footprint.keeps_refl (F : Footprint) (c : Config) : F.Keeps c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem Footprint.Keeps.trans {F : Footprint} {a b c : Config}
    (h : F.Keeps a b) (g : F.Keeps b c) : F.Keeps a c :=
  ⟨fun r hr => (g.nr r hr).trans (h.nr r hr), fun r hr => (g.rr r hr).trans (h.rr r hr),
    fun hr => (g.nm hr).trans (h.nm hr), fun hr => (g.rm hr).trans (h.rm hr),
    fun hr => (g.out hr).trans (h.out hr)⟩

theorem Footprint.effect {F : Footprint} {P : Polygon} {i : Instr} {c d : Config}
    (he : i.effect P c = some d) (h : F.allows i = true) : F.Keeps c d := by
  cases i <;> simp only [Instr.effect, Option.some.injEq, reduceCtorEq] at he <;>
    (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst d <;>
    simp only [Footprint.allows] at h <;> constructor <;> intros <;>
    first | rfl | (apply upd_other; intro e; subst e; simp_all) | simp_all

/-- An execution respects every static bound on its writes. -/
theorem Exec.keeps {P : Polygon} {W : ℕ} {s : Stmt} {c d : Config} {k : ℕ} {F : Footprint}
    (e : Exec P W s c d k) (hs : s.check F.allows = true) : F.Keeps c d :=
  e.rel_of_check hs _ (Footprint.keeps_refl F) (fun h g => h.trans g) (fun he h => Footprint.effect he h)

/-- Widening the register write sets or allowing natural stores preserves the check. -/
theorem Footprint.widen {N R N' R' : ℕ → Bool} {b b' m o : Bool}
    (hN : ∀ r, N r = true → N' r = true) (hR : ∀ r, R r = true → R' r = true)
    (hb : b = true → b' = true) {s : Stmt} (h : s.check (Footprint.allows ⟨N, R, b, m, o⟩) = true) :
    s.check (Footprint.allows ⟨N', R', b', m, o⟩) = true := by
  refine Stmt.check_mono (fun i hi => ?_) h
  cases i <;> simp_all [allows]

end

end Chazelle.Machine
