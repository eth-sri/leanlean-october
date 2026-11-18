module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Tauto

@[expose] public section

macro "by_o" : term => `(by omega)
macro "by_d" : term => `(by decide)
macro "by_n" : term => `(by norm_num)
macro "by_s" : term => `(by simp)
macro "by_l" : term => `(by linarith)
macro "by_nl" : term => `(by nlinarith)
macro "by_r" : term => `(by ring)
macro "by_p" : term => `(by positivity)
macro "by_t" : term => `(by tauto)

end
