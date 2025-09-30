import Mathlib.Tactic.Linarith

inductive BinOp where | add | mul

inductive Exp where
  | const : ℕ → Exp
  | var : ℕ → Exp
  | bin_op : Exp → BinOp → Exp → Exp

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Exp.eval (V : ℕ → ℕ) : Exp → ℕ := go
  where go : Exp → ℕ
    | const k => k
    | var x => V x
    | bin_op e₁ op e₂ => op.eval (go e₁) (go e₂)

-- NumFV n e => all vars in e are < n
inductive NumFV (n : ℕ) : Exp → Prop where
  | const {k} : NumFV n (Exp.const k)
  | var {x} : x < n → NumFV n (Exp.var x)
  | bin_op {e₁ op e₂} :
      NumFV n e₁ → NumFV n e₂ → NumFV n (Exp.bin_op e₁ op e₂)

-- def Exp.evalFinBroken {n} (V : Fin n → ℕ) : (e : Exp) → NumFV n e → ℕ := by
--   intro e
--   induction e with
--   | const k => intro; exact k
--   | var x =>
--       intro pf
--       apply V
--       apply Fin.mk x
--       cases pf
--       assumption
--   | bin_op e₁ op e₂ IH₁ IH₂ =>
--       intro pf
--       apply op.eval
--       · apply IH₁
--         cases pf
--         assumption
--       · apply IH₂
--         cases pf
--         assumption

def Exp.evalFin {n} (V : Fin n → ℕ) : (e : Exp) → NumFV n e → ℕ := go
  where go : (e : Exp) → NumFV n e → ℕ
          | const k, pf => k
          | var x, pf => V ⟨x, by cases pf; assumption⟩
          | bin_op e₁ op e₂, pf => op.eval (go e₁ (by cases pf; assumption)) (go e₂ (by cases pf; assumption))

def extend {n} (V : Fin n → ℕ) (k : ℕ) : ℕ :=
  if h : k < n then V ⟨ k, h ⟩ else 0

theorem evalFinCorrect {n e} (V : Fin n → ℕ) (pf : NumFV n e) :
    e.eval (extend V) = e.evalFin V pf := by
  sorry
