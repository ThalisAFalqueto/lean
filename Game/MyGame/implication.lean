import Game.Levels.Addition
import Game.MyNat.PeanoAxioms

namespace MyNat

-- Primeira Questão
example (x y z : ℕ) (h1: x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1  -- se a meta é P, então exact h fecha a meta se h prova P.

-- Segunda Questão
example (x y : ℕ) (h: 0 + x = 0 + y + 2) : x = y + 2 := by
  rw [zero_add] at h
  rw [zero_add] at h
  exact h

-- Terceira Questão
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1

-- Quarta Questão
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three] at h
  rw [<- succ_eq_add_one] at h
  apply succ_inj at h
  exact h

-- Quinta Questão
example (x : ℕ) (h: x + 1 = 4) : x = 3 := by
  apply succ_inj
  rw [<- four_eq_succ_three]
  rw [succ_eq_add_one]
  exact h

-- Sexta Questão
example (h : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h
