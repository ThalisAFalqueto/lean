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

-- Sétima Questão
example (x y : ℕ) : x + 1 = y + 1 → x = y := by
  rw [<- succ_eq_add_one]
  rw [<- succ_eq_add_one]
  apply succ_inj

-- Oitava Questão
example (x y : ℕ) (h1: x = y) (h2: x ≠ y) : False := by
  apply h2 at h1
  exact h1

-- Nona Questão
theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  intro h
  rw [one_eq_succ_zero] at h
  apply zero_ne_succ
  exact h

-- Décima Questão
theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  intro h
  symm at h
  apply zero_ne_one
  exact h

-- Décima Primeira Questão
example : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
  intro h
  rw [add_succ, add_succ, add_zero] at h
  repeat apply succ_inj at h
  rw [<- one_eq_succ_zero] at h
  apply zero_ne_one
  exact h
