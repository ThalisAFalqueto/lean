import Game.Metadata
import Game.MyNat.Addition
import Game.Levels.Tutorial

namespace MyNat

-- Primeira questão
theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with d hd
  rw [add_zero]
  rfl
  rw [add_succ]
  rw [succ_eq_add_one]
  rw [hd]
  rw [succ_eq_add_one]
  rfl


/- Segunda questão

-/

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with d hd
  rw [<- add_succ]
  rw [add_zero]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  rw [zero_add]
  rfl
  rw [add_succ]
  rw [hd]
  rw [add_succ]
  rfl


/- Terceira questão

-/
theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  rw [add_zero]
  rw [zero_add]
  rfl
  rw [succ_add]
  rw [add_succ]
  rw [hd]
  rfl


/- Quarta questão

-/
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction b with d hd
  rw [add_zero]
  rw [zero_add]
  rfl
  rw [add_succ]
  rw [succ_add]
  rw [hd]
  rw [succ_add]
  rw [add_succ]
  rfl


/- Quinta questão

-/

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  induction c with d hd
  rw [add_zero]
  rw [add_zero]
  rfl
  rw [add_succ]
  nth_rewrite 4 [add_comm]
  nth_rewrite 2 [add_assoc]
  rw [succ_add]
  rw [<- add_assoc]
  nth_rewrite 4 [add_comm]
  rw [hd]
  rfl
