import Game.Levels.Addition
import Game.MyNat.Multiplication

namespace MyNat


-- Primeira Questão
theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]
  rfl

-- Segunda Questão
theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with d hd
  rw [mul_zero]
  rfl
  rw [mul_succ]
  rw [hd]
  rw [add_zero]
  rfl

-- Terça Questão
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b  := by
  induction b with d hd
  rw [mul_zero]
  rw [mul_zero]
  rw [add_zero]
  rfl
  rw [mul_succ]
  rw [mul_succ]
  rw [hd]
  rw [add_right_comm]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  rw [<- add_assoc]
  rw [<- add_assoc]
  rw [add_right_comm]
  rfl

-- Quarta Questão
theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with d hd
  rw [mul_zero]
  rw [zero_mul]
  rfl
  rw [succ_mul]
  rw [mul_succ]
  rw [hd]
  rfl

-- Quinta Questão
theorem one_mul (m : ℕ) : 1 * m = m := by
  rw []
