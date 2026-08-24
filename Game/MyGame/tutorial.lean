import Game.Metadata
import Game.MyNat.Multiplication
import Game.MyNat.Definition
import Game.MyNat.TutorialLemmas

-- Primeira questão
example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

-- Segunda questão
example (x y : ℕ ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
  rfl

/- Terceira questão
2 é o número após o successor do sucessor do 0
-/
namespace MyNat

example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one]        -- 2 = succ 1
  rw [one_eq_succ_zero]       -- 1 = succ 0. com isso, 2 == succ (succ 0), logo rfl
  rfl

/- Quarta questão
2 é o número após o successor do sucessor do 0
-/

example : 2 = succ (succ 0) := by
  rw [<- one_eq_succ_zero]    -- succ 0 = 1
  rw [<- two_eq_succ_one]     -- succ 1 = 2, then 2 = 2
  rfl

-- Quinta questão
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero]               -- b + 0 = b
  rw [add_zero]               -- c + 0 = c
  rfl

-- Sexta questão
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c]              -- c + 0 = c
  rw [add_zero b]              -- b + 0 = b
  rfl

/- Sétima questão
Para todos os números a, succ(a) = a + 1
-/
theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero]        -- succ n = n + succ 0
  rw [add_succ]                -- succ n = succ (n + 0)
  rw [add_zero]                -- succ n = succ (n)
  rfl

/- Oitava questão
Mostre que 2 + 2 = 4
-/
example : (2 : ℕ) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one] -- 2 + succ 1 = 4
  rw [add_succ]                 -- succ (2 + 1) = 4
  rw [one_eq_succ_zero]         -- succ (2 + succ 0) = 4
  rw [add_succ]                 -- succ (succ(2 + 0)) = 4
  rw [add_zero]                 -- succ (succ 2) = 4
  rw [<- three_eq_succ_two]     -- succ 3 = 4
  rw [<- four_eq_succ_three]    -- 4 = 4
  rfl
