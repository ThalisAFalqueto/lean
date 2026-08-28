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
