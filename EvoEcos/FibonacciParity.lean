import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace EvoEcos

/-!
# Fibonacci Parity Theorems

This file proves that the Fibonacci sequence modulo 2 has period 3.
This is a formal verification of the experimental discovery from
the parity pattern discovery experiment.

The main theorem: `fib_mod2_period_3` proves that
  Fib (n + 3) % 2 = Fib n % 2

for all natural numbers n.
-/

/-- The Fibonacci numbers -/
def Fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => Fib n + Fib (n+1)

notation "F(" n ")" => Fib n

/-- Addition lemma for Fibonacci numbers -/
theorem Fib_add_add (n : Nat) : Fib (n + 2) = Fib n + Fib (n + 1) := by
  induction n with
  | zero =>
    simp [Fib]
  | succ n ih =>
    simp [Fib, ih, add_assoc]

/-- Key lemma: F(n+3) = F(n) + 2*F(n+1) -/
theorem Fib_three_add (n : Nat) : Fib (n + 3) = Fib n + 2 * Fib (n + 1) := by
  have h1 : Fib (n + 3) = Fib (n + 1) + Fib (n + 2) := Fib_add_add (n + 1)
  have h2 : Fib (n + 2) = Fib n + Fib (n + 1) := Fib_add_add n
  rw [h1, h2]
  ring

/-- Main theorem: Fibonacci mod 2 has period 3 -/
theorem fib_mod2_period_3 (n : Nat) : Fib (n + 3) % 2 = Fib n % 2 := by
  have h := Fib_three_add n
  rw [h]
  -- (F(n) + 2*F(n+1)) % 2 = F(n) % 2 : pure linear arithmetic mod 2
  omega

/-- Corollary: Parity[3] is a perfect predictor for Fibonacci mod 2 -/
theorem fib_parity3_perfect (n : Nat) (hn : 3 ≤ n) : Fib n % 2 = Fib (n - 3) % 2 := by
  have h : Fib n = Fib ((n - 3) + 3) := by
    congr 1
    omega
  rw [h, fib_mod2_period_3]

/-- Period 3 also means period 6, 9, 12, ... -/
theorem fib_mod2_period_3k (n k : Nat) : Fib (n + 3 * k) % 2 = Fib n % 2 := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    show Fib ((n + 3 * k) + 3) % 2 = Fib n % 2
    rw [fib_mod2_period_3]
    exact ih

end EvoEcos
