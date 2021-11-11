/-
I am trying to prove the termination of my implementation of Tate's algoritm. I thus extend Dvd to Int
Author: Sacha Huriot
-/
import Mathlib.Init.Dvd
import Mathlib.Init.Logic
import Mathlib.Tactic.Basic

--notation "ℤ" => Int

namespace Int

instance : Dvd Int where
  dvd a b := ∃ c, b = a * c

@[simp] lemma int_zero_eq_zero : Int.ofNat 0 = 0 :=
rfl

end Int
