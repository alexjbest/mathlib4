import Mathlib.Init.Dvd
import Mathlib.Init.Logic
import Mathlib.Tactic.Basic

notation "ℤ" => Int

namespace Int

instance : Dvd Int where
  dvd a b := ∃ c, b = a * c

end Int
