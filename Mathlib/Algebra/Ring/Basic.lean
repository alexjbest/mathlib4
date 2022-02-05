import Mathlib.Init.Data.Int.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Spread
import Mathlib.Tactic.LibrarySearch

/-

# Semirings and rings
-/
import Mathlib.Util.WhatsNew

@[reducible, inline]
protected def Nat.cast [Add α] [Zero α] [One α] : Nat → α
  | 0 => 0
  | 1 => 1
  | n + 1 => Nat.cast n + 1

@[simp] lemma Nat.cast_zero [Add α] [Zero α] [One α] : Nat.cast 0 = (0 : α) := rfl
@[simp] lemma Nat.cast_one [Add α] [Zero α] [One α] : Nat.cast 1 = (1 : α) := rfl
lemma Nat.cast_succ_succ [Add α] [Zero α] [One α] : Nat.cast (n+2) = ((n + 1).cast + 1 : α) := rfl

@[simp]
lemma Nat.cast_Nat : ∀ {n : Nat}, n.cast = n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simp [Nat.cast, cast_Nat]; rfl

@[simp]
lemma Nat.cast_Int : ∀ {n : Nat}, n.cast = (n : Int)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simp [Nat.cast, cast_Int]; rfl

class HasNumerals (α : Type u) extends Add α, Zero α, One α

instance (priority := low) [HasNumerals α] : OfNat α n where
  ofNat := n.cast

/-
# Semirings and rings
-/

class Semiring (R : Type u) extends AddCommMonoid R, MonoidWithZero R, HasNumerals R where
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c

section Semiring
variable {R} [Semiring R]

instance : MonoidWithZero R where
  __ := ‹Semiring R›

instance : AddCommMonoid R where
  __ := ‹Semiring R›

theorem mul_add (a b c : R) : a * (b + c) = a * b + a * c := Semiring.mul_add a b c

theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := Semiring.add_mul a b c

@[simp] lemma one_pow (n : Nat) : (1 ^ n : R) = 1 := by
  induction n with
  | zero =>
    rw [pow_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    simp

-- @[simp] lemma ofNat_zero : (ofNat 0 : R) = 0 := rfl
-- @[simp] lemma ofNat_one : (ofNat 1 : R) = 1 := rfl
lemma Nat.cast_succ {R} [Semiring R] {n : ℕ} : Nat.cast (n + 1) = (Nat.cast n + 1 : R) := by
  cases n <;> simp [Nat.cast_succ_succ]

lemma Nat.cast_succ' {R} [Semiring R] {n : ℕ} : Nat.cast n.succ = (Nat.cast n + 1 : R) :=
  Nat.cast_succ

lemma Nat.cast_add {R} [Semiring R] {m n : ℕ} : (m + n).cast = (m.cast + n.cast : R) := by
  induction n generalizing m
  case zero => simp
  case succ n ih =>
    show Nat.cast ((m + n) + 1) = _ + Nat.cast (n + 1)
    simp [Nat.cast_succ, ih, add_assoc]

lemma Nat.cast_mul {R} [Semiring R] {m n : ℕ} : (m * n).cast = (m.cast * n.cast : R) := by
  induction n generalizing m <;> simp_all [mul_succ, cast_add, cast_succ', mul_add]

lemma Nat.pow_succ' {m n : Nat} : m ^ n.succ = m * m ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

lemma Nat.cast_pow {R} [Semiring R] {m n : ℕ} : (m ^ n).cast = (m.cast ^ n : R) := by
  induction n generalizing m <;>
    simp_all [cast_mul, cast_add, cast_succ', Nat.pow_succ', _root_.pow_succ', pow_zero]

theorem add_self_eq_mul_two (a : R) : a + a = 2 * a := by
  rw [←one_mul a, ←add_mul, one_mul]
  rfl

end Semiring

class CommSemiring (R : Type u) extends Semiring R where
  mul_comm (a b : R) : a * b = b * a
  -- TODO: doesn't work
  add_mul a b c := (by rw [mul_comm, mul_add, mul_comm c, mul_comm c])

instance (R : Type u) [CommSemiring R] : CommMonoid R where
  __ := ‹CommSemiring R›

class Ring (R : Type u) extends Semiring R, Neg R, Sub R where
  -- AddGroup R
  sub := λ a b => a + -b
  sub_eq_add_neg : ∀ a b : R, a - b = a + -b
  gsmul : ℤ → R → R := gsmul_rec
  gsmul_zero' : ∀ (a : R), gsmul 0 a = 0
  gsmul_succ' (n : ℕ) (a : R) : gsmul (Int.ofNat n.succ) a = a + gsmul (Int.ofNat n) a
  gsmul_neg' (n : ℕ) (a : R) : gsmul (Int.negSucc n) a = -(gsmul ↑(n.succ) a)
  add_left_neg (a : R) : -a + a = 0

section Ring
variable {R} [Ring R]

instance {R} [Ring R] : AddCommGroup R := { ‹Ring R› with }

theorem sub_eq_add_neg (a b : R) : a - b = a + -b := Ring.sub_eq_add_neg a b

theorem neg_mul_left (a b : R) : -(a * b) = -a * b := by
  rw [←add_zero (-a * b), ←add_left_neg (a * b)]
  rw [←add_assoc (-a * b), add_comm (-a * b), add_assoc]
  rw [←add_mul, add_left_neg a]
  simp

theorem neg_mul_right (a b : R) : -(a * b) = a * -b := by
  rw [←add_zero (a * -b), ←add_left_neg (a * b)]
  rw [←add_assoc (a * -b), add_comm (a * -b), add_assoc]
  rw [←mul_add, add_left_neg b]
  simp

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [Ring.sub_eq_add_neg, mul_add, ←neg_mul_right, ←Ring.sub_eq_add_neg]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [Ring.sub_eq_add_neg, add_mul, ←neg_mul_left, ←Ring.sub_eq_add_neg]

@[simp] theorem sub_zero (a : R) : a - 0 = a := by
  rw [Ring.sub_eq_add_neg, ←add_zero (-0), add_left_neg (0: R)]
  simp

theorem neg_add (a b : R) : - (a + b) = -a + -b := by
  have h₁ : - (a + b) = -(a + b) + (a + b) + -a + -b := by
    rw [add_assoc, add_comm (-a), add_assoc, add_assoc, ← add_assoc b]
    rw [add_right_neg b, zero_add, add_right_neg a, add_zero]
  rwa [add_left_neg (a + b), zero_add] at h₁

theorem sub_add_comm (n m k : R) : n + m - k = n - k + m := by
  rw [Ring.sub_eq_add_neg, add_assoc, add_comm m, ←add_assoc, ←Ring.sub_eq_add_neg]

@[simp] lemma square_neg_one : -1 ^ 2 = (1 : R) := by
  rw [pow_succ, pow_one, ←neg_mul_left, one_mul, neg_neg (1 : R)]

end Ring
theorem neg_mul_eq_neg_mul {R} [Ring R] (a b : R) : -(a * b) = (-a) * b :=
  Eq.symm <| eq_of_sub_eq_zero' <| by
    rw [Ring.sub_eq_add_neg, neg_neg (a * b) /- TODO: why is arg necessary? -/]
    rw [← add_mul, neg_add_self a /- TODO: why is arg necessary? -/, zero_mul]

class CommRing (R : Type u) extends Ring R where
  mul_comm (a b : R) : a * b = b * a

section CommRing
variable {R} [CommRing R]

instance (R : Type u) [CommRing R] : CommSemiring R where
  __ := inferInstanceAs (Semiring R)
  __ := ‹CommRing R›

theorem square_neg (a : R) : -a ^ 2 = a ^ 2 := by
  rw [(show -a = -(1 * a) by simp), neg_mul_left, mul_pow _ a, square_neg_one, one_mul]

theorem evenpow_neg {n m : ℕ} (a : R) (h : n = 2 * m) : -a ^ n = a ^ n := by
  rw [h, pow_mul, pow_mul, square_neg]

theorem oddpow_neg {n m : ℕ} (a : R) (h : n = 2 * m + 1) : -a ^ n = -(a ^ n) := by
  rw [h, pow_succ, evenpow_neg a (show 2 * m = 2 * m by rfl), ←neg_mul_right, ←pow_succ, Nat.add_one]

lemma square_add (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by
  rw [pow_two, mul_add, add_mul, add_mul, ←pow_two, ←pow_two, ←add_assoc, mul_comm b, ←one_mul (a * b), add_assoc (a ^ 2), ←add_mul, add_self_eq_mul_two 1, mul_one, one_mul]

lemma square_sub (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * (a * b) + b ^ 2 := by
  rw [Ring.sub_eq_add_neg, square_add, square_neg, ←neg_mul_right, ←neg_mul_right, ←Ring.sub_eq_add_neg]

end CommRing

class IntegralDomain (R : Type u) extends CommRing R where
  non_trivial : ¬1 = 0
  factors_nzero_mul_nzero {a b : R} : a ≠ 0 → b ≠ 0 → a * b ≠ 0

section IntegralDomain
variable {R} [IntegralDomain R]

theorem non_trivial : ¬1 = 0 := IntegralDomain.non_trivial R

theorem factors_nzero_mul_nzero {a b : R} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := IntegralDomain.factors_nzero_mul_nzero

theorem mul_eq_zero_iff_factor_eq_zero (a b : R) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  apply Iff.intro
  . intro mul_eq_zero
    sorry
  . intro factor_eq_zero
    cases factor_eq_zero with
    | inl a_zero => rw [a_zero, zero_mul]
    | inr b_zero => rw [b_zero, mul_zero]

-- set_option pp.all true
theorem pow_nonzero (a : R) (n : ℕ) : a ≠ 0 → a ^ n ≠ 0 := by
  intro h
  induction n with
  | zero =>
    simp
    intro hh
    apply h
    rw [← one_mul a, hh, zero_mul]
  | succ n ih =>
    rw [pow_succ]
    exact factors_nzero_mul_nzero ih h

end IntegralDomain

/- Instances -/

namespace Nat

instance : CommSemiring ℕ where
  mul_comm := Nat.mul_comm
  mul_add := Nat.left_distrib
  add_mul := Nat.right_distrib
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow (n x) := x ^ n
  npow_zero' := Nat.pow_zero
  npow_succ' n x := by simp [Nat.pow_succ, Nat.mul_comm]
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := (·*·)
  nsmul_zero' := Nat.zero_mul
  nsmul_succ' n x := by simp [Nat.add_comm, (Nat.succ_mul n x)]
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

end Nat

namespace Int

-- instance : Numeric ℤ := ⟨Int.ofNat⟩

-- instance : IntegralDomain ℤ where
instance : CommRing ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_comm := Int.mul_comm
  mul_add := Int.distrib_left
  add_mul := Int.distrib_right
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow (n x) := HPow.hPow x n
  npow_zero' n := rfl
  npow_succ' n x := by rw [Int.mul_comm]; rfl
  mul_assoc := Int.mul_assoc
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero' := Int.zero_mul
  nsmul_succ' n x := by
    show ofNat (Nat.succ n) * x = x + ofNat n * x
    rw [Int.ofNat_succ, Int.distrib_right, Int.add_comm, Int.one_mul]
  sub_eq_add_neg a b := Int.sub_eq_add_neg
  gsmul := HMul.hMul
  gsmul_zero' := Int.zero_mul
  gsmul_succ' n x := by rw [Int.ofNat_succ, Int.distrib_right, Int.add_comm, Int.one_mul]
  gsmul_neg' n x := by
    cases x with
    | ofNat m =>
      rw [Int.negSucc_ofNat_ofNat, Int.ofNat_mul_ofNat]
      exact rfl
    | negSucc m =>
      rw [Int.mul_negSucc_ofNat_negSucc_ofNat, Int.ofNat_mul_negSucc_ofNat]
      exact rfl
  -- non_trivial := by sorry
  -- factors_nzero_mul_nzero := by sorry

end Int
