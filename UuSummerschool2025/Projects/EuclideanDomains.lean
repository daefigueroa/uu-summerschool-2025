/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten, Florent Schaffhauser
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Euclidean rings

In this project sketch, we introduce principal ideal domains and Euclidean rings. We explore some
examples and show that every Euclidean domain is a principal ideal domain.
-/

/-
We can find lemma names by using the library search tactic `exact?`.
-/
example (a b : ℤ) : a % b + b * (a / b) = a := by
  exact?

/-- A commutative ring is a *principal ideal domain* (PID) if it is a domain and every ideal is
principal. -/
structure IsPID (R : Type) [CommRing R] : Prop where
  isDomain : IsDomain R
  ideal_principal : ∀ (I : Ideal R), ∃ (x : R), Ideal.span {x} = I

/-
Note: We used the `structure` command to define `IsPID`. If you encounter a structure, you can inspect its fields with the `#print` command:
-/

#print IsPID

/-- Any field is a principal ideal domain. -/
lemma isPID_of_field (k : Type) [Field k] : IsPID k where
  isDomain := inferInstance
  ideal_principal := by
    intro I
    by_cases h : I = 0
    · subst h
      use 0
      simp
    · simp at h
      have h2 : ∃ x ∈ I, x ≠ 0 := sorry
      obtain ⟨x, hx, hnezero⟩ := h2
      sorry

/--
A *Euclidean function* on a commutative ring is a height function `R → ℕ` and a division
with remainder, where the height of the remainder is smaller than the denominator.

Note: This is not merely a proposition, but contains the data of a height function. This
height function is not unique, so the datum of a ring `R` with a term `h : Euclidean R` is
not equivalent to the notion of a Euclidean domain (see `IsEuclideanDomain`).
-/
structure EuclideanFunction (R : Type) [CommRing R] where
  /-- Height function. -/
  height : R → WithBot ℕ
  zero_of_bot (x : R) : height x = ⊥ → x = 0
  /-- Division by zero -/
  division (a b : R) (hb : b ≠ 0) : ∃ q r, a = b * q + r ∧ (r = 0 ∨ height r < height b)

/--
An integral domain is called a Euclidean domain if it admits a Euclidean function.
-/
structure IsEuclideanDomain (R : Type) [CommRing R] : Prop where
  isDomain : IsDomain R
  exists_euclideanFunction : Nonempty (EuclideanFunction R)

/--
A Euclidean structure on a field `k`.

Note 1: Observe that we can change the `42` in the proof below to an arbitrary value.
In particular, the height function is not unique!
Note 2: This is a `def` and not a `theorem`, because it contains data. Try to see what happens if you
replace `def` by `theorem`!
-/
def euclideanOfField (k : Type) [Field k] : EuclideanFunction k where
  height _ := 42
  zero_of_bot x h := by simp_all
  division a b hb := by
    use a / b
    use 0
    /- found by `simp?` -/
    simp only [add_zero, lt_self_iff_false, or_false, and_true]
    field_simp

theorem isEuclidean_of_field (k : Type) [Field k] : IsEuclideanDomain k where
  isDomain := inferInstance
  exists_euclideanFunction := ⟨euclideanOfField k⟩

/-
The absolute value of an integer.
-/

#check Int.natAbs

/-
The canonical Euclidean structure on ℤ.
Hint: The remainder of integer division of `a : ℤ` by `b : ℤ` is `a % b`.
-/

def Int.euclidean : EuclideanFunction ℤ where
  height := sorry
  zero_of_bot := sorry
  division a b hb := sorry

theorem Int.isEuclidean : IsEuclideanDomain ℤ where
  isDomain := inferInstance
  exists_euclideanFunction := ⟨Int.euclidean⟩

/-
Any Euclidean ring is a principal ideal domain.
-/

theorem isPID_of_euclidean (R : Type) [CommRing R] (h : IsEuclideanDomain R) : IsPID R where
  isDomain := h.isDomain
  ideal_principal := sorry

open Polynomial

/-
The canonical Euclidean function on the polynomial ring in one variable over a field.
-/
def Polynomial.euclidean (k : Type) [Field k] : EuclideanFunction k[X] where
  height f := f.degree
  zero_of_bot f hf := sorry
  division := sorry

theorem Polynomial.isEuclidean_of_field (k : Type) [Field k] : IsEuclideanDomain k[X] :=
  sorry

/-
`Polynomial.isEuclidean_of_field` is wrong if we drop the field assumption. For example:
-/
example : ¬ IsEuclideanDomain ℤ[X] :=
  sorry
