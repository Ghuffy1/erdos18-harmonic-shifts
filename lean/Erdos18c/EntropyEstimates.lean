import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite numerical estimates used by the proposed entropy argument.
These do not yet formalize the chain rule for random variables or the
conditioning/carry argument, and do not prove the full covering lemma.
-/

open Finset

namespace Erdos18c

theorem sum_squares_control {ι : Type*} (S : Finset ι) (h u : ι → ℝ)
    (hhu : ∀ i ∈ S, h i ^ 2 ≤ 2 * u i) :
    (∑ i ∈ S, h i) ^ 2 ≤ 2 * (S.card : ℝ) * ∑ i ∈ S, u i := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S h (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ i ∈ S, h i) ^ 2 ≤ (∑ i ∈ S, h i ^ 2) * (S.card : ℝ) := hcs
    _ ≤ (∑ i ∈ S, 2 * u i) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum hhu) (Nat.cast_nonneg _)
    _ = 2 * (S.card : ℝ) * ∑ i ∈ S, u i := by
      rw [← Finset.mul_sum]
      ring

theorem minority_mass_lower {ι : Type*} (S : Finset ι) (h u : ι → ℝ) (a : ℝ)
    (hcard : 0 < S.card) (ha : 0 ≤ a)
    (hhu : ∀ i ∈ S, h i ^ 2 ≤ 2 * u i)
    (hbudget : a * S.card ≤ ∑ i ∈ S, h i) :
    a ^ 2 * S.card / 2 ≤ ∑ i ∈ S, u i := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hcard
  have hsum0 : 0 ≤ ∑ i ∈ S, h i := le_trans (mul_nonneg ha hn.le) hbudget
  have hsquare : (a * S.card) ^ 2 ≤ (∑ i ∈ S, h i) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha hn.le) hbudget 2
  have hcs := sum_squares_control S h u hhu
  have hdivide : (S.card : ℝ) * (a ^ 2 * S.card) ≤
      (S.card : ℝ) * (2 * ∑ i ∈ S, u i) := by nlinarith
  have hcancel := le_of_mul_le_mul_left hdivide hn
  linarith

theorem weighted_reciprocal_lower {ι : Type*} (S : Finset ι)
    (u d : ι → ℝ) (D H c : ℝ)
    (hD : 0 < D) (hH : 0 < H)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hd : ∀ i ∈ S, 0 < d i ∧ d i ≤ D)
    (hmass : c * D ≤ ∑ i ∈ S, u i) :
    c / H ≤ (∑ i ∈ S, u i / d i) / H := by
  have hsum : (∑ i ∈ S, u i) / D ≤ ∑ i ∈ S, u i / d i := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    apply (div_le_div_iff₀ hD (hd i hi).1).mpr
    exact mul_le_mul_of_nonneg_left (hd i hi).2 (hu i hi)
  have hc : c ≤ (∑ i ∈ S, u i) / D := (le_div_iff₀ hD).mpr hmass
  exact div_le_div_of_nonneg_right (hc.trans hsum) hH.le

theorem harmonic_kernel_lower (j : ℕ) (u : ℕ → ℝ) (H c : ℝ)
    (hH : 0 < H)
    (hu : ∀ i ≤ j, 0 ≤ u i)
    (hmass : c * (j + 1 : ℕ) ≤ ∑ i ∈ Finset.range (j + 1), u i) :
    c / H ≤
      (∑ i ∈ Finset.range (j + 1), u i / (j + 1 - i : ℕ)) / H := by
  apply weighted_reciprocal_lower (Finset.range (j + 1)) u
    (fun i => (j + 1 - i : ℕ)) (j + 1 : ℕ) H c
  · positivity
  · exact hH
  · intro i hi
    exact hu i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  · intro i hi
    have hi' : i < j + 1 := Finset.mem_range.mp hi
    constructor
    · exact_mod_cast (show 0 < j + 1 - i by omega)
    · exact_mod_cast (show j + 1 - i ≤ j + 1 by omega)
  · exact hmass

#print axioms minority_mass_lower
#print axioms harmonic_kernel_lower

end Erdos18c
