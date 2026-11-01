import Erdos18c.Arithmetic
import Erdos18c.FiniteLaw
import Mathlib.Data.Nat.Log
import Mathlib.Data.Multiset.MapFold

/-!
Adapted from Kohlmeyer--Kruer Erdos18b.lean (unchanged source SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088).
The definitions and elementary representation operations retain their source
names inside Erdos18c. The new logarithmic estimates are developed separately.
-/

open Finset Filter
namespace Erdos18c
def HasFactorialDivisorMultiset (F R u : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ d ∈ s, d ∣ F.factorial) ∧ s.sum = R ∧ s.card ≤ u

theorem factorial_multiset_zero (F u : ℕ) : HasFactorialDivisorMultiset F 0 u := by
  exact ⟨0, by simp, by simp, by simp⟩

theorem factorial_multiset_singleton {F R : ℕ} (hR : R ∣ F.factorial) :
    HasFactorialDivisorMultiset F R 1 := by
  exact ⟨{R}, by simpa using hR, by simp, by simp⟩

theorem factorial_multiset_mono {F G R u v : ℕ}
    (h : HasFactorialDivisorMultiset F R u) (hFG : F ≤ G) (huv : u ≤ v) :
    HasFactorialDivisorMultiset G R v := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  exact ⟨s, fun d hd => (hs d hd).trans (Nat.factorial_dvd_factorial hFG),
    hsum, hcard.trans huv⟩

theorem factorial_multiset_to_distinct {F R u : ℕ}
    (h : HasFactorialDivisorMultiset F R u) :
    ShortSum (F + 2 * u).factorial R u := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  have hrep := distinctify_factorial_divisors s F hs
  rw [hsum] at hrep
  exact shortSum_mono_count
    (shortSum_mono_host (Nat.factorial_dvd_factorial (by omega))
      (Nat.factorial_ne_zero (F + 2 * u)) hrep) hcard

theorem factorial_multiset_add {F R S u v : ℕ}
    (hR : HasFactorialDivisorMultiset F R u)
    (hS : HasFactorialDivisorMultiset F S v) :
    HasFactorialDivisorMultiset F (R + S) (u + v) := by
  obtain ⟨s, hs, hsum, hcard⟩ := hR
  obtain ⟨t, ht, htsum, htcard⟩ := hS
  refine ⟨s + t, ?_, ?_, ?_⟩
  · intro d hd
    rcases Multiset.mem_add.mp hd with hd | hd
    · exact hs d hd
    · exact ht d hd
  · simp only [Multiset.sum_add, hsum, htsum]
  · simpa only [Multiset.card_add] using Nat.add_le_add hcard htcard

theorem factorial_multiset_scale {F G q R u : ℕ}
    (hq : q ∣ F.factorial) (h : HasFactorialDivisorMultiset G R u) :
    HasFactorialDivisorMultiset (F + G) (q * R) u := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  refine ⟨s.map (fun d => q * d), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
    exact (mul_dvd_mul hq (hs d hd)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add F G)
  · have hmul := Multiset.sum_map_mul_left (s := s) (a := q) (f := id)
    simpa [hsum] using hmul
  · simpa only [Multiset.card_map] using hcard


def binaryLength (R : ℕ) : ℕ := Nat.log 2 R + 1

theorem binaryLength_pos (R : ℕ) : 0 < binaryLength R := by simp [binaryLength]

#print axioms factorial_multiset_to_distinct
end Erdos18c
