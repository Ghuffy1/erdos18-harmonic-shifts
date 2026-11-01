import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
Finite entropy and pushforward infrastructure adapted from Kohlmeyer--Kruer,
Erdos18b.lean, source SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088.
Only the selected elementary infrastructure is ported here; no result about
Erdos 18(b) is being used to assert the new 18(c) conclusion.
-/

open Finset
namespace Erdos18c

noncomputable def finiteEntropy {ι : Type*} (S : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ x ∈ S, Real.negMulLog (p x)

theorem sum_mul_log_le_log_bound {ι : Type*} (S : Finset ι) (p : ι → ℝ) {M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hbound : ∀ x ∈ S, p x ≤ M) :
    (∑ x ∈ S, p x * Real.log (p x)) ≤ (∑ x ∈ S, p x) * Real.log M := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hpx : p x = 0
  · simp [hpx]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_of_le_of_ne (hp x hx) (Ne.symm hpx)) (hbound x hx)) (hp x hx)

theorem finite_entropy_fiber_defect {ι : Type*} (S : Finset ι) (p : ι → ℝ) {q M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hq : 0 < q) (hM : 0 ≤ M) (hbound : ∀ x ∈ S, p x ≤ M) :
    Real.negMulLog (∑ x ∈ S, p x) + (∑ x ∈ S, p x) * Real.log q - finiteEntropy S p ≤
      q * M - ∑ x ∈ S, p x := by
  let s := ∑ x ∈ S, p x
  have hs : 0 ≤ s := Finset.sum_nonneg hp
  by_cases hMzero : M = 0
  · have hzero : ∀ x ∈ S, p x = 0 := fun x hx => le_antisymm (hMzero ▸ hbound x hx) (hp x hx)
    have hsumzero : ∑ x ∈ S, p x = 0 := Finset.sum_eq_zero hzero
    have hentropy : finiteEntropy S p = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hzero x hx, Real.negMulLog_def]
    simp [hsumzero, hentropy, hMzero, Real.negMulLog_def]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  have hlog := sum_mul_log_le_log_bound S p hp hbound
  have hentropy : finiteEntropy S p = -(∑ x ∈ S, p x * Real.log (p x)) := by
    simp [finiteEntropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  change Real.negMulLog s + s * Real.log q - finiteEntropy S p ≤ q * M - s
  rw [hentropy]
  change -s * Real.log s + s * Real.log q - -(∑ x ∈ S, p x * Real.log (p x)) ≤ q * M - s
  change (∑ x ∈ S, p x * Real.log (p x)) ≤ s * Real.log M at hlog
  by_cases hszero : s = 0
  · have hlogzero : (∑ x ∈ S, p x * Real.log (p x)) ≤ 0 := by
      simpa only [hszero, zero_mul] using hlog
    simpa only [hszero, neg_zero, zero_mul, zero_add, sub_neg_eq_add, sub_zero] using
      hlogzero.trans (mul_nonneg hq.le hM)
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hszero)
  have hratio := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq hMpos) hspos)
  rw [Real.log_div (mul_ne_zero hq.ne' hMpos.ne') hspos.ne', Real.log_mul hq.ne' hMpos.ne'] at hratio
  have hscaled := mul_le_mul_of_nonneg_left hratio hs
  have hcancel : s * (q * M / s) = q * M := by field_simp
  nlinarith

theorem finite_entropy_le_log_card {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1) :
    finiteEntropy S p ≤ Real.log (S.card : ℝ) := by
  have hSne : S.Nonempty := by
    by_contra hS
    have he := Finset.not_nonempty_iff_eq_empty.mp hS
    norm_num [he] at hsum
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hpoint : ∀ x ∈ S,
      (S.card : ℝ) * Real.negMulLog (p x) ≤
        1 - (S.card : ℝ) * p x + p x * (S.card : ℝ) * Real.log (S.card : ℝ) := by
    intro x hx
    have hh := Real.negMulLog_le_one_sub_self (mul_nonneg hcard.le (hp x hx))
    rw [Real.negMulLog_mul] at hh
    change p x * (-(S.card : ℝ) * Real.log (S.card : ℝ)) +
      (S.card : ℝ) * Real.negMulLog (p x) ≤ 1 - (S.card : ℝ) * p x at hh
    nlinarith
  have htotal := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, one_mul] at htotal
  apply (mul_le_mul_iff_of_pos_left hcard).mp
  simpa only [finiteEntropy, sub_self, zero_add] using htotal

noncomputable def finitePushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (b : κ) : ℝ := ∑ a : ι with π a = b, p a

theorem finite_pushforward_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) : ∑ b : κ, finitePushforward p π b = ∑ a : ι, p a := by
  exact Finset.sum_fiberwise Finset.univ π p

theorem finite_entropy_projection_defect {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (M : κ → ℝ) {q : ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : 0 < q) (hM : ∀ b, 0 ≤ M b)
    (hbound : ∀ a, p a ≤ M (π a)) :
    finiteEntropy Finset.univ (finitePushforward p π) + (∑ a : ι, p a) * Real.log q -
      finiteEntropy Finset.univ p ≤ q * (∑ b : κ, M b) - ∑ a : ι, p a := by
  have hfiber : ∀ b : κ,
      Real.negMulLog (finitePushforward p π b) + finitePushforward p π b * Real.log q -
        finiteEntropy (Finset.univ.filter (fun a => π a = b)) p ≤ q * M b - finitePushforward p π b := by
    intro b
    apply finite_entropy_fiber_defect _ p (fun a _ => hp a) hq (hM b)
    intro a ha
    have heq := (Finset.mem_filter.mp ha).2
    simpa only [heq] using hbound a
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hfiber b)
  have hentropy : (∑ b : κ, finiteEntropy (Finset.univ.filter (fun a => π a = b)) p) =
      finiteEntropy Finset.univ p := Finset.sum_fiberwise Finset.univ π (fun a => Real.negMulLog (p a))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hentropy, finite_pushforward_sum] at htotal
  exact htotal

theorem finite_pushforward_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (b : κ) :
    0 ≤ finitePushforward p π b := Finset.sum_nonneg (fun a _ => hp a)

theorem le_finite_pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (a : ι) :
    p a ≤ finitePushforward p π (π a) := by
  exact Finset.single_le_sum (fun b _ => hp b) (by simp)

theorem finite_entropy_mono_projection {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤ finiteEntropy Finset.univ p := by
  have hh := finite_entropy_projection_defect p π (finitePushforward p π) hp
    (show (0 : ℝ) < 1 by norm_num) (finite_pushforward_nonneg p π hp) (le_finite_pushforward p π hp)
  simp only [Real.log_one, mul_zero, add_zero, one_mul, finite_pushforward_sum, sub_self] at hh
  linarith

theorem finite_entropy_le_log_support {ι : Type*} [Fintype ι] (p : ι → ℝ) (S : Finset ι)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) (hzero : ∀ a, a ∉ S → p a = 0) :
    finiteEntropy Finset.univ p ≤ Real.log (S.card : ℝ) := by
  classical
  have hsum : ∑ a ∈ S, p a = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hzero a ha)]
    exact hmass
  have hentropy : finiteEntropy S p = finiteEntropy Finset.univ p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    simp [hzero a ha, Real.negMulLog_def]
  rw [← hentropy]
  exact finite_entropy_le_log_card S p (fun a _ => hp a) hsum

theorem finite_pushforward_comp {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [DecidableEq ν] (p : ι → ℝ) (π : ι → κ) (σ : κ → ν) :
    finitePushforward (finitePushforward p π) σ = finitePushforward p (σ ∘ π) := by
  funext b
  unfold finitePushforward
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] using
    Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset ι)
      (Finset.univ.filter (fun a => σ a = b)) π p

theorem finite_entropy_pushforward_le_log_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤
      Real.log ((Finset.univ.image π).card : ℝ) := by
  classical
  apply finite_entropy_le_log_support (finitePushforward p π) (Finset.univ.image π)
    (finite_pushforward_nonneg p π hp) (by rw [finite_pushforward_sum, hmass])
  intro b hb
  have he : Finset.univ.filter (fun a => π a = b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩)
  simp only [finitePushforward, he, Finset.sum_empty]

def dyadicIndex (k n : ℕ) : Fin (2 ^ k) := ⟨n % 2 ^ k, Nat.mod_lt n (by positivity)⟩

noncomputable def dyadicDistribution {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) :
    Fin (2 ^ k) → ℝ := finitePushforward p (fun a => dyadicIndex k (f a))

noncomputable def dyadicEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) : ℝ :=
  finiteEntropy Finset.univ (dyadicDistribution p f k)

theorem dyadic_distribution_project {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    {u v : ℕ} (huv : u ≤ v) :
    finitePushforward (dyadicDistribution p f v) (fun a => dyadicIndex u a.val) = dyadicDistribution p f u := by
  rw [dyadicDistribution, finite_pushforward_comp]
  unfold dyadicDistribution
  congr 1
  funext a
  apply Fin.ext
  exact Nat.mod_mod_of_dvd (f a) (pow_dvd_pow 2 huv)

theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hmass : ∑ i ∈ S, w i = 1) :
    (∑ i ∈ S, w i * t i) ^ 2 ≤ ∑ i ∈ S, w i * (t i) ^ 2 := by
  have hleft : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * t i)) = ∑ i ∈ S, w i * t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ S, (Real.sqrt (w i)) ^ 2) = 1 := by
    calc
      _ = ∑ i ∈ S, w i := Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
      _ = _ := hmass
  have hsecond : (∑ i ∈ S, (Real.sqrt (w i) * t i) ^ 2) = ∑ i ∈ S, w i * (t i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * t i)
  rwa [hleft, hfirst, hsecond, one_mul] at hh


#print axioms finite_entropy_le_log_support
#print axioms finite_pushforward_comp
end Erdos18c
