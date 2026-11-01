import Erdos18c.BinaryEntropy
import Erdos18c.EntropyEstimates
import Mathlib.Logic.Equiv.Fin.Basic

/-! Entropy increments for finite lower-bit projections. -/

open Finset
namespace Erdos18c
noncomputable section

def dyadicSplitEquiv (j : ℕ) : Fin (2^j) ⊕ Fin (2^j) ≃ Fin (2^(j+1)) :=
  finSumFinEquiv.trans (finCongr (by omega : 2^j+2^j = 2^(j+1)))

def dyadicLower (j : ℕ) (i : Fin (2^j)) : Fin (2^(j+1)) := dyadicSplitEquiv j (.inl i)
def dyadicUpper (j : ℕ) (i : Fin (2^j)) : Fin (2^(j+1)) := dyadicSplitEquiv j (.inr i)

@[simp] theorem dyadicLower_val (j : ℕ) (i : Fin (2^j)) : (dyadicLower j i).val = i.val := rfl
@[simp] theorem dyadicUpper_val (j : ℕ) (i : Fin (2^j)) : (dyadicUpper j i).val = 2^j+i.val := rfl

theorem dyadic_split_sum (j : ℕ) (F : Fin (2^(j+1)) → ℝ) :
    ∑ z, F z = ∑ i, (F (dyadicLower j i) + F (dyadicUpper j i)) := by
  have h := Fintype.sum_equiv (dyadicSplitEquiv j)
    (fun z => F (dyadicSplitEquiv j z)) F (fun _ => rfl)
  simpa only [Fintype.sum_sum_type, dyadicLower, dyadicUpper, sum_add_distrib] using h.symm

@[simp] theorem dyadicLower_mod (j : ℕ) (i : Fin (2^j)) :
    dyadicIndex j (dyadicLower j i).val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem dyadicUpper_mod (j : ℕ) (i : Fin (2^j)) :
    dyadicIndex j (dyadicUpper j i).val = i := by
  apply Fin.ext
  simp [dyadicIndex, Nat.mod_eq_of_lt i.isLt]

theorem dyadic_parent_mass (j : ℕ) (p : Fin (2^(j+1)) → ℝ) (i : Fin (2^j)) :
    finitePushforward p (fun z => dyadicIndex j z.val) i =
      p (dyadicLower j i) + p (dyadicUpper j i) := by
  unfold finitePushforward
  rw [sum_filter, dyadic_split_sum]
  simp only [dyadicLower_mod, dyadicUpper_mod]
  rw [sum_add_distrib]
  simp

theorem dyadic_entropy_increment (j : ℕ) (p : Fin (2^(j+1)) → ℝ) :
    finiteEntropy univ p - finiteEntropy univ
      (finitePushforward p (fun z => dyadicIndex j z.val)) =
      ∑ i, pairEntropy (p (dyadicLower j i)) (p (dyadicUpper j i)) := by
  unfold finiteEntropy
  rw [dyadic_split_sum]
  simp_rw [dyadic_parent_mass]
  simp only [pairEntropy, sum_sub_distrib, sum_add_distrib]

theorem dyadic_entropy_zero {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a, p a = 1) : dyadicEntropy p f 0 = 0 := by
  have hi : ∀ a : ι, dyadicIndex 0 (f a) = (0 : Fin (2^0)) := by
    intro a
    apply Fin.ext
    simp [dyadicIndex]
  have hv : dyadicDistribution p f 0 0 = 1 := by
    simpa only [dyadicDistribution, finitePushforward, hi, filter_true] using hmass
  unfold dyadicEntropy finiteEntropy
  have hh : ∀ r : Fin (2^0), r=0 := by
    intro r
    apply Fin.ext
    have hr := r.isLt
    norm_num at hr
    omega
  simp_rw [hh, hv]
  simp [Real.negMulLog_def]

def dyadicMinority {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) : ℝ :=
  2 * ∑ i, min (dyadicDistribution p f (j+1) (dyadicLower j i))
    (dyadicDistribution p f (j+1) (dyadicUpper j i))

def dyadicBitBias {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) : ℝ :=
  ∑ i, |dyadicDistribution p f (j+1) (dyadicLower j i) -
    dyadicDistribution p f (j+1) (dyadicUpper j i)|

theorem dyadic_entropy_step_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    dyadicEntropy p f (j+1) - dyadicEntropy p f j =
      ∑ i, pairEntropy (dyadicDistribution p f (j+1) (dyadicLower j i))
        (dyadicDistribution p f (j+1) (dyadicUpper j i)) := by
  have hh := dyadic_entropy_increment j (dyadicDistribution p f (j+1))
  rw [dyadic_distribution_project p f (Nat.le_succ j)] at hh
  exact hh

theorem dyadic_entropy_step_sq {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (j : ℕ) :
    (dyadicEntropy p f (j+1) - dyadicEntropy p f j)^2 ≤ 2 * dyadicMinority p f j := by
  rw [dyadic_entropy_step_eq]
  have hn := finite_pushforward_nonneg p (fun a => dyadicIndex (j+1) (f a)) hp
  have hs : ∑ i, (dyadicDistribution p f (j+1) (dyadicLower j i) +
      dyadicDistribution p f (j+1) (dyadicUpper j i)) = 1 := by
    rw [← dyadic_split_sum, dyadicDistribution, finite_pushforward_sum, hmass]
  have hh := sum_pairEntropy_sq_le _ _ (fun i => hn _) (fun i => hn _) hs
  convert hh using 1 <;> simp only [dyadicMinority, dyadicDistribution]
  ring

theorem dyadic_entropy_step_lower {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (j : ℕ) :
    dyadicMinority p f j * Real.log 2 ≤ dyadicEntropy p f (j+1) - dyadicEntropy p f j := by
  rw [dyadic_entropy_step_eq]
  exact sum_pairEntropy_lower _ _
    (fun i => finite_pushforward_nonneg p _ hp _) (fun i => finite_pushforward_nonneg p _ hp _)

theorem dyadic_entropy_telescope {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a, p a = 1) (L : ℕ) :
    ∑ j ∈ range L, (dyadicEntropy p f (j+1) - dyadicEntropy p f j) = dyadicEntropy p f L := by
  induction L with
  | zero => simp [dyadic_entropy_zero p f hmass]
  | succ L ih => rw [sum_range_succ, ih]; ring

theorem dyadic_prefix_minority {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (L : ℕ) (hL : 0<L)
    (g : ℝ) (hg : 0 ≤ g)
    (hbudget : g * L * Real.log 2 ≤ dyadicEntropy p f L) :
    g^2 * (Real.log 2)^2 / 2 * L ≤ ∑ j ∈ range L, dyadicMinority p f j := by
  have hh := minority_mass_lower (range L)
    (fun j => dyadicEntropy p f (j+1) - dyadicEntropy p f j)
    (dyadicMinority p f) (g*Real.log 2) (by simpa using hL)
    (mul_nonneg hg (Real.log_nonneg (by norm_num)))
    (fun j _ => dyadic_entropy_step_sq p f hp hmass j)
    (by rw [dyadic_entropy_telescope p f hmass]; simpa only [card_range, mul_assoc, mul_left_comm, mul_comm] using hbudget)
  convert hh using 1
  simp only [card_range]
  ring

#print axioms dyadic_prefix_minority
end
end Erdos18c
