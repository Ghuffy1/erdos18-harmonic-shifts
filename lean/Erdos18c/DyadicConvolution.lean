import Erdos18c.DyadicEntropy
import Erdos18c.FiniteConvolution

open Finset
namespace Erdos18c
noncomputable section

def dyadicProject {u v : ℕ} (h : u ≤ v) : Fin (2^v) →+ Fin (2^u) where
  toFun x := dyadicIndex u x.val
  map_zero' := by apply Fin.ext; simp [dyadicIndex]
  map_add' x y := by
    apply Fin.ext
    change (x.val+y.val) % 2^v % 2^u = (x.val%2^u+y.val%2^u)%2^u
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)]
    exact Nat.add_mod _ _ _

def dyadicHalf (j : ℕ) : Fin (2^(j+1)) := ⟨2^j, by
  have hp : 0 < (2:ℕ)^j := pow_pos (by norm_num) _
  rw [pow_succ]
  omega⟩

theorem dyadicHalf_add_self (j : ℕ) : dyadicHalf j + dyadicHalf j = 0 := by
  apply Fin.ext
  change (2^j+2^j)%2^(j+1)=0
  have hh : 2^j+2^j=2^(j+1) := by rw [pow_succ]; omega
  rw [hh, Nat.mod_self]

@[simp] theorem dyadicLower_add_half (j : ℕ) (i : Fin (2^j)) :
    dyadicLower j i + dyadicHalf j = dyadicUpper j i := by
  apply Fin.ext
  change (i.val+2^j)%2^(j+1)=2^j+i.val
  have hi := i.isLt
  rw [Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  omega

@[simp] theorem dyadicUpper_add_half (j : ℕ) (i : Fin (2^j)) :
    dyadicUpper j i + dyadicHalf j = dyadicLower j i := by
  apply Fin.ext
  change (2^j+i.val+2^j)%2^(j+1)=i.val
  have he : 2^j+i.val+2^j=2^(j+1)+i.val := by rw [pow_succ]; omega
  rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (i.isLt.trans_le (by rw [pow_succ]; omega))]

theorem dyadic_involutionBias (j : ℕ) (p : Fin (2^(j+1)) → ℝ) :
    involutionBias (dyadicHalf j) p = ∑ i, |p (dyadicLower j i)-p (dyadicUpper j i)| := by
  unfold involutionBias finiteL1 realDifference
  rw [dyadic_split_sum]
  simp only [dyadicLower_add_half, dyadicUpper_add_half,
    abs_sub_comm (p (dyadicUpper j _)) (p (dyadicLower j _))]
  rw [sum_add_distrib]
  ring

theorem dyadic_bitBias_eq_involution {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    dyadicBitBias p f j = involutionBias (dyadicHalf j) (dyadicDistribution p f (j+1)) :=
  (dyadic_involutionBias j _).symm

theorem abs_sub_add_two_min (x y : ℝ) : |x-y|+2*min x y=x+y := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]; ring

theorem dyadic_bitBias_add_minority {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → ℕ) (hmass : ∑ a, p a=1) (j : ℕ) :
    dyadicBitBias p f j + dyadicMinority p f j = 1 := by
  have hs := sum_congr (s₁ := univ) rfl (fun (i : Fin (2^j)) _ =>
    abs_sub_add_two_min (dyadicDistribution p f (j+1) (dyadicLower j i))
      (dyadicDistribution p f (j+1) (dyadicUpper j i)))
  rw [sum_add_distrib, ← mul_sum] at hs
  change dyadicBitBias p f j + dyadicMinority p f j = _ at hs
  rw [← dyadic_split_sum, dyadicDistribution, finite_pushforward_sum, hmass] at hs
  exact hs

theorem dyadicMinority_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (j : ℕ) : 0 ≤ dyadicMinority p f j := by
  unfold dyadicMinority
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro i _
  exact le_min (finite_pushforward_nonneg p _ hp _) (finite_pushforward_nonneg p _ hp _)

theorem dyadic_bitBias_convolutionPow {k j : ℕ} (hj : j+1 ≤ k)
    (p : Fin (2^k) → ℝ) (r : ℕ) :
    dyadicBitBias (realConvolutionPow p r) Fin.val j ≤ (dyadicBitBias p Fin.val j)^r := by
  rw [dyadic_bitBias_eq_involution, dyadic_bitBias_eq_involution]
  change involutionBias (dyadicHalf j)
    (finitePushforward (realConvolutionPow p r) (dyadicProject hj)) ≤ _
  rw [pushforward_realConvolutionPow]
  exact involutionBias_convolutionPow_le _ (dyadicHalf_add_self j) _ r

#print axioms dyadic_bitBias_convolutionPow
end
end Erdos18c
