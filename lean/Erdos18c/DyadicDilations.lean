import Erdos18c.DyadicConvolution

open Finset
namespace Erdos18c
noncomputable section

def dyadicScale (a m : ℕ) : Fin (2^m) →+ Fin (2^(a+m)) where
  toFun x := ⟨2^a*x.val, by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left x.isLt (by positivity)⟩
  map_zero' := by apply Fin.ext; simp
  map_add' x y := by
    apply Fin.ext
    change 2^a*((x.val+y.val)%2^m) = (2^a*x.val+2^a*y.val)%2^(a+m)
    rw [← Nat.mul_add, pow_add, Nat.mul_mod_mul_left]

theorem dyadicScale_injective (a m : ℕ) : Function.Injective (dyadicScale a m) := by
  intro x y h
  have hv := congrArg Fin.val h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^a) hv

theorem dyadicScale_half (a j : ℕ) :
    dyadicScale a (j+1) (dyadicHalf j) =
      (dyadicHalf (a+j) : Fin (2^(a+(j+1)))) := by
  apply Fin.ext
  change 2^a*2^j = 2^(a+j)
  exact (pow_add 2 a j).symm

def dyadicMultiplier (k a : ℕ) (x : Fin (2^k)) : Fin (2^k) :=
  dyadicIndex k (2^a*x.val)

def dyadicDilate (k a : ℕ) (p : Fin (2^k) → ℝ) : Fin (2^k) → ℝ :=
  finitePushforward p (dyadicMultiplier k a)

theorem dyadic_multiplier_project {k m a : ℕ} (hj : a+m ≤ k) :
    (fun x : Fin (2^k) => dyadicIndex (a+m) (dyadicMultiplier k a x).val) =
      fun x : Fin (2^k) => (dyadicScale a m) (dyadicIndex m x.val) := by
  funext x
  apply Fin.ext
  dsimp [dyadicIndex,dyadicMultiplier,dyadicScale]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj)]
  rw [pow_add, Nat.mul_mod_mul_left]

theorem dyadicDilate_project {k m a : ℕ} (hj : a+m ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicDistribution (dyadicDilate k a p) Fin.val (a+m) =
      finitePushforward (dyadicDistribution p Fin.val m) (dyadicScale a m) := by
  unfold dyadicDistribution dyadicDilate
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  exact dyadic_multiplier_project hj

def dyadicScaleBit (a j : ℕ) : Fin (2^(j+1)) →+ Fin (2^(a+j+1)) where
  toFun x := ⟨2^a*x.val, by
    rw [show (2:ℕ)^(a+j+1)=2^a*2^(j+1) by rw [Nat.add_assoc, pow_add]]
    exact Nat.mul_lt_mul_of_pos_left x.isLt (by positivity)⟩
  map_zero' := by apply Fin.ext; simp
  map_add' x y := by
    apply Fin.ext
    change 2^a*((x.val+y.val)%2^(j+1)) = (2^a*x.val+2^a*y.val)%2^(a+j+1)
    rw [← Nat.mul_add, show (2:ℕ)^(a+j+1)=2^a*2^(j+1) by rw [Nat.add_assoc, pow_add], Nat.mul_mod_mul_left]

theorem dyadicScaleBit_injective (a j : ℕ) : Function.Injective (dyadicScaleBit a j) := by
  intro x y h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^a) (congrArg Fin.val h)

theorem dyadicScaleBit_half (a j : ℕ) :
    dyadicScaleBit a j (dyadicHalf j) = dyadicHalf (a+j) := by
  apply Fin.ext
  change 2^a*2^j=2^(a+j)
  exact (pow_add 2 a j).symm

theorem dyadicDilate_project_bit {k j a : ℕ} (hj : a+j+1 ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicDistribution (dyadicDilate k a p) Fin.val (a+j+1) =
      finitePushforward (dyadicDistribution p Fin.val (j+1)) (dyadicScaleBit a j) := by
  unfold dyadicDistribution dyadicDilate
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  funext x
  apply Fin.ext
  dsimp [dyadicIndex,dyadicMultiplier,dyadicScaleBit]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj), Nat.add_assoc, pow_add, Nat.mul_mod_mul_left]

theorem dyadicDilate_bitBias_add {k a j : ℕ} (hj : a+(j+1) ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicBitBias (dyadicDilate k a p) Fin.val (a+j) = dyadicBitBias p Fin.val j := by
  rw [dyadic_bitBias_eq_involution, dyadic_bitBias_eq_involution]
  rw [dyadicDilate_project_bit (by omega : a+j+1≤k)]
  have hh := involutionBias_pushforward (dyadicDistribution p Fin.val (j+1))
    (dyadicScaleBit a j) (dyadicScaleBit_injective _ _) (dyadicHalf j)
  rw [dyadicScaleBit_half] at hh
  exact hh

theorem dyadicDilate_bitBias {k a j : ℕ} (hj : j<k) (ha : a≤j)
    (p : Fin (2^k) → ℝ) :
    dyadicBitBias (dyadicDilate k a p) Fin.val j = dyadicBitBias p Fin.val (j-a) := by
  have he : a+(j-a)=j := Nat.add_sub_of_le ha
  have hh := dyadicDilate_bitBias_add (a:=a) (j:=j-a) (by omega : a+(j-a+1) ≤ k) p
  simpa only [he] using hh

theorem dyadicBitBias_le_one {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1) (j : ℕ) : dyadicBitBias p f j ≤ 1 := by
  rw [dyadic_bitBias_eq_involution]
  have hn := finite_pushforward_nonneg p (fun a => dyadicIndex (j+1) (f a)) hp
  have hs : finiteL1 (dyadicDistribution p f (j+1))=1 := by
    simp only [finiteL1, dyadicDistribution, abs_of_nonneg (hn _), finite_pushforward_sum, hsum]
  exact (involutionBias_le_l1 _ _).trans_eq hs

theorem dyadicDilate_nonneg {k a : ℕ} (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : Fin (2^k)) : 0 ≤ dyadicDilate k a p x :=
  finite_pushforward_nonneg p _ hp x

theorem dyadicDilate_sum {k a : ℕ} (p : Fin (2^k) → ℝ) :
    ∑ x, dyadicDilate k a p x = ∑ x, p x := finite_pushforward_sum _ _

#print axioms dyadicDilate_project
end
end Erdos18c
