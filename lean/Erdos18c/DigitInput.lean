import Erdos18c.LinearDigitSupply
import Erdos18c.HarmonicMixing

open Finset Filter
namespace Erdos18c
noncomputable section

def uniformDigitWeight (A : Finset ℕ) (_a : A) : ℝ := 1/(A.card:ℝ)
def uniformDigitProjection (A : Finset ℕ) (L : ℕ) : Fin (2^L) → ℝ :=
  dyadicDistribution (uniformDigitWeight A) (fun a => a.val) L
def positiveDigitWeight (A : Finset ℕ) (z : A × Fin 2) : ℝ := uniformDigitWeight A z.1 / 2
def positiveDigitValue (A : Finset ℕ) (z : A × Fin 2) : ℕ := z.1.val+z.2.val
def positiveDigitProjection (A : Finset ℕ) (L : ℕ) : Fin (2^L) → ℝ :=
  dyadicDistribution (positiveDigitWeight A) (positiveDigitValue A) L

theorem uniformDigitWeight_sum (A : Finset ℕ) (hA : A.Nonempty) :
    ∑ a : A, uniformDigitWeight A a = 1 := by
  have hc : (A.card:ℝ)≠0 := by exact_mod_cast (ne_of_gt (card_pos.mpr hA))
  simp only [uniformDigitWeight,sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe]
  field_simp

theorem positiveDigitWeight_sum (A : Finset ℕ) (hA : A.Nonempty) :
    ∑ z : A × Fin 2, positiveDigitWeight A z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [positiveDigitWeight,Fin.sum_univ_two]
  have he (a : A) : uniformDigitWeight A a / 2 + uniformDigitWeight A a / 2 = uniformDigitWeight A a := by ring
  simp_rw [he]
  exact uniformDigitWeight_sum A hA

theorem uniformDigitProjection_eq (A : Finset ℕ) (L : ℕ) (x : Fin (2^L)) :
    uniformDigitProjection A L x = natResidueMass A (2^L) x.val := by
  unfold uniformDigitProjection dyadicDistribution finitePushforward uniformDigitWeight
  rw [sum_filter,univ_eq_attach]
  change (∑ a ∈ A.attach, if dyadicIndex L a.val=x then 1/(A.card:ℝ) else 0) = _
  rw [sum_attach A (fun a : ℕ => if dyadicIndex L a=x then 1/(A.card:ℝ) else 0)]
  have he (a : ℕ) : dyadicIndex L a=x ↔ Nat.ModEq (2^L) a x.val := by
    simp only [Fin.ext_iff,dyadicIndex,Nat.ModEq,Nat.mod_eq_of_lt x.isLt]
  simp_rw [he]
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,natResidueMass,natResidueFiber,div_eq_mul_inv,one_mul]

theorem dyadicIndex_add_one (L n : ℕ) :
    dyadicIndex L (n+1) = dyadicIndex L n + 1 := by
  apply Fin.ext
  simp [dyadicIndex,Fin.val_add,Nat.add_mod]

theorem positiveDigitProjection_smooth (A : Finset ℕ) (L : ℕ) (x : Fin (2^L)) :
    positiveDigitProjection A L x =
      (uniformDigitProjection A L x + uniformDigitProjection A L (x-1))/2 := by
  unfold positiveDigitProjection uniformDigitProjection dyadicDistribution finitePushforward
  rw [sum_filter,Fintype.sum_prod_type]
  have he (a : A) :
      (∑ e : Fin 2, if dyadicIndex L (positiveDigitValue A (a,e))=x then positiveDigitWeight A (a,e) else 0) =
      ((if dyadicIndex L a.val=x then uniformDigitWeight A a else 0) +
       (if dyadicIndex L a.val=x-1 then uniformDigitWeight A a else 0))/2 := by
    simp [Fin.sum_univ_two,positiveDigitValue,positiveDigitWeight,dyadicIndex_add_one,
      eq_sub_iff_add_eq,add_div]
    split_ifs <;> ring
  simp_rw [he]
  rw [← sum_div,sum_add_distrib]
  simp only [sum_filter]

theorem positiveDigitProjection_probability (A : Finset ℕ) (hA : A.Nonempty) (L : ℕ) :
    (∀ x,0≤positiveDigitProjection A L x) ∧ ∑ x,positiveDigitProjection A L x=1 := by
  refine ⟨finite_pushforward_nonneg _ _ (fun z => by unfold positiveDigitWeight uniformDigitWeight; positivity), ?_⟩
  rw [positiveDigitProjection,dyadicDistribution,finite_pushforward_sum,positiveDigitWeight_sum A hA]

theorem uniformDigitProjection_probability (A : Finset ℕ) (hA : A.Nonempty) (L : ℕ) :
    (∀ x,0≤uniformDigitProjection A L x) ∧ ∑ x,uniformDigitProjection A L x=1 := by
  refine ⟨finite_pushforward_nonneg _ _ (fun a => by unfold uniformDigitWeight; positivity), ?_⟩
  rw [uniformDigitProjection,dyadicDistribution,finite_pushforward_sum,uniformDigitWeight_sum A hA]

theorem odd_uniform_parity (A : Finset ℕ) (hA : A.Nonempty) (hodd : ∀ a∈A,Odd a) :
    uniformDigitProjection A 1 0=0 ∧ uniformDigitProjection A 1 1=1 := by
  have hzero : uniformDigitProjection A 1 0=0 := by
    rw [uniformDigitProjection_eq]
    have he : natResidueFiber A (2^1) 0=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨haA,haM⟩ := mem_filter.mp ha
      have hm : a%2=0 := by simpa [Nat.ModEq] using haM
      have ho : a%2=1 := Nat.odd_iff.mp (hodd a haA)
      omega
    norm_num only [pow_one] at he
    simp [natResidueMass,he]
  have hs := (uniformDigitProjection_probability A hA 1).2
  have hu : (univ : Finset (Fin (2^1)))={0,1} := by decide
  rw [hu,sum_pair (by decide),hzero,zero_add] at hs
  exact ⟨hzero,hs⟩

theorem positiveDigit_uniform_parity (A : Finset ℕ) (hA : A.Nonempty) (hodd : ∀ a∈A,Odd a)
    (x : Fin (2^1)) : positiveDigitProjection A 1 x=1/2 := by
  have h := odd_uniform_parity A hA hodd
  have hm1 : (-1 : Fin (2^1))=1 := by decide
  have hx : x=0 ∨ x=1 := by
    by_cases h0 : x=0
    · exact Or.inl h0
    · right
      apply Fin.ext
      change x.val=1
      have hn := x.isLt
      have hz : x.val≠0 := fun he => h0 (Fin.ext he)
      norm_num at hn
      omega
  rcases hx with rfl | rfl
  · rw [positiveDigitProjection_smooth,zero_sub,hm1,h.1,h.2]
    norm_num
  · rw [positiveDigitProjection_smooth,sub_self,h.1,h.2]
    norm_num

theorem positiveDigit_prefix_cap {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (hc : c≤2)
    (L : ℕ) (hL : 0<L) (hLk : L≤k) (x : Fin (2^L)) :
    positiveDigitProjection A L x ≤ (2:ℝ)^(-(c/2)*(L:ℝ)) := by
  by_cases hL1 : L=1
  · subst L
    rw [positiveDigit_uniform_parity A hA.nonempty hA.odd]
    have hh : (2:ℝ)^(-1:ℝ) ≤ (2:ℝ)^(-(c/2)*(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at hh ⊢
    exact hh
  · have hLL : 2≤L := by omega
    rw [positiveDigitProjection_smooth]
    have h1 := hA.spread L hLL hLk x.val
    have h2 := hA.spread L hLL hLk (x-1).val
    rw [← uniformDigitProjection_eq] at h1 h2
    linarith

theorem finiteEntropy_lower_of_cap {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (M : ℝ)
    (hcap : ∀ x,p x≤M) : -Real.log M ≤ finiteEntropy univ p := by
  have hh := sum_mul_log_le_log_bound univ p (fun x _ => hp x) (fun x _ => hcap x)
  rw [hs,one_mul] at hh
  have he : finiteEntropy univ p = -(∑ x,p x*Real.log (p x)) := by
    simp [finiteEntropy,Real.negMulLog_def,neg_mul,sum_neg_distrib]
  rw [he]
  linarith

theorem positiveDigit_entropy_prefix {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (hc : c≤2)
    (L : ℕ) (hL : 0<L) (hLk : L≤k) :
    (c/2)*(L:ℝ)*Real.log 2 ≤ dyadicEntropy (positiveDigitProjection A k) Fin.val L := by
  have he : dyadicDistribution (positiveDigitProjection A k) Fin.val L = positiveDigitProjection A L :=
    dyadic_distribution_project (positiveDigitWeight A) (positiveDigitValue A) hLk
  unfold dyadicEntropy
  rw [he]
  have hp := positiveDigitProjection_probability A hA.nonempty L
  have hh := finiteEntropy_lower_of_cap _ hp.1 hp.2 _ (positiveDigit_prefix_cap hA hc L hL hLk)
  rw [Real.log_rpow (by norm_num : (0:ℝ)<2)] at hh
  linarith

#print axioms positiveDigitProjection_smooth
end
end Erdos18c
