import Erdos18c.LocalRepresentatives
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

open Finset Filter
namespace Erdos18c
noncomputable section

def localCopies (k : ℕ) : ℕ := ⌈32768*(Real.log (k:ℝ))^4⌉₊+1
def localCount (k : ℕ) : ℕ := 2*localCopies k*(binaryLength k+2)
def localHost (k : ℕ) : ℕ := linearDigitHost k+4*k
def localHeight (k : ℕ) : ℕ := localCount k*(localHost k).factorial

theorem factorial_multiset_height {F R u : ℕ} (h : HasFactorialDivisorMultiset F R u) :
    R≤u*F.factorial := by
  obtain ⟨s,hs,hsum,hcard⟩ := h
  have hh := Multiset.sum_le_card_nsmul s F.factorial
    (fun d hd => Nat.le_of_dvd (Nat.factorial_pos _) (hs d hd))
  rw [hsum] at hh
  exact hh.trans (by simpa using Nat.mul_le_mul_right F.factorial hcard)

theorem localCount_pos (k : ℕ) : 0<localCount k := by
  unfold localCount localCopies
  positivity

theorem localHeight_pos (k : ℕ) : 0<localHeight k :=
  Nat.mul_pos (localCount_pos k) (Nat.factorial_pos _)

theorem harmonicSum_le (k : ℕ) : harmonicSum k ≤ 1+Real.log (k:ℝ) := by
  have he : harmonicSum k = (harmonic k : ℝ) := by
    simp [harmonicSum,harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [he]
  exact harmonic_le_one_add_log k

theorem eventually_local_copy_condition : ∀ᶠ k : ℕ in atTop,
    Real.log (2*(k:ℝ)) ≤ (localCopies k:ℝ)*
      ((linearDigitRate k/2)^2*(Real.log 2)^2/2)/harmonicSum k := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (max 1 (Real.log 1000)), eventually_ge_atTop 2] with k ht hk
  let t := Real.log (k:ℝ)
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  have ht1000 : Real.log 1000≤t := (le_max_right _ _).trans ht
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hH : harmonicSum k≤2*t := (harmonicSum_le k).trans (by dsimp [t]; linarith)
  have hH0 := (harmonicSum_pos k (by omega)).le
  have hL : Real.log (linearDigitHost k:ℝ)≤2*t := by
    simp only [linearDigitHost,Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) hkp.ne']
    dsimp [t] at *
    linarith
  have hLp : 0<Real.log (linearDigitHost k:ℝ) := Real.log_pos (by
    simp only [linearDigitHost,Nat.cast_mul,Nat.cast_ofNat]
    have h1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    linarith)
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hhalf : (1/2:ℝ)≤Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have h2t : Real.log (2*(k:ℝ))≤2*t := by
    rw [Real.log_mul (by norm_num) hkp.ne']
    have : Real.log 2≤1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    dsimp [t] at *
    linarith
  have hlog2k0 : 0≤Real.log (2*(k:ℝ)) := Real.log_nonneg (by
    have : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    linarith)
  have hden : 0<(linearDigitRate k/2)^2*(Real.log 2)^2 := by
    unfold linearDigitRate linearDigitDelta
    positivity
  have hreq : 2*harmonicSum k*Real.log (2*(k:ℝ)) /
      ((linearDigitRate k/2)^2*(Real.log 2)^2) ≤ (localCopies k:ℝ) := by
    calc
      _ = 512*harmonicSum k*Real.log (2*(k:ℝ)) * Real.log (linearDigitHost k:ℝ)^2 /
          (Real.log 2)^2 := by
        unfold linearDigitRate linearDigitDelta
        field_simp
        ring
      _ ≤ 512*(2*t)*(2*t)*(2*t)^2/((1/2:ℝ)^2) := by
        gcongr
      _ = 32768*t^4 := by ring
      _ ≤ _ := by
        have hh := Nat.le_ceil (32768*t^4)
        have hstep : (⌈32768*t^4⌉₊:ℝ) ≤ localCopies k := by
          dsimp [localCopies,t]
          exact_mod_cast (Nat.le_succ _)
        exact hh.trans hstep
  have hscaled := (div_le_iff₀ hden).mp hreq
  apply (le_div_iff₀ (harmonicSum_pos k (by omega))).mpr
  nlinarith

theorem eventually_local_count_bound : ∀ᶠ k : ℕ in atTop,
    (localCount k:ℝ)≤400000*(Real.log (k:ℝ))^5 := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop 1,eventually_ge_atTop 2] with k ht hk
  let t := Real.log (k:ℝ)
  have ht4 : 1≤t^4 := one_le_pow₀ ht
  have hceil := (Nat.ceil_lt_add_one (show 0≤32768*t^4 by positivity)).le
  have hr : (localCopies k:ℝ)≤32770*t^4 := by
    dsimp [localCopies]
    push_cast
    dsimp [t] at *
    linarith
  have hb : (binaryLength k:ℝ)+2 ≤ 6*t := by
    have hh := binaryLength_log_upper k hk
    dsimp [t] at *
    linarith
  calc
    (localCount k:ℝ) = 2*(localCopies k:ℝ)*((binaryLength k:ℝ)+2) := by simp [localCount]
    _ ≤ 2*(32770*t^4)*(6*t) := by gcongr
    _ ≤ 400000*t^5 := by nlinarith [pow_nonneg (by linarith : 0≤t) 5]

theorem eventually_local_representatives : ∀ᶠ k : ℕ in atTop,
    ∀ R : ℕ, ∃ S,0<S ∧ dyadicIndex k S=dyadicIndex k R ∧
      HasFactorialDivisorMultiset (localHost k) S (localCount k) := by
  filter_upwards [eventually_linear_digit_profile,eventually_local_copy_condition,eventually_ge_atTop 1] with k hp hr hk
  intro R
  have hh := modular_representatives_of_profile hk hp.2.2
    (by unfold linearDigitRate; linarith [hp.1])
    (by unfold linearDigitRate; linarith [hp.2.1]) hr R
  exact hh

theorem eventually_local_height_bound : ∀ᶠ k : ℕ in atTop,
    Real.log (localHeight k:ℝ) ≤ 4096*(k:ℝ)*Real.log (k:ℝ) := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_local_count_bound,htend.eventually_ge_atTop
    (max 1 (max (Real.log 400000) (Real.log 1004))),eventually_ge_atTop 2] with k hcount ht hk
  let t := Real.log (k:ℝ)
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  have htC : Real.log 400000≤t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htF : Real.log 1004≤t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hCpos : (0:ℝ)<localCount k := by exact_mod_cast localCount_pos k
  have hlogC : Real.log (localCount k:ℝ)≤6*t := by
    have hh := Real.log_le_log hCpos hcount
    rw [Real.log_mul (by norm_num) (by positivity : t^5≠0),Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have hlogt : Real.log t≤t := (Real.log_le_sub_one_of_pos (by linarith : 0<t)).trans (by linarith)
    linarith
  have hFval : (localHost k:ℝ)=1004*(k:ℝ) := by simp [localHost,linearDigitHost]; ring
  have hFpos : (0:ℝ)<localHost k := by rw [hFval]; positivity
  have hlogF : Real.log (localHost k:ℝ)≤2*t := by
    rw [hFval,Real.log_mul (by norm_num) hkp.ne']
    dsimp [t] at *
    linarith
  have hfact : Real.log ((localHost k).factorial:ℝ) ≤ (localHost k:ℝ)*Real.log (localHost k:ℝ) := by
    have hh : ((localHost k).factorial:ℝ) ≤ (localHost k:ℝ)^(localHost k) := by
      exact_mod_cast Nat.factorial_le_pow (localHost k)
    have hp : (0:ℝ)<(localHost k).factorial := by exact_mod_cast Nat.factorial_pos _
    have hl := Real.log_le_log hp hh
    rwa [Real.log_pow] at hl
  have hprod := mul_le_mul_of_nonneg_left hlogF hFpos.le
  have hk1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hkt : 0≤((k:ℝ)-1)*t := mul_nonneg (by linarith) (by linarith)
  change Real.log ((localCount k*(localHost k).factorial:ℕ):ℝ) ≤ _
  rw [Nat.cast_mul,Real.log_mul hCpos.ne' (by exact_mod_cast Nat.factorial_ne_zero _)]
  rw [hFval] at hprod
  nlinarith

#print axioms eventually_local_representatives
#print axioms eventually_local_count_bound
end
end Erdos18c
