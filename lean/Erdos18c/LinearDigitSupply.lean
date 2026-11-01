import Erdos18c.DivisorDigits
import Erdos18c.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset Filter
namespace Erdos18c
noncomputable section

theorem binaryLength_log_lower (F : ℕ) (hF : 0<F) : Real.log (F:ℝ) ≤ binaryLength F := by
  have hp : (F:ℝ) ≤ (2:ℝ)^binaryLength F := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) F).le
  have hl := Real.log_le_log (by exact_mod_cast hF) hp
  rw [Real.log_pow] at hl
  have hlog : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (binaryLength F))])

theorem binaryLength_log_upper (F : ℕ) (hF : 2≤F) : (binaryLength F:ℝ) ≤ 4*Real.log (F:ℝ) := by
  have hp : (2:ℝ)^(Nat.log 2 F) ≤ (F:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : F≠0)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 F)) hp
  rw [Real.log_pow] at hl
  have hhalf : (1/2:ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have hnlog : 0≤(Nat.log 2 F:ℝ) := Nat.cast_nonneg _
  have hFlog : Real.log 2 ≤ Real.log (F:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hF)
  have hmul := mul_le_mul_of_nonneg_left hhalf hnlog
  unfold binaryLength
  push_cast
  nlinarith

theorem eventually_primeCounting_lower : ∀ᶠ F : ℕ in atTop,
    (F:ℝ)/(2*Real.log (F:ℝ)) ≤ (Nat.primeCounting F:ℝ) := by
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))).def (by norm_num : (0:ℝ)<1/16)
  have hsucc : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  filter_upwards [hsucc.eventually hsmall, eventually_ge_atTop 2] with F hs hF
  have hpos : (0:ℝ)<F := by exact_mod_cast (show 0<F by omega)
  have hlogpos : 0<Real.log (F:ℝ) := Real.log_pos (by exact_mod_cast hF)
  have hnorm : |Real.log ((F+1:ℕ):ℝ)| ≤ (1/16) * (((F+1:ℕ):ℝ)) := by
    simp only [Function.comp_apply,id_eq,Real.norm_eq_abs] at hs
    rwa [abs_of_nonneg (show (0:ℝ)≤((F+1:ℕ):ℝ) by positivity)] at hs
  have hlogsmall : Real.log ((F+1:ℕ):ℝ) ≤ (F:ℝ)/8 := by
    have h := (le_abs_self _).trans hnorm
    have h1 : (1:ℝ)≤F := by exact_mod_cast (show 1≤F by omega)
    push_cast at h
    push_cast
    linarith
  have htwo : (5/8:ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have hnum : (F:ℝ)/2 ≤ (F:ℝ)*Real.log 2 - Real.log ((F+1:ℕ):ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left htwo hpos.le]
  have hprime := Chebyshev.pi_ge F
  have hh := div_le_div_of_nonneg_right hnum hlogpos.le
  calc
    (F:ℝ)/(2*Real.log (F:ℝ)) = ((F:ℝ)/2)/Real.log (F:ℝ) := by ring
    _ ≤ _ := hh
    _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using hprime

def linearDigitHost (k : ℕ) : ℕ := 1000*k
def linearDigitDelta (k : ℕ) : ℝ := 1/Real.log (linearDigitHost k:ℝ)
def linearDigitRate (k : ℕ) : ℝ := linearDigitDelta k/8
def linearInputRate (k : ℕ) : ℝ := linearDigitDelta k/16

theorem linearDigitHost_tendsto : Tendsto linearDigitHost atTop atTop := by
  exact tendsto_atTop_mono (fun k => by dsimp [linearDigitHost]; omega) tendsto_id

theorem eventually_linear_digit_count : ∀ᶠ k : ℕ in atTop,
    0<linearDigitDelta k ∧ linearDigitDelta k≤1 ∧
    (∀ l, 1≤l → l≤k → (2:ℝ)^(linearDigitRate k*(l:ℝ)) ≤
      (shortFactorialDigits (linearDigitHost k) l).card) := by
  have hlog : Tendsto (fun k => Real.log (linearDigitHost k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp linearDigitHost_tendsto)
  filter_upwards [linearDigitHost_tendsto.eventually eventually_primeCounting_lower,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with k hprime hlog hk
  let F := linearDigitHost k
  have hF : 2≤F := by dsimp [F,linearDigitHost]; omega
  have hFp : (0:ℝ)<F := by exact_mod_cast (show 0<F by omega)
  have hlogp : 0<Real.log (F:ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hdpos : 0<linearDigitDelta k := one_div_pos.mpr hlogp
  have hdle : linearDigitDelta k≤1 := (div_le_one hlogp).mpr hlog
  have hpower : (F:ℝ)^linearDigitDelta k = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hFp]
    unfold linearDigitDelta
    change Real.exp (Real.log (F:ℝ) * (1/Real.log (F:ℝ))) = _
    rw [mul_one_div_cancel hlogp.ne']
  have hcapacity : (k:ℝ)*(F:ℝ)^linearDigitDelta k ≤ (Nat.primeCounting F:ℝ)*(binaryLength F:ℝ) := by
    have hlen := binaryLength_log_lower F (by omega)
    have hprod := mul_le_mul_of_nonneg_right hprime (show (0:ℝ)≤Real.log (F:ℝ) from hlogp.le)
    have hcancel : ((F:ℝ)/(2*Real.log (F:ℝ))) * Real.log (F:ℝ) = (F:ℝ)/2 := by field_simp
    rw [hcancel] at hprod
    have hprod2 := mul_le_mul_of_nonneg_left hlen
      (show (0:ℝ)≤(Nat.primeCounting F:ℝ) from Nat.cast_nonneg _)
    rw [hpower]
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hFval : (F:ℝ)=1000*(k:ℝ) := by simp [F,linearDigitHost]
    nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
  refine ⟨hdpos,hdle,?_⟩
  intro l hl hlk
  have hh := shortFactorialDigits_uniform_linear hF hdpos hdle hcapacity l hl hlk
  simpa only [linearDigitRate,div_mul_eq_mul_div] using hh

def linearInitialBits (k : ℕ) : ℕ := Nat.log 2 (linearDigitHost k)
def linearDigitSet (k : ℕ) : Finset ℕ :=
  binaryBlockSet (linearDigitHost k) k (linearInitialBits k) (binaryLength k)

theorem eventually_initial_bits_bounds : ∀ᶠ k : ℕ in atTop,
    2≤linearInitialBits k ∧ linearInitialBits k≤k ∧
    2^linearInitialBits k≤linearDigitHost k := by
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop.comp linearDigitHost_tendsto)).def
    (by norm_num : (0:ℝ)<1/4000)
  filter_upwards [hsmall,linearDigitHost_tendsto.eventually_ge_atTop 4] with k hs hF
  let F := linearDigitHost k
  have hF2 : 2≤F := by omega
  have hlogp : 0≤Real.log (F:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤F by omega))
  have hbound : Real.log (F:ℝ) ≤ (1/4000)*(F:ℝ) := by
    simp only [Function.comp_apply,id_eq,Real.norm_eq_abs] at hs
    change |Real.log (F:ℝ)| ≤ (1/4000)*|(F:ℝ)| at hs
    rwa [abs_of_nonneg hlogp,abs_of_nonneg (show (0:ℝ)≤F from Nat.cast_nonneg F)] at hs
  have hlen := binaryLength_log_upper F hF2
  have hFk : (F:ℝ)=1000*(k:ℝ) := by simp [F,linearDigitHost]
  have hsmallNat : binaryLength F≤k := by
    have hr : (binaryLength F:ℝ)≤k := by linarith
    exact_mod_cast hr
  refine ⟨?_,?_,?_⟩
  · exact Nat.le_log_of_pow_le (by decide) (by change 2^2≤F; norm_num; omega)
  · change Nat.log 2 F≤k
    exact (Nat.le_succ _).trans hsmallNat
  · exact Nat.pow_log_le_self 2 (by omega : F≠0)

theorem eventually_linear_digit_profile : ∀ᶠ k : ℕ in atTop,
    0<linearDigitDelta k ∧ linearDigitDelta k≤1 ∧
    BinaryBlockProfile (linearDigitHost k) k k (binaryLength k+1)
      (linearDigitRate k) (linearDigitSet k) := by
  filter_upwards [eventually_linear_digit_count,eventually_initial_bits_bounds] with k hc hb
  refine ⟨hc.1,hc.2.1,?_⟩
  exact binary_block_set_profile_top hb.1 hb.2.1 hb.2.2
    (by unfold linearDigitRate; linarith [hc.1])
    (by unfold linearDigitRate; linarith [hc.2.1]) hc.2.2

#print axioms eventually_linear_digit_count
#print axioms eventually_linear_digit_profile
end
end Erdos18c
