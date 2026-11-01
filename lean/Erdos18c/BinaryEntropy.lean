import Erdos18c.FiniteLaw
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Binary entropy estimates used in the harmonic-shift proof.  Finite-law
infrastructure is credited in FiniteLaw.lean; these analytic inequalities
are the scalar steps of the new manuscript.
-/

open Finset
namespace Erdos18c

theorem negMulLog_le_sqrt {p : ℝ} (hp : 0 ≤ p) :
    Real.negMulLog p ≤ (2 / Real.exp 1) * Real.sqrt p := by
  by_cases hp0 : p = 0
  · simp [hp0, Real.negMulLog_def]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  let t := -(Real.log p) / 2
  have he : Real.exp (-t) = Real.sqrt p := by
    apply (Real.log_injOn_pos (Real.exp_pos _) (Real.sqrt_pos.2 hp'))
    rw [Real.log_exp, Real.log_sqrt hp]
    dsimp [t]
    ring
  have hh := Real.mul_exp_neg_le_exp_neg_one t
  have ht : Real.negMulLog p = 2 * Real.sqrt p * (t * Real.exp (-t)) := by
    rw [he]
    dsimp [t]
    rw [Real.negMulLog_def]
    change -p * Real.log p = _
    calc
      -p * Real.log p = -(Real.sqrt p ^ 2) * Real.log p := by rw [Real.sq_sqrt hp]
      _ = _ := by ring
  rw [ht]
  have hscaled := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * Real.sqrt p)
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

theorem binEntropy_le_two_sqrt_min {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ 2 * Real.sqrt (min p (1-p)) := by
  wlog hhalf : p ≤ 1 / 2 generalizing p
  · have h := this (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) (by linarith : 1-p ≤ 1/2)
    simpa [Real.binEntropy_one_sub, min_comm] using h
  have hmin : min p (1-p) = p := min_eq_left (by linarith)
  rw [hmin, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hfirst := negMulLog_le_sqrt hp
  have hsecond : Real.negMulLog (1-p) ≤ p := by
    have := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hp1)
    linarith
  have hroot : p ≤ Real.sqrt p := by
    have hs := Real.sq_sqrt hp
    have hsn := Real.sqrt_nonneg p
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp1)]
  have hexp : 2 / Real.exp 1 ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (le_of_lt Real.exp_one_gt_two)
  have hh := mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg p)
  linarith

theorem two_min_le_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * min p (1-p) * Real.log 2 ≤ Real.binEntropy p := by
  wlog hhalf : p ≤ 1 / 2 generalizing p
  · have h := this (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) (by linarith : 1-p ≤ 1/2)
    simpa [Real.binEntropy_one_sub, min_comm] using h
  have hconc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (2:ℝ)⁻¹ ∈ Set.Icc 0 1 by norm_num)
    (show 0 ≤ 1 - 2*p by linarith)
    (show 0 ≤ 2*p by linarith)
    (show (1-2*p) + 2*p = 1 by ring)
  norm_num only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero, mul_zero,
    zero_add, Real.binEntropy_two_inv] at hconc
  have hhalfentropy : Real.binEntropy (1/2) = Real.log 2 := by
    convert Real.binEntropy_two_inv using 1
    norm_num
  rw [hhalfentropy] at hconc
  have harg : (2*p)*(1/2) = p := by ring
  rw [harg] at hconc
  rw [min_eq_left (by linarith : p ≤ 1-p)]
  exact hconc

noncomputable def pairEntropy (x y : ℝ) : ℝ :=
  Real.negMulLog x + Real.negMulLog y - Real.negMulLog (x+y)

theorem pairEntropy_eq (x y : ℝ) :
    pairEntropy x y = (x+y) * Real.binEntropy (x/(x+y)) := by
  by_cases hs : x+y = 0
  · have hy : y = -x := by linarith
    simp [pairEntropy, hy, Real.negMulLog_def, Real.log_neg_eq_log]
  have hxid := Real.negMulLog_mul (x+y) (x/(x+y))
  have hyid := Real.negMulLog_mul (x+y) (y/(x+y))
  rw [mul_div_cancel₀ _ hs] at hxid hyid
  have hratio : 1-x/(x+y) = y/(x+y) := by field_simp; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hratio, mul_add]
  unfold pairEntropy
  have hsum : x/(x+y) + y/(x+y) = 1 := by field_simp
  have hsum' := congrArg (fun t : ℝ => t * Real.negMulLog (x+y)) hsum
  nlinarith

theorem binary_probability_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x/(x+y) ∧ x/(x+y) ≤ 1 := by
  constructor
  · positivity
  · by_cases hs : x+y=0
    · simp [hs]
    · exact (div_le_one (lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs))).mpr (by linarith)

theorem mass_mul_min_probability {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x+y) * min (x/(x+y)) (1-x/(x+y)) = min x y := by
  by_cases hs : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    simp [hx0,hy0]
  have hsp : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
  have hratio : 1-x/(x+y)=y/(x+y) := by field_simp; ring
  rw [hratio]
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, min_eq_left ((div_le_div_iff_of_pos_right hsp).mpr hxy)]
    exact mul_div_cancel₀ _ hs
  · have hyx := le_of_not_ge hxy
    rw [min_eq_right hyx, min_eq_right ((div_le_div_iff_of_pos_right hsp).mpr hyx)]
    exact mul_div_cancel₀ _ hs

theorem pairEntropy_lower {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * min x y * Real.log 2 ≤ pairEntropy x y := by
  rw [pairEntropy_eq]
  have hp := binary_probability_bounds hx hy
  have hh := mul_le_mul_of_nonneg_left (two_min_le_binEntropy hp.1 hp.2) (add_nonneg hx hy)
  calc
    2 * min x y * Real.log 2 = (x+y) * (2 * min (x/(x+y)) (1-x/(x+y)) * Real.log 2) := by
      rw [← mass_mul_min_probability hx hy]
      ring
    _ ≤ _ := hh

theorem binary_entropy_sq_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ^ 2 ≤ 4 * min p (1-p) := by
  have hh := pow_le_pow_left₀ (Real.binEntropy_nonneg hp hp1)
    (binEntropy_le_two_sqrt_min hp hp1) 2
  have hm : 0 ≤ min p (1-p) := le_min hp (sub_nonneg.mpr hp1)
  nlinarith [Real.sq_sqrt hm]

theorem sum_pairEntropy_sq_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hmass : ∑ i, (x i+y i) = 1) :
    (∑ i, pairEntropy (x i) (y i)) ^ 2 ≤ 4 * ∑ i, min (x i) (y i) := by
  have hcs := weighted_sum_sq_le univ (fun i => x i+y i)
    (fun i => Real.binEntropy (x i/(x i+y i))) (fun i _ => add_nonneg (hx i) (hy i)) hmass
  simp_rw [← pairEntropy_eq] at hcs
  apply hcs.trans
  calc
    (∑ i, (x i+y i) * Real.binEntropy (x i/(x i+y i)) ^ 2) ≤
        ∑ i, (x i+y i) * (4 * min (x i/(x i+y i)) (1-x i/(x i+y i))) := by
      apply sum_le_sum
      intro i _
      have hp := binary_probability_bounds (hx i) (hy i)
      exact mul_le_mul_of_nonneg_left (binary_entropy_sq_bound hp.1 hp.2) (add_nonneg (hx i) (hy i))
    _ = 4 * ∑ i, min (x i) (y i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [← mass_mul_min_probability (hx i) (hy i)]
      ring

theorem sum_pairEntropy_lower {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (2 * ∑ i, min (x i) (y i)) * Real.log 2 ≤ ∑ i, pairEntropy (x i) (y i) := by
  have hh := sum_le_sum (fun i (_ : i ∈ univ) => pairEntropy_lower (hx i) (hy i))
  simpa only [← sum_mul, ← mul_sum] using hh

#print axioms binEntropy_le_two_sqrt_min
#print axioms two_min_le_binEntropy

end Erdos18c
