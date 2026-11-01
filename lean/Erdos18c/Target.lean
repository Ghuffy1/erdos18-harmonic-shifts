import Erdos18c.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.NormNum

/-!
Target definitions and elementary implications from the quantitative bound.
The unconditional quantitative theorem is proved in FinalBound.lean.
-/

open Filter

namespace Erdos18c

def upstreamSubsetSums (D : Set ℕ) : Set ℕ :=
  {R | ∃ E : Finset ℕ, (↑E : Set ℕ) ⊆ D ∧ R = E.sum id}

theorem subsetSums_eq_upstream (D : Set ℕ) :
    subsetSums D = upstreamSubsetSums D := by
  ext R
  constructor
  · rintro ⟨E,hE,hEq⟩
    exact ⟨E,hE,hEq.symm⟩
  · rintro ⟨E,hE,hEq⟩
    exact ⟨E,hE,hEq.symm⟩

noncomputable def upstreamPracticalH (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).sup fun R =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ upstreamSubsetSums (↑D : Set ℕ)}

theorem practicalH_eq_upstream (N : ℕ) :
    practicalH N = upstreamPracticalH N := by
  simp only [practicalH,upstreamPracticalH,subsetSums_eq_upstream]

/-- Local transcription of `Nat.IsPractical` at the pinned upstream revision. -/
def upstreamIsPractical (N : ℕ) : Prop :=
  ∀ R, R ≤ N → R ∈ upstreamSubsetSums (↑N.divisors : Set ℕ)

theorem isPractical_iff_upstream (N : ℕ) :
    IsPractical N ↔ upstreamIsPractical N := by
  constructor
  · intro h R hR
    obtain ⟨D, hD, hsum⟩ := h R hR
    exact ⟨D, Finset.coe_subset.mpr hD, hsum.symm⟩
  · intro h R hR
    obtain ⟨D, hD, hsum⟩ := h R hR
    exact ⟨D, Finset.coe_subset.mp hD, hsum.symm⟩

def Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    (practicalH n.factorial : ℝ) < (Real.log (n : ℝ)) ^ C

def NinthPowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    (practicalH n.factorial : ℝ) ≤ C * (Real.log (n : ℝ)) ^ (9 : ℕ)

def StatementB : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε

def StatementA : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ᶠ m : ℕ in atTop,
    IsPractical m ∧ (practicalH m : ℝ) < (Real.log (Real.log (m : ℝ))) ^ C

/-- Elementary exponential growth of factorials, used only in the corollary. -/
theorem log_factorial_succ_lower (n : ℕ) :
    (n : ℝ) * Real.log 2 ≤ Real.log ((n + 1).factorial : ℝ) := by
  have hnat : 2 ^ n ≤ (n + 1).factorial := by
    simpa [Nat.add_comm] using (Nat.factorial_mul_pow_le_factorial (m := 1) (n := n))
  have hreal : (2 : ℝ) ^ n ≤ ((n + 1).factorial : ℝ) := by exact_mod_cast hnat
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n) hreal
  rwa [Real.log_pow] at h

theorem eventually_log_succ_le_four_loglog_factorial :
    ∀ᶠ n : ℕ in atTop, Real.log ((n + 1 : ℕ) : ℝ) ≤
      4 * Real.log (Real.log ((n + 1).factorial : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hlog.eventually_ge_atTop (max (Real.log 2) (-2 * Real.log (Real.log 2))),
    eventually_gt_atTop 0] with n hn hnpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hshift : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    linarith
  have hlogshift : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hshift
    rwa [Real.log_mul (by norm_num) hnreal.ne'] at hh
  have hfactor : Real.log (n : ℝ) + Real.log (Real.log 2) ≤
      Real.log (Real.log ((n + 1).factorial : ℝ)) := by
    have hh := Real.log_le_log (mul_pos hnreal ha) (log_factorial_succ_lower n)
    rwa [Real.log_mul hnreal.ne' ha.ne'] at hh
  have h1 := (le_max_left _ _).trans hn
  have h2 := (le_max_right _ _).trans hn
  linarith

/-- Part (a) is a consequence along the cofinal sequence of factorials.
This does not claim new priority for the previously known part (a). -/
theorem statementA_of_ninthPowerBound (h : NinthPowerBound) : StatementA := by
  obtain ⟨C, hC, hbound⟩ := h
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have hfac : Tendsto (fun n : ℕ => (n + 1).factorial) atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (Nat.self_le_factorial _)) tendsto_id
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log ((n + 1).factorial : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp hfac))
  have hgood : ∀ᶠ n : ℕ in atTop,
      IsPractical (n + 1).factorial ∧ (practicalH (n + 1).factorial : ℝ) <
        Real.log (Real.log ((n + 1).factorial : ℝ)) ^ (10 : ℝ) := by
    filter_upwards [hsucc.eventually hbound, eventually_log_succ_le_four_loglog_factorial,
      hloglog.eventually_gt_atTop (C * (4 : ℝ) ^ (9 : ℕ))] with n hn hcomp hlarge
    refine ⟨factorial_isPractical _, ?_⟩
    let y := Real.log (Real.log ((n + 1).factorial : ℝ))
    have hy : 0 < y := lt_trans (by positivity) hlarge
    have hleft : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.succ_pos n))
    have hpow := pow_le_pow_left₀ hleft hcomp 9
    have hcost : (practicalH (n + 1).factorial : ℝ) ≤ C * (4 * y) ^ (9 : ℕ) :=
      hn.trans (mul_le_mul_of_nonneg_left hpow hC.le)
    have hstrict : (C * (4 : ℝ) ^ (9 : ℕ)) * y ^ (9 : ℕ) < y * y ^ (9 : ℕ) :=
      mul_lt_mul_of_pos_right hlarge (pow_pos hy _)
    have hrewrite : C * (4 * y) ^ (9 : ℕ) =
        (C * (4 : ℝ) ^ (9 : ℕ)) * y ^ (9 : ℕ) := by ring
    rw [hrewrite] at hcost
    have hresult := hcost.trans_lt hstrict
    have hconvert : y ^ (10 : ℝ) = y ^ (10 : ℕ) := Real.rpow_natCast _ _
    change _ < y ^ (10 : ℝ)
    rw [hconvert]
    convert hresult using 1
    ring
  refine ⟨10, by norm_num, frequently_atTop.mpr ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  intro a
  refine ⟨(max a N + 1).factorial, ?_, hN _ (le_max_right _ _)⟩
  exact (le_max_left _ _).trans ((Nat.le_succ _).trans (Nat.self_le_factorial _))

/-- The already-known part (b) follows from the proposed stronger bound.
This implication is applied to the unconditional theorem in FinalBound.lean. -/
theorem statementB_of_ninthPowerBound (h : NinthPowerBound) : StatementB := by
  obtain ⟨C, hC, hbound⟩ := h
  intro ε hε
  have hlittle := (isLittleO_log_rpow_rpow_atTop (9 : ℝ) hε).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hlittle.def (show 0 < 1 / (2 * C) by positivity)
  filter_upwards [hbound, hsmall, eventually_gt_atTop 0] with n hn hnorm hnpos
  have hbase : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpow : (0 : ℝ) < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hbase _
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast hnpos)
  have hlogpow : (0 : ℝ) ≤ Real.log (n : ℝ) ^ (9 : ℝ) := Real.rpow_nonneg hlog0 _
  simp only [Function.comp_apply] at hnorm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogpow,
    abs_of_pos hpow] at hnorm
  have hconvert : Real.log (n : ℝ) ^ (9 : ℝ) = Real.log (n : ℝ) ^ (9 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hconvert] at hnorm
  have hhalf : C * (Real.log (n : ℝ)) ^ (9 : ℕ) ≤ (n : ℝ) ^ ε / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hnorm hC.le
    convert hmul using 1
    field_simp
  exact hn.trans_lt (hhalf.trans_lt (by linarith))

theorem statement_of_ninthPowerBound (h : NinthPowerBound) : Statement := by
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨10, by norm_num, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hbound, hlog.eventually_gt_atTop (max C 0)] with n hn hlarge
  have hClog : C < Real.log (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hlarge
  have hpositive : 0 < Real.log (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hlarge
  have hstrict : C * Real.log (n : ℝ) ^ (9 : ℕ) <
      Real.log (n : ℝ) * Real.log (n : ℝ) ^ (9 : ℕ) :=
    mul_lt_mul_of_pos_right hClog (pow_pos hpositive _)
  have hresult := lt_of_le_of_lt hn hstrict
  have hpow : Real.log (n : ℝ) ^ (10 : ℝ) = Real.log (n : ℝ) ^ (10 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hpow]
  convert hresult using 1
  ring

/-- All three original conclusions; the middle entry is the already-known (b). -/
def FullStatement : Prop := StatementA ∧ StatementB ∧ Statement

/-- Logical synthesis, applied to the unconditional bound in FinalBound.lean. -/
theorem fullStatement_of_ninthPowerBound (h : NinthPowerBound) : FullStatement :=
  ⟨statementA_of_ninthPowerBound h, statementB_of_ninthPowerBound h,
    statement_of_ninthPowerBound h⟩

#print axioms statement_of_ninthPowerBound
#print axioms practicalH_eq_upstream
#print axioms statementB_of_ninthPowerBound
#print axioms statementA_of_ninthPowerBound
#print axioms fullStatement_of_ninthPowerBound
#print axioms isPractical_iff_upstream

end Erdos18c
