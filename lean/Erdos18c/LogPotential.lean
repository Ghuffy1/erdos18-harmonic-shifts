import Erdos18c.LiftingScale

open Finset Filter
namespace Erdos18c
noncomputable section

theorem log_gap_lower {x y : ℝ} (hy : 0<y) (hxy : y≤x) :
    (x-y)/x ≤ Real.log x-Real.log y := by
  have hx : 0<x := hy.trans_le hxy
  have hh := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hh
  have he : (x-y)/x = 1-y/x := by field_simp
  rw [he]
  linarith

theorem pow_gap_lower {a b : ℝ} (hb : 0≤b) (hba : b≤a) (p : ℕ) :
    (a-b)*a^p ≤ a^(p+1)-b^(p+1) := by
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hba p) hb
  rw [pow_succ,pow_succ]
  nlinarith

theorem log_pow_gap_lower {x y : ℝ} (hy : 1≤y) (hxy : y≤x) (p : ℕ) :
    ((x-y)/x)*Real.log x^p ≤ Real.log x^(p+1)-Real.log y^(p+1) := by
  have hyp : 0<y := lt_of_lt_of_le (by norm_num) hy
  have hlogy : 0≤Real.log y := Real.log_nonneg hy
  have hlogs := Real.log_le_log hyp hxy
  have hlogx : 0≤Real.log x := hlogy.trans hlogs
  exact (mul_le_mul_of_nonneg_right (log_gap_lower hyp hxy) (pow_nonneg hlogx p)).trans
    (pow_gap_lower hlogy hlogs p)

def localPotential (T : ℕ) : ℝ := 52428800000 * Real.log (T:ℝ)^7

theorem localPotential_step {T Q k : ℕ} (hT : 4≤T) (hQ : 1≤Q)
    (hgap : Q+k≤T)
    (hk : (T:ℝ)/(131072*Real.log (T:ℝ))≤k) :
    400000*Real.log (T:ℝ)^5 ≤ localPotential T-localPotential Q := by
  have hTp : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hlogp : 0<Real.log (T:ℝ) := Real.log_pos (by exact_mod_cast (show 1<T by omega))
  have hQreal : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hQT : (Q:ℝ)≤T := by exact_mod_cast (show Q≤T by omega)
  have hgapR : (k:ℝ)≤(T:ℝ)-(Q:ℝ) := by
    have hs : (Q:ℝ)+(k:ℝ)≤T := by exact_mod_cast hgap
    linarith
  have hp := log_pow_gap_lower hQreal hQT 6
  calc
    400000*Real.log (T:ℝ)^5 =
        52428800000 * (((T:ℝ)/(131072*Real.log (T:ℝ)))/(T:ℝ)*Real.log (T:ℝ)^6) := by
          field_simp
          ring
    _ ≤ 52428800000 * ((k:ℝ)/(T:ℝ)*Real.log (T:ℝ)^6) := by gcongr
    _ ≤ 52428800000 * (((T:ℝ)-(Q:ℝ))/(T:ℝ)*Real.log (T:ℝ)^6) := by gcongr
    _ ≤ 52428800000 * (Real.log (T:ℝ)^7-Real.log (Q:ℝ)^7) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by unfold localPotential; ring

theorem binaryLength_quotient {R Q k : ℕ} (hQ : Q≤R/2^k) (hk : k≤Nat.log 2 R) :
    binaryLength Q+k≤binaryLength R := by
  have hh := Nat.log_mono_right (b:=2) hQ
  rw [Nat.log_div_base_pow] at hh
  unfold binaryLength
  omega

theorem log_integer_lower_by_bits {R : ℕ} (hR : 0<R) :
    ((binaryLength R:ℝ)-1)*Real.log 2 ≤ Real.log (R:ℝ) := by
  have hp : (2:ℝ)^(Nat.log 2 R) ≤ (R:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : R≠0)
  have hh := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 R)) hp
  rw [Real.log_pow] at hh
  simpa [binaryLength] using hh

theorem representative_lt_target {R S : ℕ} (hR : 0<R) (_hS : 0<S)
    (hT : 4≤binaryLength R) (hheight : Real.log (S:ℝ)≤(binaryLength R:ℝ)/16) : S<R := by
  have hRlog := log_integer_lower_by_bits hR
  have hhalf : (1/2:ℝ)≤Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have hTreal : (4:ℝ)≤binaryLength R := by exact_mod_cast hT
  have hlogstrict : Real.log (S:ℝ)<Real.log (R:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show (0:ℝ)≤(binaryLength R:ℝ)-1 by linarith)]
  by_contra h
  have hRS : (R:ℝ)≤S := by exact_mod_cast (le_of_not_gt h)
  have hh := Real.log_le_log (by exact_mod_cast hR) hRS
  linarith

#print axioms localPotential_step
end
end Erdos18c
