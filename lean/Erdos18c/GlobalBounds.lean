import Erdos18c.LocalShortSums

/-!
The factorial-quotient estimates and potential induction are adapted from
Kohlmeyer--Kruer, Erdos18b.lean, source SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088,
lines 610--631 and 729--747. The logarithmic width and potential are new here.
-/
open Finset Filter
open scoped Topology
namespace Erdos18c
noncomputable section

theorem binaryLength_mono {a b : ℕ} (h : a≤b) : binaryLength a≤binaryLength b :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem binaryLength_le_of_le_pow {R w : ℕ} (h : R≤2^w) : binaryLength R≤w+1 := by
  have hh := Nat.log_mono_right h (b:=2)
  rw [Nat.log_pow (by norm_num : 1<2)] at hh
  exact Nat.add_le_add_right hh 1

theorem binaryLength_pow_le (n w : ℕ) : binaryLength (n^w)≤w*binaryLength n+1 := by
  apply binaryLength_le_of_le_pow
  calc
    n^w ≤ (2^binaryLength n)^w :=
      Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num : 1<2) n).le w
    _ = 2^(w*binaryLength n) := by rw [←pow_mul,Nat.mul_comm]

theorem factorial_quotient_le_pow {n w : ℕ} (hw : w≤n) :
    n.factorial/(n-w).factorial≤n^w := by
  rw [←Nat.descFactorial_eq_div hw]
  exact Nat.descFactorial_le_pow n w

theorem binaryLength_factorial_quotient_le {n w : ℕ} (hw : w≤n) :
    binaryLength (n.factorial/(n-w).factorial)≤w*binaryLength n+1 :=
  (binaryLength_mono (factorial_quotient_le_pow hw)).trans (binaryLength_pow_le n w)

def logarithmicWidth (n : ℕ) : ℕ := n/(64*binaryLength n)

theorem eventually_logarithmicWidth_bounds : ∀ᶠ n : ℕ in atTop,
    12≤n ∧ 1≤logarithmicWidth n ∧ 2*logarithmicWidth n≤n ∧
    6*(logarithmicWidth n*binaryLength n+1)≤n ∧
    (n:ℝ)/(512*Real.log (n:ℝ))≤logarithmicWidth n := by
  have hlittle := Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hratio : Tendsto (fun n : ℕ => 256*Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using
      hlittle.tendsto_div_nhds_zero.const_mul (256:ℝ)
  filter_upwards [eventually_ge_atTop 12,(tendsto_order.1 hratio).2 1 (by norm_num)] with n hn hr
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlogp : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hsmall : 256*Real.log (n:ℝ)≤n := ((div_lt_one hnp).mp hr).le
  have hbl := binaryLength_log_upper n (by omega)
  have hdR : (64*binaryLength n:ℕ)≤n := by
    have hh : 64*(binaryLength n:ℝ)≤n := by linarith
    exact_mod_cast hh
  have hd : 0<64*binaryLength n := by have := binaryLength_pos n; omega
  have hw : 1≤logarithmicWidth n := Nat.div_pos hdR hd
  have hprod : 64*binaryLength n*logarithmicWidth n≤n := Nat.mul_div_le n (64*binaryLength n)
  have hbpos : 1≤binaryLength n := binaryLength_pos n
  have htwo : 2*logarithmicWidth n≤n := by
    have hh := Nat.mul_le_mul_right (logarithmicWidth n) hbpos
    nlinarith
  have hhost : 6*(logarithmicWidth n*binaryLength n+1)≤n := by nlinarith
  have hmod := Nat.mod_lt n hd
  have hnlt : n<64*binaryLength n*(logarithmicWidth n+1) := by
    calc
      n = n%(64*binaryLength n)+(64*binaryLength n)*logarithmicWidth n :=
        (Nat.mod_add_div n (64*binaryLength n)).symm
      _ < (64*binaryLength n)+(64*binaryLength n)*logarithmicWidth n :=
        Nat.add_lt_add_right hmod _
      _ = _ := by ring
  have hnltR : (n:ℝ)<64*(binaryLength n:ℝ)*((logarithmicWidth n:ℝ)+1) := by exact_mod_cast hnlt
  have hwR : (1:ℝ)≤logarithmicWidth n := by exact_mod_cast hw
  have hbR : (0:ℝ)≤binaryLength n := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hbl (Nat.cast_nonneg (α:=ℝ) (logarithmicWidth n))
  have hwidth : (n:ℝ)/(512*Real.log (n:ℝ))≤logarithmicWidth n := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<512*Real.log (n:ℝ))).mpr
    nlinarith
  exact ⟨hn,hw,htwo,hhost,hwidth⟩

def globalPotential (C : ℝ) (n : ℕ) : ℝ := 512*(C+1)*Real.log (n:ℝ)^9

theorem globalPotential_nonneg {C : ℝ} (hC : 0≤C) (n : ℕ) : 0≤globalPotential C n := by
  by_cases hn : n=0
  · simp [hn,globalPotential]
  · unfold globalPotential
    have hh : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
    positivity

theorem globalPotential_step {C : ℝ} (hC : 0≤C) {n m w : ℕ}
    (hn : 2≤n) (hm : 1≤m) (heq : m+w=n)
    (hw : (n:ℝ)/(512*Real.log (n:ℝ))≤w) :
    (C+1)*Real.log (n:ℝ)^7≤globalPotential C n-globalPotential C m := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlogp : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hmn : (m:ℝ)≤n := by exact_mod_cast (show m≤n by omega)
  have hgap : (n:ℝ)-(m:ℝ)=w := by
    have hh : (m:ℝ)+(w:ℝ)=n := by exact_mod_cast heq
    linarith
  have hp := log_pow_gap_lower (show (1:ℝ)≤m by exact_mod_cast hm) hmn 8
  calc
    (C+1)*Real.log (n:ℝ)^7 = 512*(C+1)*
        (((n:ℝ)/(512*Real.log (n:ℝ)))/(n:ℝ)*Real.log (n:ℝ)^8) := by field_simp
    _ ≤ 512*(C+1)*((w:ℝ)/(n:ℝ)*Real.log (n:ℝ)^8) := by gcongr
    _ = 512*(C+1)*(((n:ℝ)-(m:ℝ))/(n:ℝ)*Real.log (n:ℝ)^8) := by rw [hgap]
    _ ≤ 512*(C+1)*(Real.log (n:ℝ)^9-Real.log (m:ℝ)^9) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by unfold globalPotential; ring

theorem bounded_of_eventual_potential_decrease (f P : ℕ→ℝ)
    (hP : ∀ n,0≤P n)
    (hstep : ∀ᶠ n : ℕ in atTop, ∃ m<n, f n≤f m+P n-P m) :
    ∃ K : ℝ,0≤K ∧ ∀ n,f n≤K+P n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hstep
  let K : ℝ := ∑ i∈range N,max 0 (f i)
  refine ⟨K,sum_nonneg (fun _ _ => le_max_left _ _),?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<N
    · have hf : f n≤K := (le_max_right 0 (f n)).trans
        (single_le_sum (f:=fun i => max 0 (f i)) (fun _ _ => le_max_left _ _) (mem_range.mpr hn))
      linarith [hP n]
    · obtain ⟨m,hm,hfm⟩ := hN n (by omega)
      linarith [ih m hm]

#print axioms eventually_logarithmicWidth_bounds
#print axioms globalPotential_step
end
end Erdos18c
