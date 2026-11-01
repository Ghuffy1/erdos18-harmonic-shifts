import Erdos18c.GlobalBounds
import Erdos18c.Target

open Finset Filter
open scoped Topology
namespace Erdos18c
noncomputable section

theorem shortSum_singleton_factorial {n r : ℕ} (hr : 0<r) (hrn : r≤n) :
    ShortSum n.factorial r 1 := by
  refine ⟨{r},?_,by simp,by simp⟩
  intro d hd
  have hd' : d=r := mem_singleton.mp hd
  subst d
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hr hrn,Nat.factorial_ne_zero _⟩

theorem eventually_factorial_recurrence : ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
    ∃ m<n, (practicalH n.factorial:ℝ)≤(practicalH m.factorial:ℝ)+
      globalPotential C n-globalPotential C m := by
  obtain ⟨C,hC,N,hlocal⟩ := local_short_sums
  let D : ℝ := C+1
  have hD : 0<D := by dsimp [D]; linarith
  have hD1 : 1≤D := by dsimp [D]; linarith
  refine ⟨D,hD,?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_logarithmicWidth_bounds,eventually_ge_atTop (2^N),
    hlog.eventually_ge_atTop 1] with n hn hlarge hlogn
  obtain ⟨hn12,hw1,hw2,hhost,hwidth⟩ := hn
  let w := logarithmicWidth n
  let m := n-w
  let l := ⌈D*Real.log (n:ℝ)^7⌉₊
  have hmn : m≤n := Nat.sub_le _ _
  have hmlt : m<n := by dsimp [m,w]; omega
  have hmpos : 1≤m := by dsimp [m,w]; omega
  have hpow1 : 1≤Real.log (n:ℝ)^7 := one_le_pow₀ hlogn
  have hceil : D*Real.log (n:ℝ)^7≤(l:ℝ) := Nat.le_ceil _
  have hl1 : 1≤l := by
    have hh : (1:ℝ)≤l := by nlinarith
    exact_mod_cast hh
  have hrem : ∀ r<n.factorial/m.factorial,ShortSum n.factorial r l := by
    intro r hr
    by_cases hr0 : r=0
    · subst r
      exact shortSum_zero _ _
    have hrpos : 0<r := Nat.pos_of_ne_zero hr0
    by_cases hsmall : binaryLength r<N
    · have hrpow : r<2^binaryLength r := Nat.lt_pow_succ_log_self (by norm_num) r
      have hrn : r≤n := (hrpow.le.trans (Nat.pow_le_pow_right (by norm_num) hsmall.le)).trans hlarge
      exact shortSum_mono_count (shortSum_singleton_factorial hrpos hrn) hl1
    · obtain ⟨u,hu,huc⟩ := hlocal r hrpos (by omega)
      have hbits : binaryLength r≤w*binaryLength n+1 :=
        (binaryLength_mono hr.le).trans (binaryLength_factorial_quotient_le (by dsimp [w]; omega))
      have hhostr : 6*binaryLength r≤n := by dsimp [w] at hbits; omega
      have hlogr : Real.log (binaryLength r:ℝ)≤Real.log (n:ℝ) :=
        Real.log_le_log (by exact_mod_cast binaryLength_pos r) (by exact_mod_cast (show binaryLength r≤n by omega))
      have hlogr0 : 0≤Real.log (binaryLength r:ℝ) :=
        Real.log_nonneg (by exact_mod_cast binaryLength_pos r)
      have hClt : C≤D := by dsimp [D]; linarith
      have hcost : (u:ℝ)≤D*Real.log (n:ℝ)^7 := huc.trans (by gcongr)
      have hul : u≤l := by exact_mod_cast hcost.trans hceil
      exact shortSum_mono_count (shortSum_mono_host (Nat.factorial_dvd_factorial hhostr)
        (Nat.factorial_ne_zero _) hu) hul
  have hrec := factorial_radix_recurrence hmn hrem
  have hrecR : (practicalH n.factorial:ℝ)≤(practicalH m.factorial:ℝ)+(l:ℝ) := by exact_mod_cast hrec
  have hceilUpper : (l:ℝ)≤(D+1)*Real.log (n:ℝ)^7 := by
    have hh := (Nat.ceil_lt_add_one (show 0≤D*Real.log (n:ℝ)^7 by positivity)).le
    change (⌈D*Real.log (n:ℝ)^7⌉₊:ℝ)≤_ 
    nlinarith
  have hp := globalPotential_step hD.le (show 2≤n by omega) hmpos
    (show m+w=n from Nat.sub_add_cancel (by dsimp [w]; omega)) hwidth
  exact ⟨m,hmlt,by linarith⟩

/-- The quantitative bound, with no target theorem or analytic hypothesis assumed. -/
theorem ninthPowerBound : NinthPowerBound := by
  obtain ⟨C,hC,hrec⟩ := eventually_factorial_recurrence
  obtain ⟨K,hK,hbound⟩ := bounded_of_eventual_potential_decrease
    (fun n => (practicalH n.factorial:ℝ)) (globalPotential C) (globalPotential_nonneg hC.le) hrec
  refine ⟨K+512*(C+1),by positivity,?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  have hp : 1≤Real.log (n:ℝ)^9 := one_le_pow₀ hn
  have hh := hbound n
  unfold globalPotential at hh
  nlinarith [mul_le_mul_of_nonneg_left hp hK]

theorem erdos_18c : Statement := statement_of_ninthPowerBound ninthPowerBound
theorem erdos_18b : StatementB := statementB_of_ninthPowerBound ninthPowerBound
theorem erdos_18a : StatementA := statementA_of_ninthPowerBound ninthPowerBound
theorem erdos_18_full : FullStatement := fullStatement_of_ninthPowerBound ninthPowerBound

#print axioms ninthPowerBound
#print axioms erdos_18c
#print axioms erdos_18b
#print axioms erdos_18a
#print axioms erdos_18_full
end
end Erdos18c
