import Erdos18c.LogPotential

open Finset Filter
namespace Erdos18c
noncomputable section

theorem factorial_multiset_ones (F R : ℕ) : HasFactorialDivisorMultiset F R R := by
  refine ⟨Multiset.replicate R 1, ?_, ?_, ?_⟩
  · intro d hd
    have hd1 : d=1 := (Multiset.mem_replicate.mp hd).2
    subst d
    exact one_dvd _
  · simp
  · simp

theorem localPotential_nonneg (T : ℕ) (hT : 1≤T) : 0≤localPotential T := by
  unfold localPotential
  exact mul_nonneg (by norm_num) (pow_nonneg (Real.log_nonneg (by exact_mod_cast hT)) _)

/-- Exact integer lifting of the harmonic modular representatives. -/
theorem integer_multiset_lifting : ∃ K : ℝ, 0≤K ∧ ∀ R : ℕ, 0<R →
    ∃ u : ℕ, HasFactorialDivisorMultiset (4*binaryLength R) R u ∧
      (u:ℝ)≤K+localPotential (binaryLength R) := by
  have hall := eventually_liftingScale_bounds.and
    (liftingScale_tendsto.eventually eventually_local_representatives)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hall
  refine ⟨(2^N:ℕ),by positivity,?_⟩
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
    intro hR
    let T := binaryLength R
    by_cases hTN : T<N
    · refine ⟨R,factorial_multiset_ones (4*T) R,?_⟩
      have hpow : R<2^T := Nat.lt_pow_succ_log_self (by norm_num) R
      have hRN : R≤2^N := hpow.le.trans (Nat.pow_le_pow_right (by norm_num) hTN.le)
      have hcast : (R:ℝ)≤(2^N:ℕ) := by exact_mod_cast hRN
      exact hcast.trans (le_add_of_nonneg_right (localPotential_nonneg T (binaryLength_pos R)))
    · obtain ⟨hb,hr⟩ := hN T (by omega)
      obtain ⟨hT,hk,h2k,hkl,hku,hhost,hcount,hheight⟩ := hb
      let k := liftingScale T
      obtain ⟨S,hSpos,hmod,hS⟩ := hr R
      have hSheight : Real.log (S:ℝ)≤(T:ℝ)/16 := by
        have hsmax : S≤localHeight k := factorial_multiset_height hS
        exact (Real.log_le_log (by exact_mod_cast hSpos) (by exact_mod_cast hsmax)).trans hheight
      have hSR : S<R := representative_lt_target hR hSpos hT hSheight
      have hcong : Nat.ModEq (2^k) S R := congrArg Fin.val hmod
      obtain ⟨Q,hQ,heq,hQquot⟩ := positive_quotient (by positivity : 0<2^k) hSR hcong.dvd'
      have hQR : Q<R := by
        have hqle : Q≤2^k*Q := by nlinarith [show 1≤2^k from one_le_pow₀ (by norm_num)]
        omega
      have hklog : k≤Nat.log 2 R := by
        change 2*k≤T at h2k
        have hTb : T=Nat.log 2 R+1 := rfl
        change 1≤k at hk
        omega
      have hbits : binaryLength Q+k≤T := binaryLength_quotient hQquot hklog
      obtain ⟨u,hu,hucount⟩ := ih Q hQR hQ
      have hshift : HasFactorialDivisorMultiset (4*binaryLength Q+2*k) (2^k*Q) u :=
        factorial_multiset_shift (le_refl k) hu
      have hshift' : HasFactorialDivisorMultiset (4*T) (2^k*Q) u :=
        factorial_multiset_mono hshift (by omega) le_rfl
      have hS' : HasFactorialDivisorMultiset (4*T) S (localCount k) :=
        factorial_multiset_mono (F:=localHost k) hS (by change localHost k≤T at hhost; omega) le_rfl
      have hadd := factorial_multiset_add hS' hshift'
      rw [←heq] at hadd
      refine ⟨localCount k+u,hadd,?_⟩
      have hstep := localPotential_step hT (binaryLength_pos Q) hbits hkl
      rw [Nat.cast_add]
      change (localCount k:ℝ)+(u:ℝ)≤((2^N:ℕ):ℝ)+localPotential T
      change (localCount k:ℝ)≤400000*Real.log (T:ℝ)^5 at hcount
      linarith

#print axioms integer_multiset_lifting
end
end Erdos18c
