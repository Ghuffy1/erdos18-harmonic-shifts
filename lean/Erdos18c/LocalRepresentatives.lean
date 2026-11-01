import Erdos18c.DigitInput

open Finset Filter
namespace Erdos18c
noncomputable section

theorem finite_pushforward_support {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (T : ι → κ) (x : κ) (hx : finitePushforward p T x≠0) :
    ∃ a,T a=x ∧ p a≠0 := by
  obtain ⟨a,ha,hpa⟩ := exists_ne_zero_of_sum_ne_zero hx
  exact ⟨a,(mem_filter.mp ha).2,hpa⟩

theorem dyadicIndex_add (k a b : ℕ) :
    dyadicIndex k (a+b) = dyadicIndex k a + dyadicIndex k b := by
  apply Fin.ext
  exact Nat.add_mod _ _ _

theorem dyadicIndex_scale (k a b : ℕ) :
    dyadicIndex k (2^a*b) = dyadicMultiplier k a (dyadicIndex k b) := by
  apply Fin.ext
  change (2^a*b)%2^k = (2^a*(b%2^k))%2^k
  simp [Nat.mul_mod]

theorem positiveDigitValue_repr {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (z : A × Fin 2) :
    0<positiveDigitValue A z ∧ positiveDigitValue A z≤2^k ∧
      HasFactorialDivisorMultiset (F+2*k) (positiveDigitValue A z) (u+1) := by
  have hu := hA.representatives z.1.val z.1.property
  have hub := hA.bounded z.1.val z.1.property
  have huo : 0<z.1.val := by
    obtain ⟨t,ht⟩ := hA.odd z.1.val z.1.property
    omega
  have he := z.2.isLt
  refine ⟨by dsimp [positiveDigitValue]; omega,by dsimp [positiveDigitValue]; omega,?_⟩
  by_cases hz : z.2.val=0
  · have heq : positiveDigitValue A z=z.1.val := by dsimp [positiveDigitValue]; omega
    rw [heq]
    exact factorial_multiset_mono hu le_rfl (by omega)
  · have hz1 : z.2.val=1 := by omega
    have heq : positiveDigitValue A z=z.1.val+1 := by dsimp [positiveDigitValue]; omega
    rw [heq]
    exact factorial_multiset_add hu (factorial_multiset_singleton (one_dvd _))

theorem positiveDigit_support_repr {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (x : Fin (2^k))
    (hx : positiveDigitProjection A k x≠0) :
    ∃ V,0<V ∧ V≤2^k ∧ dyadicIndex k V=x ∧
      HasFactorialDivisorMultiset (F+2*k) V (u+1) := by
  obtain ⟨z,hz,_⟩ := finite_pushforward_support (positiveDigitWeight A)
    (fun z => dyadicIndex k (positiveDigitValue A z)) x hx
  obtain ⟨hp,hbound,hr⟩ := positiveDigitValue_repr hA z
  exact ⟨positiveDigitValue A z,hp,hbound,hz,hr⟩

theorem factorial_multiset_shift {F k a R u : ℕ} (ha : a≤k)
    (h : HasFactorialDivisorMultiset F R u) :
    HasFactorialDivisorMultiset (F+2*k) (2^a*R) u := by
  obtain ⟨s,hs,hsum,hcard⟩ := h
  refine ⟨s.map (fun d => 2^a*d),?_,?_,?_⟩
  · intro x hx
    obtain ⟨d,hd,rfl⟩ := Multiset.mem_map.mp hx
    exact shifted_divisor_dvd_factorial (hs d hd) ha
  · simpa [hsum] using Multiset.sum_map_mul_left (s:=s) (a:=2^a) (f:=id)
  · simpa using hcard

theorem harmonic_support_repr {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (x : Fin (2^k))
    (hx : harmonicLaw k (positiveDigitProjection A k) x≠0) :
    ∃ V,0<V ∧ dyadicIndex k V=x ∧ HasFactorialDivisorMultiset (F+4*k) V (u+1) := by
  change (∑ a : Fin k, harmonicWeight k a.val * dyadicDilate k a.val (positiveDigitProjection A k) x)≠0 at hx
  obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
  have hda : dyadicDilate k a.val (positiveDigitProjection A k) x≠0 := (mul_ne_zero_iff.mp ha).2
  obtain ⟨y,hy,hyp⟩ := finite_pushforward_support (positiveDigitProjection A k) (dyadicMultiplier k a.val) x hda
  obtain ⟨V,hV,_,heq,hrep⟩ := positiveDigit_support_repr hA y hyp
  refine ⟨2^a.val*V,by positivity,?_,?_⟩
  · rw [dyadicIndex_scale,heq]
    exact hy
  · have hh := factorial_multiset_shift (Nat.le_of_lt a.isLt) hrep
    convert hh using 1; omega

theorem convolutionPow_actual_repr {k F u : ℕ} (f : Fin (2^k) → ℝ)
    (hrep : ∀ x, f x≠0 → ∃ V,0<V ∧ dyadicIndex k V=x ∧ HasFactorialDivisorMultiset F V u)
    (r : ℕ) (x : Fin (2^k)) (hx : realConvolutionPow f r x≠0) :
    ∃ S, dyadicIndex k S=x ∧ HasFactorialDivisorMultiset F S (r*u) ∧ (0<r → 0<S) := by
  induction r generalizing x with
  | zero =>
    have hx0 : x=0 := by by_contra h; simp [realConvolutionPow,h] at hx
    subst x
    exact ⟨0,by simp [dyadicIndex],factorial_multiset_zero _ _,by omega⟩
  | succ r ih =>
    change (∑ a : Fin (2^k), f a * realConvolutionPow f r (x-a))≠0 at hx
    obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
    obtain ⟨V,hV,heV,hVrep⟩ := hrep a (mul_ne_zero_iff.mp ha).1
    obtain ⟨S,heS,hSrep,_⟩ := ih (x-a) (mul_ne_zero_iff.mp ha).2
    refine ⟨V+S,?_,?_,by omega⟩
    · rw [dyadicIndex_add,heV,heS]
      abel
    · simpa only [Nat.succ_mul,Nat.add_comm] using factorial_multiset_add hVrep hSrep

theorem modular_representatives_of_profile {F k u r : ℕ} {c : ℝ} {A : Finset ℕ}
    (hk : 0<k) (hA : BinaryBlockProfile F k k u c A) (hc0 : 0≤c) (hc : c≤2)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*((c/2)^2*(Real.log 2)^2/2)/harmonicSum k)
    (R : ℕ) :
    ∃ S,0<S ∧ dyadicIndex k S=dyadicIndex k R ∧
      HasFactorialDivisorMultiset (F+4*k) S (2*r*(u+1)) := by
  have hp := positiveDigitProjection_probability A hA.nonempty k
  have hpre := positiveDigit_entropy_prefix hA hc
  obtain ⟨a,ha,b,hb,heq⟩ := harmonicLaw_covers k r hk (positiveDigitProjection A k)
    hp.1 hp.2 (c/2) (by linarith) hpre hr (dyadicIndex k R)
  have hrepr := harmonic_support_repr hA
  obtain ⟨V,hV,hVrep,hVpos⟩ := convolutionPow_actual_repr _ hrepr r a (by simpa [finiteSupport] using ha)
  obtain ⟨W,hW,hWrep,_⟩ := convolutionPow_actual_repr _ hrepr r b (by simpa [finiteSupport] using hb)
  have hrpos : 0<r := by
    by_contra hn
    have hz : r=0 := by omega
    have hlog : 0<Real.log (2*(k:ℝ)) := Real.log_pos (by
      have hkR : (1:ℝ)≤k := by exact_mod_cast hk
      linarith)
    simp only [hz,Nat.cast_zero,zero_mul,zero_div] at hr
    linarith
  refine ⟨V+W,by have := hVpos hrpos; omega,?_,?_⟩
  · rw [dyadicIndex_add,hV,hW]
    exact heq
  · have hh := factorial_multiset_add hVrep hWrep
    convert hh using 1; ring

#print axioms modular_representatives_of_profile
end
end Erdos18c
