import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Multiset.Replicate
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic infrastructure for Erdős 18(c)

Arithmetic lemmas used by the complete proof in FinalBound.lean.

The definitions of subset sums and practicalH follow the Formal Conjectures
statement (Apache-2.0); the radix and carrying arguments are adapted from
Kohlmeyer--Kruer, "Short sums of factorial divisors and Erdős Problem 18(b)"
(16 September 2026), Sections 5--6, with explicit credit.
-/

open Finset

namespace Erdos18c

def subsetSums (D : Set ℕ) : Set ℕ :=
  {R | ∃ E : Finset ℕ, (↑E : Set ℕ) ⊆ D ∧ E.sum id = R}

noncomputable def practicalH (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).sup fun R =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ subsetSums (↑D : Set ℕ)}

def IsPractical (N : ℕ) : Prop :=
  ∀ R ≤ N, ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.sum id = R

def ShortSum (N R k : ℕ) : Prop :=
  ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.sum id = R ∧ D.card ≤ k

theorem shortSum_zero (N k : ℕ) : ShortSum N 0 k := by
  exact ⟨∅, by simp, by simp, by simp⟩

theorem shortSum_mono_count {N R k l : ℕ}
    (h : ShortSum N R k) (hkl : k ≤ l) : ShortSum N R l := by
  obtain ⟨D, hD, hsum, hcard⟩ := h
  exact ⟨D, hD, hsum, hcard.trans hkl⟩

theorem shortSum_mono_host {N M R k : ℕ}
    (hNM : N ∣ M) (hM : M ≠ 0) (h : ShortSum N R k) : ShortSum M R k := by
  obtain ⟨D, hD, hsum, hcard⟩ := h
  exact ⟨D, hD.trans (Nat.divisors_subset_of_dvd hM hNM), hsum, hcard⟩

theorem practicalH_le_of_shortSums (N k : ℕ)
    (h : ∀ R ∈ Finset.Icc 1 N, ShortSum N R k) : practicalH N ≤ k := by
  classical
  unfold practicalH
  apply Finset.sup_le
  intro R hR
  obtain ⟨D, hD, hsum, hcard⟩ := h R hR
  apply le_trans ?_ hcard
  apply Nat.sInf_le
  exact ⟨D, hD, rfl, D, Set.Subset.rfl, hsum⟩

theorem shortSum_of_practicalH {N R : ℕ}
    (hN : IsPractical N) (hR : R ≤ N) : ShortSum N R (practicalH N) := by
  classical
  by_cases hz : R = 0
  · subst R
    exact shortSum_zero _ _
  obtain ⟨A, hA, hAsum⟩ := hN R hR
  have hne : {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ subsetSums (↑D : Set ℕ)}.Nonempty :=
    ⟨A.card, A, hA, rfl, A, Set.Subset.rfl, hAsum⟩
  obtain ⟨D, hD, hcard, E, hED, hsum⟩ := Nat.sInf_mem hne
  have hsub : E ⊆ D := Finset.coe_subset.mp hED
  refine ⟨E, hsub.trans hD, hsum, ?_⟩
  calc
    E.card ≤ D.card := Finset.card_le_card hsub
    _ = sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ subsetSums (↑D : Set ℕ)} := hcard
    _ ≤ practicalH N := Finset.le_sup (f := fun R =>
      sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
        R ∈ subsetSums (↑D : Set ℕ)}) (Finset.mem_Icc.mpr ⟨by omega, hR⟩)

theorem shortSum_radix {M q a r k l : ℕ}
    (hM : 0 < M) (hq : 0 < q) (hrq : r < q)
    (ha : ShortSum M a k) (hr : ShortSum (q * M) r l) :
    ShortSum (q * M) (q * a + r) (k + l) := by
  classical
  obtain ⟨A, hA, hAsum, hAcard⟩ := ha
  obtain ⟨B, hB, hBsum, hBcard⟩ := hr
  have hinj : Function.Injective (fun d : ℕ => q * d) :=
    fun _ _ h => mul_left_cancel₀ (ne_of_gt hq) h
  have hdisj : Disjoint (A.image (fun d => q * d)) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors (hA hd)) hM
    have hlow : q ≤ q * d := by nlinarith
    have hhigh : q * d ≤ r := by
      rw [← hBsum]
      exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hxB
    omega
  refine ⟨A.image (fun d => q * d) ∪ B, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.mem_divisors.mpr
        ⟨mul_dvd_mul_left q (Nat.dvd_of_mem_divisors (hA hd)),
          ne_of_gt (Nat.mul_pos hq hM)⟩
    · exact hB hx
  · rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hinj h)]
    change (∑ x ∈ A, q * x) + B.sum id = q * a + r
    rw [← Finset.mul_sum, show (∑ x ∈ A, x) = a from hAsum, hBsum]
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective A hinj]
    omega

theorem practicalH_radix {M q l : ℕ}
    (hM : IsPractical M) (hMpos : 0 < M) (hq : 0 < q)
    (hlocal : ∀ r < q, ShortSum (q * M) r l) :
    practicalH (q * M) ≤ practicalH M + l := by
  apply practicalH_le_of_shortSums
  intro R hR
  have hquot : R / q ≤ M :=
    Nat.div_le_of_le_mul (Finset.mem_Icc.mp hR).2
  have hrep := shortSum_radix hMpos hq (Nat.mod_lt R hq)
    (shortSum_of_practicalH hM hquot) (hlocal (R % q) (Nat.mod_lt R hq))
  simpa only [Nat.div_add_mod] using hrep

theorem positive_quotient {R S q : ℕ}
    (hq : 0 < q) (hSR : S < R) (hdvd : q ∣ R - S) :
    ∃ t : ℕ, 0 < t ∧ R = S + q * t ∧ t ≤ R / q := by
  refine ⟨(R - S) / q, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hSR) hdvd) hq
  · rw [Nat.mul_div_cancel' hdvd]
    exact (Nat.add_sub_of_le hSR.le).symm
  · exact Nat.div_le_div_right (Nat.sub_le R S)

theorem factorial_power_dvd (m r : ℕ) :
    m.factorial ^ r ∣ (r * m).factorial := by
  simpa using Nat.prod_factorial_dvd_factorial_sum (Finset.range r) (fun _ => m)

theorem factorial_binary_reserve (m k : ℕ) :
    2 ^ k * m.factorial ∣ (m + 2 * k).factorial := by
  have hpow : 2 ^ k ∣ (2 * k).factorial := by
    simpa [Nat.factorial, Nat.mul_comm] using factorial_power_dvd 2 k
  exact (mul_dvd_mul hpow (dvd_refl m.factorial)).trans
    (by simpa [Nat.add_comm] using
      Nat.factorial_mul_factorial_dvd_factorial_add (2 * k) m)

theorem shifted_divisor_dvd_factorial {m k b d : ℕ}
    (hd : d ∣ m.factorial) (hb : b ≤ k) :
    2 ^ b * d ∣ (m + 2 * k).factorial :=
  (mul_dvd_mul (pow_dvd_pow 2 hb) hd).trans (factorial_binary_reserve m k)

theorem factorial_isPractical (n : ℕ) : IsPractical n.factorial := by
  induction n with
  | zero =>
    intro R hR
    simp only [Nat.factorial_zero] at hR
    have hcases : R = 0 ∨ R = 1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ n ih =>
    intro R hR
    let q := n + 1
    have hq : 0 < q := Nat.succ_pos n
    have hle : R / q ≤ n.factorial := by
      apply Nat.div_le_of_le_mul
      simpa [q, Nat.factorial_succ] using hR
    obtain ⟨A, hA, hAsum⟩ := ih (R / q) hle
    have hr : R % q < q := Nat.mod_lt R hq
    have hrepsum : ShortSum (q * n.factorial) (R % q) 1 := by
      by_cases hz : R % q = 0
      · simpa only [hz] using shortSum_zero (q * n.factorial) 1
      · refine ⟨{R % q}, ?_, by simp, by simp⟩
        intro d hd
        have hd' : d = R % q := Finset.mem_singleton.mp hd
        subst d
        exact Nat.mem_divisors.mpr ⟨
          (Nat.dvd_factorial (Nat.pos_of_ne_zero hz) (show R % q ≤ n + 1 from hr.le)),
          Nat.factorial_ne_zero (n + 1)⟩
    have hrep := shortSum_radix (Nat.factorial_pos n) hq hr
      (show ShortSum n.factorial (R / q) A.card from ⟨A,hA,hAsum,le_rfl⟩) hrepsum
    obtain ⟨D,hD,hDsum,_⟩ := hrep
    refine ⟨D, ?_, ?_⟩
    · simpa [q,Nat.factorial_succ] using hD
    · simpa only [Nat.div_add_mod] using hDsum

theorem distinctify_divisor_multiset (s : Multiset ℕ) {N : ℕ}
    (hN : N ≠ 0) (hs : ∀ d ∈ s, d ∣ N) :
    ShortSum (2 ^ s.card * N) s.sum s.card := by
  classical
  have aux : ∀ k : ℕ, ∀ t : Multiset ℕ, t.card = k →
      ∀ M : ℕ, M ≠ 0 → (∀ d ∈ t, d ∣ M) →
      ShortSum (2 ^ k * M) t.sum k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hk M hM ht
      by_cases hn : t.Nodup
      · refine ⟨t.toFinset, ?_, ?_, ?_⟩
        · intro d hd
          exact Nat.mem_divisors.mpr
            ⟨dvd_mul_of_dvd_right (ht d (Multiset.mem_toFinset.mp hd)) (2 ^ k),
             mul_ne_zero (pow_ne_zero _ (by decide)) hM⟩
        · change (t.toFinset.val.map id).sum = t.sum
          simp [hn.dedup]
        · exact le_of_eq ((Multiset.toFinset_card_of_nodup hn).trans hk)
      · rw [Multiset.nodup_iff_ne_cons_cons] at hn
        push Not at hn
        obtain ⟨a,u,rfl⟩ := hn
        have hc : (2 * a ::ₘ u).card < k := by
          simp only [Multiset.card_cons] at hk ⊢
          omega
        have hnew : ∀ d ∈ (2 * a ::ₘ u), d ∣ 2 * M := by
          intro d hd
          rcases Multiset.mem_cons.mp hd with rfl | hd
          · exact mul_dvd_mul_left 2 (ht a (by simp))
          · exact dvd_mul_of_dvd_right (ht d (by simp [hd])) 2
        have hrep := ih _ hc (2 * a ::ₘ u) rfl (2 * M)
          (mul_ne_zero (by decide) hM) hnew
        have hhost : 2 ^ (2 * a ::ₘ u).card * (2 * M) = 2 ^ k * M := by
          rw [← hk]
          simp only [Multiset.card_cons,pow_succ]
          ring
        have hsum : (2 * a ::ₘ u).sum = (a ::ₘ a ::ₘ u).sum := by
          simp [two_mul,add_assoc]
        have hrep' := shortSum_mono_count hrep hc.le
        simpa only [hhost,hsum] using hrep'
  exact aux s.card s rfl N hN hs

theorem distinctify_factorial_divisors (s : Multiset ℕ) (F : ℕ)
    (hs : ∀ d ∈ s, d ∣ F.factorial) :
    ShortSum (F + 2 * s.card).factorial s.sum s.card :=
  shortSum_mono_host (factorial_binary_reserve F s.card)
    (Nat.factorial_ne_zero _) (distinctify_divisor_multiset s (Nat.factorial_ne_zero F) hs)

theorem factorial_radix_recurrence {n m l : ℕ} (hmn : m ≤ n)
    (hlocal : ∀ r < n.factorial / m.factorial, ShortSum n.factorial r l) :
    practicalH n.factorial ≤ practicalH m.factorial + l := by
  have hdiv : m.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hmn
  have heq : n.factorial / m.factorial * m.factorial = n.factorial :=
    Nat.div_mul_cancel hdiv
  have hq : 0 < n.factorial / m.factorial :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) hdiv) (Nat.factorial_pos m)
  have h := practicalH_radix (factorial_isPractical m) (Nat.factorial_pos m) hq
    (by simpa only [heq] using hlocal)
  simpa only [heq] using h

#print axioms factorial_radix_recurrence
#print axioms distinctify_factorial_divisors

end Erdos18c
