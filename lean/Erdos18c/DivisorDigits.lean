import Erdos18c.DivisorRepresentations
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds

/-!
Factorial digits and disjoint binary blocks adapted from Kohlmeyer--Kruer,
Erdos18b.lean, SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088.
The original source proves (b). The linear-host quantitative count needed
for (c) is supplied separately in this development.
-/
open Finset Filter
namespace Erdos18c
def shortFactorialDigits (F l : ℕ) : Finset ℕ :=
  insert 0 (F.factorial.divisors.filter (fun d => d < 2 ^ l))

theorem mem_shortFactorialDigits {F l d : ℕ} :
    d ∈ shortFactorialDigits F l ↔ d < 2 ^ l ∧ (d = 0 ∨ d ∣ F.factorial) := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with hz | hd
    · exact ⟨by rw [hz]; positivity, Or.inl hz⟩
    · obtain ⟨hdiv, hlt⟩ := Finset.mem_filter.mp hd
      exact ⟨hlt, Or.inr (Nat.dvd_of_mem_divisors hdiv)⟩
  · rintro ⟨hlt, hz | hdvd⟩
    · exact Finset.mem_insert.mpr (Or.inl hz)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.factorial_ne_zero F⟩, hlt⟩))

theorem shortFactorialDigits_small_integers {F l : ℕ} :
    min (F + 1) (2 ^ l) ≤ (shortFactorialDigits F l).card := by
  have hsub : Finset.range (min (F + 1) (2 ^ l)) ⊆ shortFactorialDigits F l := by
    intro d hd
    have hdlt := Finset.mem_range.mp hd
    apply mem_shortFactorialDigits.mpr
    refine ⟨lt_of_lt_of_le hdlt (min_le_right _ _), ?_⟩
    by_cases hz : d = 0
    · exact Or.inl hz
    · exact Or.inr (Nat.dvd_factorial (by omega)
        (by have := min_le_left (F + 1) (2 ^ l); omega))
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem prime_dvd_prime_product_iff {p : ℕ} (hp : Nat.Prime p)
    (s : Finset ℕ) (hs : ∀ q ∈ s, Nat.Prime q) :
    p ∣ s.prod id ↔ p ∈ s := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp h
    have heq : q = p := (hs q hq).dvd_iff_eq hp.ne_one |>.mp hpq
    exact heq ▸ hq
  · exact Finset.dvd_prod_of_mem id

theorem prime_products_injective {s t : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (ht : ∀ p ∈ t, Nat.Prime p)
    (heq : s.prod id = t.prod id) : s = t := by
  apply Finset.Subset.antisymm
  · intro p hp
    apply (prime_dvd_prime_product_iff (hs p hp) t ht).mp
    rw [← heq]
    exact Finset.dvd_prod_of_mem id hp
  · intro p hp
    apply (prime_dvd_prime_product_iff (ht p hp) s hs).mp
    rw [heq]
    exact Finset.dvd_prod_of_mem id hp

theorem prime_subset_product_dvd_factorial {F : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Nat.primesLE F) : s.prod id ∣ F.factorial := by
  rw [← Finset.prod_Ico_id_eq_factorial F]
  apply Finset.prod_dvd_prod_of_subset s (Finset.Ico 1 (F + 1)) id
  intro p hp
  obtain ⟨hpF, hprime⟩ := Nat.mem_primesLE.mp (hs hp)
  exact Finset.mem_Ico.mpr ⟨by have := hprime.two_le; omega, by omega⟩

theorem shortFactorialDigits_choose_lower {F l v : ℕ} (hheight : F ^ v < 2 ^ l) :
    (Nat.primeCounting F).choose v ≤ (shortFactorialDigits F l).card := by
  have hmap : Set.MapsTo (fun s : Finset ℕ => s.prod id)
      ((Nat.primesLE F).powersetCard v) (shortFactorialDigits F l) := by
    intro s hs
    obtain ⟨hs, hcard⟩ := Finset.mem_powersetCard.mp hs
    apply mem_shortFactorialDigits.mpr
    refine ⟨?_, Or.inr (prime_subset_product_dvd_factorial hs)⟩
    have hprod : s.prod id ≤ F ^ v := by
      calc
        s.prod id ≤ ∏ _ ∈ s, F := Finset.prod_le_prod (fun p hp => Nat.le_of_mem_primesLE (hs hp))
        _ = F ^ v := by rw [Finset.prod_const, hcard]
    exact hprod.trans_lt hheight
  have hinj : Set.InjOn (fun s : Finset ℕ => s.prod id) ((Nat.primesLE F).powersetCard v) := by
    intro s hs t ht heq
    apply prime_products_injective _ _ heq
    · intro p hp
      exact Nat.prime_of_mem_primesLE ((Finset.mem_powersetCard.mp hs).1 hp)
    · intro p hp
      exact Nat.prime_of_mem_primesLE ((Finset.mem_powersetCard.mp ht).1 hp)
  simpa only [Finset.card_powersetCard, Nat.primesLE_card_eq_primeCounting] using
    Finset.card_le_card_of_injOn _ hmap hinj

theorem choose_lower_half_ratio {n v : ℕ} (hv : 0 < v) (hvn : 2 * v ≤ n) :
    ((n : ℝ) / 2 / (v : ℝ)) ^ v ≤ (n.choose v : ℝ) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hnsub : (n : ℝ) / 2 ≤ ((n + 1 - v : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : v ≤ n + 1), Nat.cast_add, Nat.cast_one]
    have hh : (2 : ℝ) * v ≤ n := by exact_mod_cast hvn
    linarith
  have hfac : (v.factorial : ℝ) ≤ (v : ℝ) ^ v := by exact_mod_cast Nat.factorial_le_pow v
  calc
    ((n : ℝ) / 2 / (v : ℝ)) ^ v = ((n : ℝ) / 2) ^ v / (v : ℝ) ^ v := div_pow _ _ _
    _ ≤ (((n + 1 - v : ℕ) : ℝ) ^ v) / (v : ℝ) ^ v := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnsub v) (by positivity)
    _ ≤ (((n + 1 - v : ℕ) : ℝ) ^ v) / (v.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ ≤ (n.choose v : ℝ) := Nat.pow_le_choose v n


theorem half_binaryLength_rpow_le {F : ℕ} (hF : 2 ≤ F) :
    (2 : ℝ) ^ ((binaryLength F : ℝ) / 2) ≤ (F : ℝ) := by
  have hlog : 1 ≤ Nat.log 2 F := Nat.le_log_of_pow_le (by decide) (by simpa using hF)
  have hlen : (binaryLength F : ℝ) / 2 ≤ (Nat.log 2 F : ℝ) := by
    simp only [binaryLength, Nat.cast_add, Nat.cast_one]
    have hh : (1 : ℝ) ≤ Nat.log 2 F := by exact_mod_cast hlog
    linarith
  calc
    (2 : ℝ) ^ ((binaryLength F : ℝ) / 2) ≤ (2 : ℝ) ^ (Nat.log 2 F : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlen
    _ = ((2 ^ Nat.log 2 F : ℕ) : ℝ) := by simp
    _ ≤ (F : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : F ≠ 0)

theorem shortFactorialDigits_uniform_lower {F k : ℕ} {δ : ℝ}
    (hF : 2 ≤ F) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hprimes : (2 * (k : ℝ)) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ)) :
    ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (shortFactorialDigits F l).card := by
  intro l hlpos hlk
  let a := binaryLength F
  have ha : 0 < a := binaryLength_pos F
  have hFa : (2 : ℝ) ^ ((a : ℝ) / 2) ≤ (F : ℝ) := half_binaryLength_rpow_le hF
  by_cases hsmall : l ≤ 4 * a
  · have hsmallreal : (l : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast hsmall
    have hfirst : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (F + 1 : ℕ) := by
      calc
        (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
        _ ≤ (F : ℝ) := hFa
        _ ≤ (F + 1 : ℕ) := by exact_mod_cast Nat.le_succ F
    have hsecond : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ ((2 ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    have hmin : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (min (F + 1) (2 ^ l) : ℕ) := by
      rw [Nat.cast_min]
      exact le_min hfirst hsecond
    exact hmin.trans (by exact_mod_cast shortFactorialDigits_small_integers (F := F) (l := l))
  · let v := l / (2 * a)
    have hvpos : 0 < v := Nat.div_pos (by omega) (by omega)
    have hvle : v ≤ k := (Nat.div_le_self l (2 * a)).trans hlk
    have hmul : 2 * a * v ≤ l := Nat.mul_div_le l (2 * a)
    have hupper : l < 2 * a * (v + 1) := Nat.lt_mul_div_succ l (by omega)
    have halower : l ≤ 4 * a * v := by nlinarith
    have hheight : F ^ v < 2 ^ l := by
      calc
        F ^ v ≤ (2 ^ a) ^ v := Nat.pow_le_pow_left
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) F).le v
        _ = 2 ^ (a * v) := (pow_mul _ _ _).symm
        _ < 2 ^ l := Nat.pow_lt_pow_right (by decide : 1 < 2) (by nlinarith)
    have hFpow : 1 ≤ (F : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ F by omega)) hδ.le
    have htwov : 2 * v ≤ Nat.primeCounting F := by
      have hkr : (v : ℝ) ≤ k := by exact_mod_cast hvle
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hreal : 2 * (v : ℝ) ≤ (Nat.primeCounting F : ℝ) := by nlinarith
      exact_mod_cast hreal
    have hratio : (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) / 2 / (v : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hvpos : (0 : ℝ) < v)).mpr
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hkr : (v : ℝ) ≤ k := by exact_mod_cast hvle
      have hF0 : 0 ≤ (F : ℝ) ^ δ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hkr hF0]
    have halowerreal : (l : ℝ) ≤ 4 * (a : ℝ) * (v : ℝ) := by exact_mod_cast halower
    calc
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ (((a : ℝ) / 2 * δ) * (v : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left halowerreal hδ.le]
      _ = (((2 : ℝ) ^ ((a : ℝ) / 2)) ^ δ) ^ v := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_mul (by norm_num)]
      _ ≤ ((F : ℝ) ^ δ) ^ v :=
        pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by positivity) hFa hδ.le) v
      _ ≤ ((Nat.primeCounting F : ℝ) / 2 / (v : ℝ)) ^ v :=
        pow_le_pow_left₀ (by positivity) hratio v
      _ ≤ ((Nat.primeCounting F).choose v : ℝ) := choose_lower_half_ratio hvpos htwov
      _ ≤ (shortFactorialDigits F l).card := by exact_mod_cast shortFactorialDigits_choose_lower hheight


def binaryAppend (A D : Finset ℕ) (b : ℕ) : Finset ℕ :=
  (A ×ˢ D).image (fun p => p.1 + 2 ^ b * p.2)

def natResidueFiber (A : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  A.filter (fun x => Nat.ModEq q x r)

noncomputable def natResidueMass (A : Finset ℕ) (q r : ℕ) : ℝ :=
  ((natResidueFiber A q r).card : ℝ) / (A.card : ℝ)

theorem binary_append_injective {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + 2 ^ b * p.2) (A ×ˢ D : Finset (ℕ × ℕ)) := by
  intro p hp s hs heq
  change p.1 + 2 ^ b * p.2 = s.1 + 2 ^ b * s.2 at heq
  have hpA := hA p.1 (Finset.mem_product.mp hp).1
  have hsA := hA s.1 (Finset.mem_product.mp hs).1
  have hmod := congrArg (fun n => n % (2 ^ b)) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpA, Nat.mod_eq_of_lt hsA] at hmod
  have hmul : 2 ^ b * p.2 = 2 ^ b * s.2 := by omega
  have hright := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ b) hmul
  exact Prod.ext hmod hright

theorem binary_append_card {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) : (binaryAppend A D b).card = A.card * D.card := by
  rw [binaryAppend, Finset.card_image_of_injOn (binary_append_injective hA), Finset.card_product]

theorem binary_append_nonempty {A D : Finset ℕ} {b : ℕ}
    (hA : A.Nonempty) (hD : D.Nonempty) : (binaryAppend A D b).Nonempty := by
  exact (hA.product hD).image _

theorem binary_append_lt {A D : Finset ℕ} {b l : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hD : ∀ d ∈ D, d < 2 ^ l) :
    ∀ x ∈ binaryAppend A D b, x < 2 ^ (b + l) := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  have ha := hA a (Finset.mem_product.mp had).1
  have hd := hD d (Finset.mem_product.mp had).2
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_left (show d + 1 ≤ 2 ^ l by omega) (Nat.zero_le (2 ^ b))]

theorem nat_residue_fiber_mono_modulus {A : Finset ℕ} {q Q r : ℕ} (hq : q ∣ Q) :
    natResidueFiber A Q r ⊆ natResidueFiber A q r := by
  intro x hx
  obtain ⟨hx, hmod⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, hmod.of_dvd hq⟩

theorem nat_residue_fiber_card_le_one {A : Finset ℕ} {q r : ℕ}
    (hA : ∀ x ∈ A, x < q) : (natResidueFiber A q r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxA, hxmod⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyA, hymod⟩ := Finset.mem_filter.mp hy
  have hxy := hxmod.trans hymod.symm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hA x hxA), Nat.mod_eq_of_lt (hA y hyA)] using hxy

theorem binary_append_residue_fiber {A D : Finset ℕ} {b q r : ℕ} (hq : q ∣ 2 ^ b) :
    natResidueFiber (binaryAppend A D b) q r = binaryAppend (natResidueFiber A q r) D b := by
  have hequiv (a d : ℕ) : Nat.ModEq q (a + 2 ^ b * d) r ↔ Nat.ModEq q a r := by
    have hh : Nat.ModEq q (a + 2 ^ b * d) a := by
      simpa only [add_zero] using (Nat.ModEq.refl a).add ((hq.trans (dvd_mul_right _ _)).modEq_zero_nat)
    exact ⟨fun h => hh.symm.trans h, fun h => hh.trans h⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hm⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp had).1, (hequiv a d).mp hm⟩,
        (Finset.mem_product.mp had).2⟩, rfl⟩
  · intro hx
    obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
    obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hd⟩, rfl⟩,
      (hequiv a d).mpr hm⟩

theorem binary_append_residue_fiber_card {A D : Finset ℕ} {b q r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hq : q ∣ 2 ^ b) :
    (natResidueFiber (binaryAppend A D b) q r).card = (natResidueFiber A q r).card * D.card := by
  rw [binary_append_residue_fiber hq]
  exact binary_append_card (fun x hx => hA x (Finset.mem_filter.mp hx).1)

theorem binary_append_residue_mass {A D : Finset ℕ} {b q r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hD : D.Nonempty) (hq : q ∣ 2 ^ b) :
    natResidueMass (binaryAppend A D b) q r = natResidueMass A q r := by
  have hDc : (D.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hD
  unfold natResidueMass
  rw [binary_append_residue_fiber_card hA hq, binary_append_card hA, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ hDc

theorem binary_append_residue_mass_high {A D : Finset ℕ} {b j r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hne : A.Nonempty) (hD : D.Nonempty) (hj : b ≤ j) :
    natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ 1 / (A.card : ℝ) := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  calc
    natResidueMass (binaryAppend A D b) (2 ^ j) r ≤
        natResidueMass (binaryAppend A D b) (2 ^ b) r := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_le_card (nat_residue_fiber_mono_modulus (pow_dvd_pow 2 hj))
    _ = natResidueMass A (2 ^ b) r := binary_append_residue_mass hA hD (dvd_refl _)
    _ ≤ 1 / (A.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ hAc.le
      exact_mod_cast nat_residue_fiber_card_le_one hA

theorem nat_residue_fiber_range_card_le {q N r : ℕ} (hq : 0 < q) :
    (natResidueFiber (Finset.range (q * N)) q r).card ≤ N := by
  have hmap : Set.MapsTo (fun x : ℕ => x / q)
      (natResidueFiber (Finset.range (q * N)) q r) (Finset.range N) := by
    intro x hx
    have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [mul_comm] using hxlt))
  have hinj : Set.InjOn (fun x : ℕ => x / q)
      (natResidueFiber (Finset.range (q * N)) q r) := by
    intro x hx y hy heq
    change x / q = y / q at heq
    have hmod := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    change x % q = y % q at hmod
    have hxdiv := Nat.mod_add_div x q
    have hydiv := Nat.mod_add_div y q
    rw [heq, hmod] at hxdiv
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hinj

theorem nat_residue_fiber_bounded_card_le {A : Finset ℕ} {b j r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hj : j ≤ b) :
    (natResidueFiber A (2 ^ j) r).card ≤ 2 ^ (b - j) := by
  have hpow : 2 ^ b = 2 ^ j * 2 ^ (b - j) := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hsub : natResidueFiber A (2 ^ j) r ⊆ natResidueFiber (Finset.range (2 ^ b)) (2 ^ j) r := by
    intro x hx
    obtain ⟨hxA, hmod⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hA x hxA), hmod⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [hpow]
  exact nat_residue_fiber_range_card_le (by positivity)

def initialOddDigits (b : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (b - 1))).image (fun i => 2 * i + 1)

theorem initial_odd_digits_card (b : ℕ) : (initialOddDigits b).card = 2 ^ (b - 1) := by
  rw [initialOddDigits, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro x y h
    change 2 * x + 1 = 2 * y + 1 at h
    omega

theorem initial_odd_digits_nonempty (b : ℕ) : (initialOddDigits b).Nonempty := by
  apply Finset.card_pos.mp
  rw [initial_odd_digits_card]
  positivity

theorem initial_odd_digits_lt {b : ℕ} (hb : 0 < b) :
    ∀ x ∈ initialOddDigits b, x < 2 ^ b := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hi := Finset.mem_range.mp hi
  have hp : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb]
  rw [hp]
  omega

theorem initial_odd_digits_odd {b x : ℕ} (hx : x ∈ initialOddDigits b) : Odd x := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, by ring⟩

theorem initial_odd_digits_entropy {b : ℕ} {c : ℝ} (hb : 2 ≤ b) (hc : c ≤ 1 / 2) :
    (2 : ℝ) ^ (c * (b : ℝ)) ≤ (initialOddDigits b).card := by
  rw [initial_odd_digits_card, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

theorem initial_odd_digits_spread {b j r : ℕ} {c : ℝ}
    (hb : 2 ≤ b) (hj : 2 ≤ j) (hjb : j ≤ b) (hc : c ≤ 1) :
    natResidueMass (initialOddDigits b) (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
  have hcard := nat_residue_fiber_bounded_card_le (r := r)
    (initial_odd_digits_lt (by omega : 0 < b)) hjb
  unfold natResidueMass
  rw [initial_odd_digits_card]
  calc
    ((natResidueFiber (initialOddDigits b) (2 ^ j) r).card : ℝ) / ((2 ^ (b - 1) : ℕ) : ℝ) ≤
        ((2 ^ (b - j) : ℕ) : ℝ) / ((2 ^ (b - 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = (2 : ℝ) ^ (1 - (j : ℝ)) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Nat.cast_sub hjb,
        Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem binary_append_entropy {A D : Finset ℕ} {b l : ℕ} {c : ℝ}
    (hA : ∀ x ∈ A, x < 2 ^ b)
    (hcA : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card)
    (hcD : (2 : ℝ) ^ (c * (l : ℝ)) ≤ D.card) :
    (2 : ℝ) ^ (c * ((b + l : ℕ) : ℝ)) ≤ (binaryAppend A D b).card := by
  rw [binary_append_card hA, Nat.cast_mul, Nat.cast_add, mul_add, Real.rpow_add (by norm_num)]
  exact mul_le_mul hcA hcD (by positivity) (Nat.cast_nonneg _)

theorem binary_append_spread {A D : Finset ℕ} {b l : ℕ} {c : ℝ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hne : A.Nonempty) (hD : D.Nonempty)
    (hl : l ≤ b) (hc : 0 ≤ c)
    (hcA : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card)
    (hspread : ∀ j : ℕ, 2 ≤ j → j ≤ b → ∀ r : ℕ,
      natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))) :
    ∀ j : ℕ, 2 ≤ j → j ≤ b + l → ∀ r : ℕ,
      natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
  intro j hj hjbl r
  by_cases hjb : j ≤ b
  · rw [binary_append_residue_mass hA hD (pow_dvd_pow 2 hjb)]
    exact hspread j hj hjb r
  · calc
      natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ 1 / (A.card : ℝ) :=
        binary_append_residue_mass_high hA hne hD (by omega)
      _ ≤ 1 / (2 : ℝ) ^ (c * (b : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hcA
      _ = (2 : ℝ) ^ (-(c * (b : ℝ))) := by rw [Real.rpow_neg (by norm_num), one_div]
      _ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hltwo : (j : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast (show j ≤ 2 * b by omega)
        nlinarith [mul_le_mul_of_nonneg_left hltwo hc]

theorem short_factorial_digits_nonempty (F l : ℕ) : (shortFactorialDigits F l).Nonempty := by
  exact ⟨0, Finset.mem_insert_self _ _⟩

theorem short_factorial_digits_entropy {F K : ℕ} {c : ℝ}
    (h : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card)
    {l : ℕ} (hl : l ≤ K) : (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card := by
  by_cases hz : l = 0
  · subst l
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact_mod_cast Finset.card_pos.mpr (short_factorial_digits_nonempty F 0)
  · exact h l (by omega) hl

theorem binary_append_odd {A D : Finset ℕ} {b : ℕ} (hb : 0 < b)
    (hA : ∀ x ∈ A, Odd x) : ∀ x ∈ binaryAppend A D b, Odd x := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  exact (hA a (Finset.mem_product.mp had).1).add_even
    ((even_two.pow_of_ne_zero (Nat.ne_of_gt hb)).mul_right d)

theorem binary_append_representations {A : Finset ℕ} {F K b l u : ℕ} (hb : b ≤ K)
    (hA : ∀ x ∈ A, HasFactorialDivisorMultiset (F + 2 * K) x u) :
    ∀ x ∈ binaryAppend A (shortFactorialDigits F l) b,
      HasFactorialDivisorMultiset (F + 2 * K) x (u + 1) := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  apply factorial_multiset_add (hA a ha)
  rcases (mem_shortFactorialDigits.mp hd).2 with hz | hdiv
  · rw [hz, mul_zero]
    exact factorial_multiset_zero _ _
  · exact factorial_multiset_singleton (shifted_divisor_dvd_factorial hdiv hb)

structure BinaryBlockProfile (F K b u : ℕ) (c : ℝ) (A : Finset ℕ) : Prop where
  nonempty : A.Nonempty
  bounded : ∀ x ∈ A, x < 2 ^ b
  odd : ∀ x ∈ A, Odd x
  representatives : ∀ x ∈ A, HasFactorialDivisorMultiset (F + 2 * K) x u
  entropy : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card
  spread : ∀ j : ℕ, 2 ≤ j → j ≤ b → ∀ r : ℕ,
    natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))

theorem initial_odd_digits_profile {F K b : ℕ} {c : ℝ}
    (hb : 2 ≤ b) (hF : 2 ^ b ≤ F) (hc : c ≤ 1 / 2) :
    BinaryBlockProfile F K b 1 c (initialOddDigits b) := by
  refine ⟨initial_odd_digits_nonempty b, initial_odd_digits_lt (by omega),
    fun _ hx => initial_odd_digits_odd hx, ?_, initial_odd_digits_entropy hb hc, ?_⟩
  · intro x hx
    have hodd := initial_odd_digits_odd hx
    have hpos : 0 < x := by obtain ⟨t, ht⟩ := hodd; omega
    exact factorial_multiset_singleton (Nat.dvd_factorial hpos
      (by have := initial_odd_digits_lt (by omega : 0 < b) x hx; omega))
  · intro j hj hjb r
    exact initial_odd_digits_spread hb hj hjb (by linarith)

theorem binary_append_profile {F K b l u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F K b u c A) (hb : 0 < b) (hbK : b ≤ K) (hl : l ≤ b) (hc : 0 ≤ c)
    (hD : (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    BinaryBlockProfile F K (b + l) (u + 1) c (binaryAppend A (shortFactorialDigits F l) b) := by
  refine ⟨binary_append_nonempty hA.nonempty (short_factorial_digits_nonempty F l),
    binary_append_lt hA.bounded (fun _ hd => (mem_shortFactorialDigits.mp hd).1),
    binary_append_odd hb hA.odd, binary_append_representations hbK hA.representatives,
    binary_append_entropy hA.bounded hA.entropy hD, ?_⟩
  exact binary_append_spread hA.bounded hA.nonempty (short_factorial_digits_nonempty F l)
    hl hc hA.entropy hA.spread

def binaryBlockEndpoint (K b₀ i : ℕ) : ℕ := min K (2 ^ i * b₀)

def binaryBlockWidth (K b₀ i : ℕ) : ℕ := binaryBlockEndpoint K b₀ (i + 1) - binaryBlockEndpoint K b₀ i

def binaryBlockSet (F K b₀ : ℕ) : ℕ → Finset ℕ
  | 0 => initialOddDigits b₀
  | i + 1 => binaryAppend (binaryBlockSet F K b₀ i)
      (shortFactorialDigits F (binaryBlockWidth K b₀ i)) (binaryBlockEndpoint K b₀ i)

theorem binary_block_endpoint_zero {K b₀ : ℕ} (hb : b₀ ≤ K) : binaryBlockEndpoint K b₀ 0 = b₀ := by
  simp only [binaryBlockEndpoint, pow_zero, one_mul, min_eq_right hb]

theorem binary_block_endpoint_bounds {K b₀ : ℕ} (hb : b₀ ≤ K) (i : ℕ) :
    b₀ ≤ binaryBlockEndpoint K b₀ i ∧ binaryBlockEndpoint K b₀ i ≤ K := by
  refine ⟨le_min hb ?_, min_le_left _ _⟩
  nlinarith [show 1 ≤ 2 ^ i from Nat.one_le_two_pow]

theorem binary_block_endpoint_mono (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ i ≤ binaryBlockEndpoint K b₀ (i + 1) := by
  apply min_le_min_left
  exact Nat.mul_le_mul_right b₀ (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem binary_block_endpoint_succ_le_twice (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ (i + 1) ≤ 2 * binaryBlockEndpoint K b₀ i := by
  unfold binaryBlockEndpoint
  by_cases h : 2 ^ i * b₀ ≤ K
  · rw [min_eq_right h]
    calc
      min K (2 ^ (i + 1) * b₀) ≤ 2 ^ (i + 1) * b₀ := min_le_right _ _
      _ = 2 * (2 ^ i * b₀) := by rw [pow_succ]; ring
  · rw [min_eq_left (by omega : K ≤ 2 ^ i * b₀)]
    exact (min_le_left _ _).trans (by omega)

theorem binary_block_width_add (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ i + binaryBlockWidth K b₀ i = binaryBlockEndpoint K b₀ (i + 1) := by
  exact Nat.add_sub_of_le (binary_block_endpoint_mono K b₀ i)

theorem binary_block_width_le (K b₀ i : ℕ) :
    binaryBlockWidth K b₀ i ≤ binaryBlockEndpoint K b₀ i := by
  have := binary_block_endpoint_succ_le_twice K b₀ i
  unfold binaryBlockWidth
  omega

theorem binary_block_endpoint_top {K b₀ : ℕ} (hb : 1 ≤ b₀) :
    binaryBlockEndpoint K b₀ (binaryLength K) = K := by
  apply min_eq_left
  have hK : K < 2 ^ binaryLength K := Nat.lt_pow_succ_log_self (by decide : 1 < 2) K
  nlinarith

theorem binary_block_set_profile {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    ∀ i : ℕ, BinaryBlockProfile F K (binaryBlockEndpoint K b₀ i) (i + 1) c (binaryBlockSet F K b₀ i) := by
  intro i
  induction i with
  | zero =>
    rw [binary_block_endpoint_zero hbK]
    exact initial_odd_digits_profile hb hF hcsmall
  | succ i ih =>
    have hbds := binary_block_endpoint_bounds hbK i
    have hw := binary_block_width_le K b₀ i
    have hstep := binary_append_profile ih (by omega) hbds.2 hw hc
      (short_factorial_digits_entropy hD (hw.trans hbds.2))
    rw [binary_block_width_add] at hstep
    exact hstep

theorem binary_block_set_profile_top {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    BinaryBlockProfile F K K (binaryLength K + 1) c (binaryBlockSet F K b₀ (binaryLength K)) := by
  have h := binary_block_set_profile hb hbK hF hc hcsmall hD (binaryLength K)
  rwa [binary_block_endpoint_top (by omega : 1 ≤ b₀)] at h


theorem shortFactorialDigits_uniform_linear {F k : ℕ} {δ : ℝ}
    (hF : 2 ≤ F) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hprimes : (k : ℝ) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) * (binaryLength F : ℝ)) :
    ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (shortFactorialDigits F l).card := by
  intro l hlpos hlk
  let a := binaryLength F
  have ha : 0 < a := binaryLength_pos F
  have hFa : (2 : ℝ) ^ ((a : ℝ) / 2) ≤ (F : ℝ) := half_binaryLength_rpow_le hF
  by_cases hsmall : l ≤ 4 * a
  · have hsmallreal : (l : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast hsmall
    have hfirst : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (F + 1 : ℕ) := by
      calc
        (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
        _ ≤ (F : ℝ) := hFa
        _ ≤ (F + 1 : ℕ) := by exact_mod_cast Nat.le_succ F
    have hsecond : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ ((2 ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    have hmin : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (min (F + 1) (2 ^ l) : ℕ) := by
      rw [Nat.cast_min]
      exact le_min hfirst hsecond
    exact hmin.trans (by exact_mod_cast shortFactorialDigits_small_integers (F := F) (l := l))
  · let v := l / (2 * a)
    have hvpos : 0 < v := Nat.div_pos (by omega) (by omega)
    have hvle : v ≤ k := (Nat.div_le_self l (2 * a)).trans hlk
    have hmul : 2 * a * v ≤ l := Nat.mul_div_le l (2 * a)
    have hupper : l < 2 * a * (v + 1) := Nat.lt_mul_div_succ l (by omega)
    have halower : l ≤ 4 * a * v := by nlinarith
    have hheight : F ^ v < 2 ^ l := by
      calc
        F ^ v ≤ (2 ^ a) ^ v := Nat.pow_le_pow_left
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) F).le v
        _ = 2 ^ (a * v) := (pow_mul _ _ _).symm
        _ < 2 ^ l := Nat.pow_lt_pow_right (by decide : 1 < 2) (by nlinarith)
    have hFpow : 1 ≤ (F : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ F by omega)) hδ.le
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hmulR : 2 * (a : ℝ) * (v : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hmul.trans hlk
    have hcore : 2 * (v : ℝ) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) := by
      have hh := (mul_le_mul_of_nonneg_right hmulR (Real.rpow_nonneg (Nat.cast_nonneg F) δ)).trans hprimes
      apply le_of_mul_le_mul_left (a := (a : ℝ)) _ haR
      change (a : ℝ) * (2 * (v : ℝ) * (F : ℝ) ^ δ) ≤ (a : ℝ) * (Nat.primeCounting F : ℝ)
      dsimp [a] at hh ⊢
      nlinarith
    have htwov : 2 * v ≤ Nat.primeCounting F := by
      have hh := mul_le_mul_of_nonneg_left hFpow (show (0:ℝ) ≤ 2*(v:ℝ) by positivity)
      have hr : 2*(v:ℝ) ≤ (Nat.primeCounting F : ℝ) := by nlinarith
      exact_mod_cast hr
    have hratio : (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) / 2 / (v : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hvpos : (0 : ℝ) < v)).mpr
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      nlinarith
    have halowerreal : (l : ℝ) ≤ 4 * (a : ℝ) * (v : ℝ) := by exact_mod_cast halower
    calc
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ (((a : ℝ) / 2 * δ) * (v : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left halowerreal hδ.le]
      _ = (((2 : ℝ) ^ ((a : ℝ) / 2)) ^ δ) ^ v := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_mul (by norm_num)]
      _ ≤ ((F : ℝ) ^ δ) ^ v :=
        pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by positivity) hFa hδ.le) v
      _ ≤ ((Nat.primeCounting F : ℝ) / 2 / (v : ℝ)) ^ v :=
        pow_le_pow_left₀ (by positivity) hratio v
      _ ≤ ((Nat.primeCounting F).choose v : ℝ) := choose_lower_half_ratio hvpos htwov
      _ ≤ (shortFactorialDigits F l).card := by exact_mod_cast shortFactorialDigits_choose_lower hheight


#print axioms shortFactorialDigits_uniform_linear
#print axioms binary_block_set_profile_top
end Erdos18c
