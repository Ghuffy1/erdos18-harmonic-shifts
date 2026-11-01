import Erdos18c.FinalBound

/-!
The following three definitions reproduce the natural-number instances of
the definitions in google-deepmind/formal-conjectures at commit
a64e959c32c270df4dd0d96d2027481f15750534. Copyright 2026 The Formal
Conjectures Authors; Apache-2.0 (see licenses/Apache-2.0.txt).

Only definitions and target types are reproduced. The upstream file, which
contains unfinished conjectures, is not imported into the proof dependency
graph. The source snapshots and exact Git blob hashes accompany this package.
-/

open Filter Real

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

namespace Nat
def IsPractical (n : ℕ) : Prop :=
  ∀ m, m≤n → m∈subsetSums n.divisors
end Nat

namespace Erdos18
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D⊆n.divisors ∧ D.card=k ∧ m∈subsetSums D}
end Erdos18

namespace Erdos18c

theorem subsetSums_eq_original (A : Set ℕ) : Erdos18c.subsetSums A=_root_.subsetSums A := by
  ext n
  constructor
  · rintro ⟨B,hB,hEq⟩
    exact ⟨B,hB,hEq.symm⟩
  · rintro ⟨B,hB,hEq⟩
    exact ⟨B,hB,hEq.symm⟩

theorem practicalH_eq_original (n : ℕ) : Erdos18c.practicalH n=Erdos18.practicalH n := by
  simp only [Erdos18c.practicalH,Erdos18.practicalH,subsetSums_eq_original]

theorem isPractical_iff_original (n : ℕ) : Erdos18c.IsPractical n↔Nat.IsPractical n := by
  constructor
  · intro h m hm
    obtain ⟨D,hD,hEq⟩ := h m hm
    exact ⟨D,Finset.coe_subset.mpr hD,hEq.symm⟩
  · intro h m hm
    obtain ⟨D,hD,hEq⟩ := h m hm
    exact ⟨D,Finset.coe_subset.mp hD,hEq.symm⟩

end Erdos18c

namespace Erdos18

/-- Exact original part (a); earlier priority is expressly retained. -/
theorem erdos_18a :
    ∃ C : ℝ, 0<C ∧ ∃ᶠ m in atTop, Nat.IsPractical m ∧
      (practicalH m:ℝ)<(log (log m))^C := by
  simpa only [Erdos18c.StatementA,Erdos18c.practicalH_eq_original,
    Erdos18c.isPractical_iff_original] using Erdos18c.erdos_18a

/-- Exact original part (b); earlier priority is expressly retained. -/
theorem erdos_18b :
    ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, (practicalH n.factorial:ℝ)<(n:ℝ)^ε := by
  simpa only [Erdos18c.StatementB,Erdos18c.practicalH_eq_original] using Erdos18c.erdos_18b

/-- Exact original part (c), with no additional assumptions. -/
theorem erdos_18c :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, (practicalH n.factorial:ℝ)<(log n)^C := by
  simpa only [Erdos18c.Statement,Erdos18c.practicalH_eq_original] using Erdos18c.erdos_18c

end Erdos18

#print axioms Erdos18.erdos_18a
#print axioms Erdos18.erdos_18b
#print axioms Erdos18.erdos_18c
#print axioms Erdos18c.practicalH_eq_original
#print axioms Erdos18c.isPractical_iff_original
