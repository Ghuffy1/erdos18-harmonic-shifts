import Erdos18c.IntegerLifting

open Finset Filter
open scoped Topology
namespace Erdos18c
noncomputable section

theorem local_short_sums : ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ R : ℕ,
    0<R → N≤binaryLength R → ∃ u : ℕ,
      ShortSum (6*binaryLength R).factorial R u ∧
        (u:ℝ)≤C*Real.log (binaryLength R:ℝ)^7 := by
  obtain ⟨K,hK,hrep⟩ := integer_multiset_lifting
  let C : ℝ := K+52428800000+1
  have hC : 0<C := by dsimp [C]; linarith
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n:=7)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hratio : Tendsto (fun T : ℕ => C*Real.log (T:ℝ)^7/(T:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using
      hlittle.tendsto_div_nhds_zero.const_mul C
  have hlog : Tendsto (fun T : ℕ => Real.log (T:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ T : ℕ in atTop, 1≤T ∧ 1≤Real.log (T:ℝ) ∧ C*Real.log (T:ℝ)^7≤T := by
    filter_upwards [eventually_ge_atTop 1,hlog.eventually_ge_atTop 1,
      (tendsto_order.1 hratio).2 1 (by norm_num)] with T hT hl hr
    exact ⟨hT,hl,((div_lt_one (by exact_mod_cast (show 0<T by omega))).mp hr).le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.1 hev
  refine ⟨C,hC,N,?_⟩
  intro R hR hRN
  obtain ⟨hT,hlogT,hlinear⟩ := hN (binaryLength R) hRN
  obtain ⟨u,hu,huc⟩ := hrep R hR
  have hpow : 1≤Real.log (binaryLength R:ℝ)^7 := one_le_pow₀ hlogT
  have hcount : (u:ℝ)≤C*Real.log (binaryLength R:ℝ)^7 := by
    dsimp [C,localPotential] at *
    nlinarith [mul_le_mul_of_nonneg_left hpow hK]
  have huT : u≤binaryLength R := by exact_mod_cast hcount.trans hlinear
  have hd := factorial_multiset_to_distinct hu
  refine ⟨u,shortSum_mono_host (Nat.factorial_dvd_factorial (by omega))
    (Nat.factorial_ne_zero _) hd,hcount⟩

#print axioms local_short_sums
end
end Erdos18c
