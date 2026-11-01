import Erdos18c.LocalBounds
import Mathlib.Analysis.SpecificLimits.Basic

open Finset Filter
open scoped Topology
namespace Erdos18c
noncomputable section

def liftingScale (T : ℕ) : ℕ := ⌊(T:ℝ)/(65536*Real.log (T:ℝ))⌋₊

theorem liftingRatio_tendsto : Tendsto (fun T : ℕ => (T:ℝ)/(65536*Real.log (T:ℝ))) atTop atTop := by
  have hs0 := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))).tendsto_div_nhds_zero
  have hs : Tendsto (fun T : ℕ => 65536*Real.log (T:ℝ)/(T:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hs0.const_mul (65536:ℝ)
  have hp : ∀ᶠ T : ℕ in atTop, 0<65536*Real.log (T:ℝ)/(T:ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with T hT
    have hTR : (1:ℝ)<T := by exact_mod_cast hT
    exact div_pos (mul_pos (by norm_num) (Real.log_pos hTR)) (by linarith)
  have hw : Tendsto (fun T : ℕ => 65536*Real.log (T:ℝ)/(T:ℝ)) atTop (𝓝[>] 0) :=
    tendsto_inf.2 ⟨hs,tendsto_principal.2 hp⟩
  have hi := tendsto_inv_nhdsGT_zero.comp hw
  change Tendsto (fun T : ℕ => (65536*Real.log (T:ℝ)/(T:ℝ))⁻¹) atTop atTop at hi
  simpa only [inv_div] using hi

theorem liftingScale_tendsto : Tendsto liftingScale atTop atTop :=
  tendsto_nat_floor_atTop.comp liftingRatio_tendsto

theorem eventually_liftingScale_bounds : ∀ᶠ T : ℕ in atTop,
    4≤T ∧ 1≤liftingScale T ∧ 2*liftingScale T≤T ∧
    (T:ℝ)/(131072*Real.log (T:ℝ)) ≤ liftingScale T ∧
    (liftingScale T:ℝ) ≤ (T:ℝ)/(65536*Real.log (T:ℝ)) ∧
    localHost (liftingScale T)≤T ∧
    (localCount (liftingScale T):ℝ)≤400000*Real.log (T:ℝ)^5 ∧
    Real.log (localHeight (liftingScale T):ℝ) ≤ (T:ℝ)/16 := by
  have htend : Tendsto (fun T : ℕ => Real.log (T:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 4, liftingScale_tendsto.eventually_ge_atTop 1,
    liftingRatio_tendsto.eventually_ge_atTop 2, htend.eventually_ge_atTop 1,
    liftingScale_tendsto.eventually eventually_local_count_bound,
    liftingScale_tendsto.eventually eventually_local_height_bound] with T hT hk hratio hlog hcount hheight
  have hTR : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hlogp : 0<Real.log (T:ℝ) := by linarith
  have hu : (liftingScale T:ℝ)≤(T:ℝ)/(65536*Real.log (T:ℝ)) :=
    Nat.floor_le (by positivity)
  have hlt := Nat.lt_floor_add_one ((T:ℝ)/(65536*Real.log (T:ℝ)))
  have hl : (T:ℝ)/(131072*Real.log (T:ℝ)) ≤ liftingScale T := by
    change _ ≤ (⌊(T:ℝ)/(65536*Real.log (T:ℝ))⌋₊:ℝ)
    have he : (T:ℝ)/(131072*Real.log (T:ℝ)) = ((T:ℝ)/(65536*Real.log (T:ℝ)))/2 := by ring
    rw [he]
    linarith
  have hscale : (65536*Real.log (T:ℝ))*(liftingScale T:ℝ)≤T := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<65536*Real.log (T:ℝ))).mp hu
    nlinarith
  have hk0 : (0:ℝ)≤liftingScale T := Nat.cast_nonneg _
  have htwoR : 2*(liftingScale T:ℝ)≤T := by nlinarith
  have htwo : 2*liftingScale T≤T := by exact_mod_cast htwoR
  have hhF : localHost (liftingScale T)≤T := by
    have he : (localHost (liftingScale T):ℝ)=1004*(liftingScale T:ℝ) := by simp [localHost,linearDigitHost]; ring
    have hr : (localHost (liftingScale T):ℝ)≤T := by rw [he]; nlinarith
    exact_mod_cast hr
  have hkT : (liftingScale T:ℝ)≤T := by nlinarith
  have hlogk : 0≤Real.log (liftingScale T:ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogle : Real.log (liftingScale T:ℝ)≤Real.log (T:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0<liftingScale T by omega)) hkT
  have hcountT := hcount.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogk hlogle 5) (by norm_num))
  have hheightT : Real.log (localHeight (liftingScale T):ℝ)≤(T:ℝ)/16 := by
    have hh := mul_le_mul_of_nonneg_left hlogle (show 0≤4096*(liftingScale T:ℝ) by positivity)
    have hbig : 4096*(liftingScale T:ℝ)*Real.log (T:ℝ)≤(T:ℝ)/16 := by nlinarith
    exact hheight.trans (hh.trans hbig)
  exact ⟨hT,hk,htwo,hl,hu,hhF,hcountT,hheightT⟩

#print axioms eventually_liftingScale_bounds
end
end Erdos18c
