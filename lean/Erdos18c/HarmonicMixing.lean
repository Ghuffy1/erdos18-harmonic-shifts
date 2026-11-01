import Erdos18c.DyadicDilations
import Mathlib.Algebra.BigOperators.Intervals

open Finset
namespace Erdos18c
noncomputable section

def harmonicSum (k : ℕ) : ℝ := ∑ a ∈ range k, 1 / ((a:ℝ)+1)
def harmonicWeight (k a : ℕ) : ℝ := (1 / ((a:ℝ)+1)) / harmonicSum k
def harmonicLaw (k : ℕ) (p : Fin (2^k) → ℝ) : Fin (2^k) → ℝ :=
  finiteMixture (fun a : Fin k => harmonicWeight k a.val) (fun a => dyadicDilate k a.val p)

theorem harmonicSum_pos (k : ℕ) (hk : 0<k) : 0 < harmonicSum k := by
  have hb : (1:ℝ) ≤ harmonicSum k := by
    calc
      1 = 1 / ((0:ℝ)+1) := by norm_num
      _ ≤ _ := by
        simpa [harmonicSum] using single_le_sum (f := fun a : ℕ => 1/((a:ℝ)+1))
          (fun a _ => by positivity) (mem_range.mpr hk)
  linarith

theorem harmonicWeight_nonneg (k a : ℕ) : 0 ≤ harmonicWeight k a := by
  unfold harmonicWeight harmonicSum
  positivity

theorem harmonicWeight_sum (k : ℕ) (hk : 0<k) :
    ∑ a ∈ range k, harmonicWeight k a = 1 := by
  unfold harmonicWeight
  rw [← sum_div]
  change harmonicSum k / harmonicSum k = 1
  exact div_self (harmonicSum_pos k hk).ne'

theorem harmonicLaw_probability (k : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x, p x=1) :
    (∀ x, 0≤harmonicLaw k p x) ∧ ∑ x, harmonicLaw k p x=1 := by
  constructor
  · exact finiteMixture_nonneg _ _ (fun a => harmonicWeight_nonneg _ _)
      (fun a => dyadicDilate_nonneg p hp)
  · rw [harmonicLaw,sum_finiteMixture]
    simp_rw [dyadicDilate_sum, hs, mul_one]
    rw [Fin.sum_univ_eq_sum_range]
    exact harmonicWeight_sum k hk

def harmonicDefect (k j : ℕ) (p : Fin (2^k) → ℝ) : ℝ :=
  ∑ a ∈ range (j+1), harmonicWeight k a * dyadicMinority p Fin.val (j-a)

theorem harmonicDefect_lower (k j : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (c : ℝ)
    (hmass : c * (j+1:ℕ) ≤ ∑ t ∈ range (j+1), dyadicMinority p Fin.val t) :
    c / harmonicSum k ≤ harmonicDefect k j p := by
  have href : (∑ a ∈ range (j+1), dyadicMinority p Fin.val (j-a)) =
      ∑ t ∈ range (j+1), dyadicMinority p Fin.val t := by
    simpa using sum_range_reflect (dyadicMinority p Fin.val) (j+1)
  have hh := weighted_reciprocal_lower (range (j+1))
    (fun a => dyadicMinority p Fin.val (j-a)) (fun a => (a:ℝ)+1)
    (j+1:ℕ) (harmonicSum k) c (by positivity) (harmonicSum_pos k hk)
    (fun a _ => dyadicMinority_nonneg p Fin.val hp (j-a))
    (fun a ha => ⟨by positivity, by exact_mod_cast (mem_range.mp ha)⟩)
    (by rwa [href])
  apply hh.trans_eq
  unfold harmonicDefect harmonicWeight
  rw [sum_div]
  apply sum_congr rfl
  intro a _
  ring

theorem harmonicLaw_bias (k j : ℕ) (hj : j<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) :
    dyadicBitBias (harmonicLaw k p) Fin.val j ≤ 1 - harmonicDefect k j p := by
  have hk : 0<k := by omega
  let b := fun a : ℕ => dyadicBitBias (dyadicDilate k a p) Fin.val j
  have hble (a : ℕ) : b a ≤ 1 := by
    apply dyadicBitBias_le_one
    · exact dyadicDilate_nonneg p hp
    · rw [dyadicDilate_sum,hs]
  have hpos (a : ℕ) : 0 ≤ harmonicWeight k a * (1-b a) :=
    mul_nonneg (harmonicWeight_nonneg _ _) (sub_nonneg.mpr (hble a))
  have hpartial : harmonicDefect k j p ≤ ∑ a ∈ range k, harmonicWeight k a*(1-b a) := by
    calc
      _ = ∑ a ∈ range (j+1), harmonicWeight k a*(1-b a) := by
        apply sum_congr rfl
        intro a ha
        have haj : a≤j := by have := mem_range.mp ha; omega
        have hb := dyadicDilate_bitBias hj haj p
        have hu := dyadic_bitBias_add_minority p Fin.val hs (j-a)
        dsimp [b]
        rw [hb]
        congr 1
        linarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun a _ _ => hpos a)
  have htotal : (∑ a ∈ range k, harmonicWeight k a*(1-b a)) =
      1 - ∑ a ∈ range k, harmonicWeight k a*b a := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib,harmonicWeight_sum k hk]
  rw [htotal] at hpartial
  have hb : dyadicBitBias (harmonicLaw k p) Fin.val j ≤
      ∑ a ∈ range k, harmonicWeight k a*b a := by
    rw [dyadic_bitBias_eq_involution]
    change involutionBias (dyadicHalf j)
      (finitePushforward (harmonicLaw k p) (dyadicProject (Nat.succ_le_of_lt hj))) ≤ _
    rw [harmonicLaw,pushforward_finiteMixture]
    have hh := involutionBias_finiteMixture
      (fun a : Fin k => harmonicWeight k a.val)
      (fun a : Fin k => finitePushforward (dyadicDilate k a.val p) (dyadicProject (Nat.succ_le_of_lt hj)))
      (fun a => harmonicWeight_nonneg _ _) (dyadicHalf j)
    apply hh.trans_eq
    calc
      _ = ∑ a : Fin k, harmonicWeight k a.val * dyadicBitBias (dyadicDilate k a.val p) Fin.val j := by
        apply sum_congr rfl
        intro a _
        congr 1
        exact (dyadic_bitBias_eq_involution _ Fin.val j).symm
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => harmonicWeight k a*b a) k
  linarith

theorem dyadicBitBias_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    0 ≤ dyadicBitBias p f j := sum_nonneg fun _ _ => abs_nonneg _

theorem dyadic_entropy_lower_of_bias {k : ℕ} (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) (δ : ℝ)
    (hb : ∀ j<k, dyadicBitBias p Fin.val j ≤ δ) :
    (k:ℝ) * Real.log 2 * (1-δ) ≤ dyadicEntropy p Fin.val k := by
  have hlower : ∀ j∈range k, Real.log 2 * (1-δ) ≤
      dyadicEntropy p Fin.val (j+1)-dyadicEntropy p Fin.val j := by
    intro j hj
    have hbi := hb j (mem_range.mp hj)
    have he := dyadic_bitBias_add_minority p Fin.val hs j
    have hu : 1-δ ≤ dyadicMinority p Fin.val j := by linarith
    have hh := dyadic_entropy_step_lower p Fin.val hp j
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hu hlog]
  have hh := sum_le_sum hlower
  rw [dyadic_entropy_telescope p Fin.val hs] at hh
  simpa only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id,mul_assoc] using hh

theorem harmonicLaw_power_entropy (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L, 0<L → L≤k → g * L * Real.log 2 ≤ dyadicEntropy p Fin.val L) :
    (k:ℝ) * Real.log 2 *
      (1-Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)) ≤
      dyadicEntropy (realConvolutionPow (harmonicLaw k p) r) Fin.val k := by
  let c := g^2*(Real.log 2)^2/2
  let t := c/harmonicSum k
  have hprob := harmonicLaw_probability k hk p hp hs
  have hout := realConvolutionPow_probability hprob.1 hprob.2 r
  apply dyadic_entropy_lower_of_bias _ hout.1 hout.2
  intro j hj
  have hm := dyadic_prefix_minority p Fin.val hp hs (j+1) (by omega) g hg
    (hprefix (j+1) (by omega) (by omega))
  have hdef := harmonicDefect_lower k j hk p hp c hm
  have hb0 := harmonicLaw_bias k j hj p hp hs
  have hb : dyadicBitBias (harmonicLaw k p) Fin.val j ≤ 1-t := by
    dsimp [t]
    linarith
  have hnonneg := dyadicBitBias_nonneg (harmonicLaw k p) Fin.val j
  have hbase : 0 ≤ 1-t := hnonneg.trans hb
  have hpwr := pow_le_pow_left₀ hnonneg hb r
  have hexp : 1-t ≤ Real.exp (-t) := by
    have hh := Real.add_one_le_exp (-t)
    linarith
  have hpowexp := pow_le_pow_left₀ hbase hexp r
  have hconv := dyadic_bitBias_convolutionPow (Nat.succ_le_of_lt hj) (harmonicLaw k p) r
  have hr := hconv.trans (hpwr.trans hpowexp)
  have he : Real.exp (-t) ^ r = Real.exp (-(r:ℝ)*c/harmonicSum k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [t]
    ring
  rwa [he] at hr

theorem dyadicEntropy_full (k : ℕ) (p : Fin (2^k) → ℝ) :
    dyadicEntropy p Fin.val k = finiteEntropy univ p := by
  have hid (x : Fin (2^k)) : dyadicIndex k x.val = x := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  have he : dyadicDistribution p Fin.val k = p := by
    funext x
    simp [dyadicDistribution,finitePushforward,hid,sum_filter]
  rw [dyadicEntropy,he]

def finiteSupport {ι : Type*} [Fintype ι] (p : ι → ℝ) : Finset ι :=
  univ.filter fun x => p x≠0

theorem harmonicLaw_support_large (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L,0<L → L≤k → g*L*Real.log 2 ≤ dyadicEntropy p Fin.val L)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) :
    2^k < 2*(finiteSupport (realConvolutionPow (harmonicLaw k p) r)).card := by
  let P := realConvolutionPow (harmonicLaw k p) r
  let B := finiteSupport P
  have hprob := harmonicLaw_probability k hk p hp hs
  have hout := realConvolutionPow_probability hprob.1 hprob.2 r
  have hB : B.Nonempty := by
    by_contra hB
    have hz (x : Fin (2^k)) : P x=0 := by
      by_contra hx
      exact hB ⟨x,by simp [B,finiteSupport,hx]⟩
    have hzero : ∑ x,P x=0 := sum_eq_zero fun x _ => hz x
    have hone : ∑ x,P x=1 := hout.2
    linarith
  have hcardpos : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hb := finite_entropy_le_log_support P B hout.1 hout.2 (fun x hx => by
    by_contra hn
    exact hx (by simp [B,finiteSupport,hn]))
  have hmain := harmonicLaw_power_entropy k r hk p hp hs g hg hprefix
  rw [dyadicEntropy_full] at hmain
  change (k:ℝ)*Real.log 2*(1-Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)) ≤ finiteEntropy univ P at hmain
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hr)
  have hrhs : Real.exp (-Real.log (2*(k:ℝ))) = (2*(k:ℝ))⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<2*(k:ℝ))]
  rw [hrhs] at hexp
  have hdelta : (k:ℝ)*Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hexp hkp.le
    have hid : (k:ℝ)*(2*(k:ℝ))⁻¹ = 1/2 := by field_simp
    have hneg : -((r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) =
        -(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k := by ring
    rwa [hid,hneg] at hh
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hdelta hlog.le
  have hlower : ((k:ℝ)-1/2)*Real.log 2 ≤ finiteEntropy univ P := by nlinarith
  by_contra hc
  have hc' : 2*B.card ≤ 2^k := Nat.le_of_not_gt hc
  have hcR : (B.card:ℝ) ≤ (2:ℝ)^k/2 := by
    have hh : (2:ℝ)*(B.card:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hc'
    linarith
  have hlogB := Real.log_le_log hcardpos hcR
  rw [Real.log_div (by positivity : (2:ℝ)^k≠0) (by norm_num),Real.log_pow] at hlogB
  linarith

theorem harmonicLaw_covers (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L,0<L → L≤k → g*L*Real.log 2 ≤ dyadicEntropy p Fin.val L)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)
    (x : Fin (2^k)) :
    ∃ a∈finiteSupport (realConvolutionPow (harmonicLaw k p) r),
    ∃ b∈finiteSupport (realConvolutionPow (harmonicLaw k p) r), a+b=x := by
  apply twice_card_cover
  simpa using harmonicLaw_support_large k r hk p hp hs g hg hprefix hr

#print axioms harmonicLaw_bias
end
end Erdos18c
