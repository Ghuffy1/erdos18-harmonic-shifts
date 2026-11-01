import Erdos18c.FiniteLaw
import Mathlib.Data.ZMod.Basic

/-!
Finite real convolution estimates. The summation/reindexing arguments adapt
the finite convolution infrastructure of the credited Kohlmeyer--Kruer 18(b)
source. The involution-bias contraction is used for the new dyadic mixing step.
-/

open Finset
namespace Erdos18c

noncomputable section
variable {G H : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]

def realConvolution (f g : G → ℝ) (x : G) : ℝ := ∑ y, f y * g (x-y)
def realShift (h : G) (f : G → ℝ) (x : G) : ℝ := f (x+h)
def realDifference (h : G) (f : G → ℝ) (x : G) : ℝ := f x - f (x+h)
def finiteL1 (f : G → ℝ) : ℝ := ∑ x, |f x|
def involutionBias (h : G) (f : G → ℝ) : ℝ := finiteL1 (realDifference h f) / 2

omit [AddCommGroup G] [DecidableEq G] in
theorem finiteL1_nonneg (f : G → ℝ) : 0 ≤ finiteL1 f :=
  sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq G] in
theorem finiteL1_shift (h : G) (f : G → ℝ) : finiteL1 (realShift h f) = finiteL1 f := by
  exact Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)

omit [DecidableEq G] in
theorem sum_realConvolution (f g : G → ℝ) :
    ∑ x, realConvolution f g x = (∑ x, f x) * (∑ x, g x) := by
  simp only [realConvolution]
  rw [sum_comm]
  calc
    (∑ y, ∑ x, f y * g (x-y)) = ∑ y, f y * ∑ x, g x := by
      apply sum_congr rfl
      intro y _
      rw [← mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (sum_mul _ _ _).symm

omit [DecidableEq G] in
theorem realConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : G) :
    0 ≤ realConvolution f g x := sum_nonneg (fun y _ => mul_nonneg (hf y) (hg _))

omit [DecidableEq G] in
theorem finiteL1_convolution_le (f g : G → ℝ) :
    finiteL1 (realConvolution f g) ≤ finiteL1 f * finiteL1 g := by
  calc
    _ ≤ ∑ x, ∑ y, |f y| * |g (x-y)| := by
      apply sum_le_sum
      intro x _
      simpa only [realConvolution, abs_mul] using abs_sum_le_sum_abs (s := univ) (f := fun y => f y * g (x-y))
    _ = ∑ y, |f y| * ∑ x, |g x| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      rw [← mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (sum_mul _ _ _).symm

omit [DecidableEq G] in
theorem convolution_shift_right (h : G) (f g : G → ℝ) :
    realConvolution f (realShift h g) = realShift h (realConvolution f g) := by
  funext x
  apply sum_congr rfl
  intro y _
  dsimp [realShift]
  congr 2
  abel

omit [DecidableEq G] in
theorem convolution_shift_left (h : G) (f g : G → ℝ) :
    realConvolution (realShift h f) g = realShift h (realConvolution f g) := by
  funext x
  refine Fintype.sum_equiv (Equiv.addRight h) _ _ ?_
  intro y
  dsimp [realShift]
  congr 2
  abel

omit [DecidableEq G] in
theorem convolution_difference_right (h : G) (f g : G → ℝ) :
    realConvolution f (realDifference h g) = realDifference h (realConvolution f g) := by
  funext x
  have hh := congrFun (convolution_shift_right h f g) x
  simpa only [realConvolution, realDifference, mul_sub, sum_sub_distrib,
    realShift] using congrArg (fun z => realConvolution f g x - z) hh

omit [DecidableEq G] in
theorem convolution_difference_left (h : G) (f g : G → ℝ) :
    realConvolution (realDifference h f) g = realDifference h (realConvolution f g) := by
  funext x
  have hh := congrFun (convolution_shift_left h f g) x
  simpa only [realConvolution, realDifference, sub_mul, sum_sub_distrib,
    realShift] using congrArg (fun z => realConvolution f g x - z) hh

theorem convolution_double_difference (h : G) (hh : h+h=0) (f g : G → ℝ) (x : G) :
    realConvolution (realDifference h f) (realDifference h g) x =
      2 * realDifference h (realConvolution f g) x := by
  rw [convolution_difference_left, convolution_difference_right]
  simp only [realDifference, add_assoc, hh, add_zero]
  ring

omit [DecidableEq G] in
theorem involutionBias_nonneg (h : G) (f : G → ℝ) : 0 ≤ involutionBias h f :=
  div_nonneg (finiteL1_nonneg _) (by norm_num)

omit [DecidableEq G] in
theorem involutionBias_le_l1 (h : G) (f : G → ℝ) : involutionBias h f ≤ finiteL1 f := by
  have hb : finiteL1 (realDifference h f) ≤ finiteL1 f + finiteL1 (realShift h f) := by
    calc
      _ ≤ ∑ x, (|f x| + |f (x+h)|) := sum_le_sum (fun x _ => abs_sub _ _)
      _ = _ := sum_add_distrib
  rw [finiteL1_shift] at hb
  unfold involutionBias
  linarith

theorem involutionBias_convolution_le (h : G) (hh : h+h=0) (f g : G → ℝ) :
    involutionBias h (realConvolution f g) ≤ involutionBias h f * involutionBias h g := by
  have hb := finiteL1_convolution_le (realDifference h f) (realDifference h g)
  have he : finiteL1 (realConvolution (realDifference h f) (realDifference h g)) =
      2 * finiteL1 (realDifference h (realConvolution f g)) := by
    simp only [finiteL1, convolution_double_difference h hh, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_sum]
  rw [he] at hb
  unfold involutionBias
  nlinarith

def realConvolutionPow (f : G → ℝ) : ℕ → G → ℝ
  | 0 => fun x => if x=0 then 1 else 0
  | r+1 => realConvolution f (realConvolutionPow f r)

theorem involutionBias_convolutionPow_le (h : G) (hh : h+h=0) (f : G → ℝ) (r : ℕ) :
    involutionBias h (realConvolutionPow f r) ≤ involutionBias h f ^ r := by
  induction r with
  | zero =>
    have hb := involutionBias_le_l1 h (realConvolutionPow f 0)
    have hd : finiteL1 (realConvolutionPow f 0) = 1 := by
      calc
        _ = ∑ x : G, if x=0 then (1:ℝ) else 0 := by
          apply sum_congr rfl
          intro x _
          by_cases hx : x=0 <;> simp [realConvolutionPow,hx]
        _ = 1 := by simp
    simpa only [hd, pow_zero] using hb
  | succ r ih =>
    calc
      _ ≤ involutionBias h f * involutionBias h (realConvolutionPow f r) :=
        involutionBias_convolution_le h hh _ _
      _ ≤ involutionBias h f * involutionBias h f ^ r :=
        mul_le_mul_of_nonneg_left ih (involutionBias_nonneg _ _)
      _ = _ := by rw [pow_succ]; ring

theorem realConvolutionPow_probability {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsum : ∑ x, f x = 1) (r : ℕ) :
    (∀ x, 0 ≤ realConvolutionPow f r x) ∧ ∑ x, realConvolutionPow f r x = 1 := by
  induction r with
  | zero => simp [realConvolutionPow]; intro x; split_ifs <;> norm_num
  | succ r ih => exact ⟨realConvolution_nonneg hf ih.1, by rw [realConvolutionPow, sum_realConvolution, hsum, ih.2, one_mul]⟩

theorem sum_test_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (T : ι → κ) (h : κ → ℝ) :
    (∑ b, h b * finitePushforward p T b) = ∑ a, h (T a) * p a := by
  simp only [finitePushforward, mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [mul_ite, mul_zero]
  simp

omit [DecidableEq G] in
theorem sum_test_realConvolution (f g h : G → ℝ) :
    (∑ a, h a * realConvolution f g a) = ∑ x, ∑ y, h (x+y) * f x * g y := by
  simp only [realConvolution, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ ?_
  intro z
  simp only [Equiv.subRight_apply]
  have he : x+(z-x)=z := by abel
  rw [he]
  ring

theorem convolution_pushforward_left {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (T : ι → G) (g : G → ℝ) (a : G) :
    realConvolution (finitePushforward p T) g a = ∑ x, p x * g (a-T x) := by
  simpa only [realConvolution, mul_comm] using sum_test_pushforward p T (fun b => g (a-b))

omit [DecidableEq G] in
theorem pushforward_realConvolution (f g : G → ℝ) (T : G →+ H) :
    finitePushforward (realConvolution f g) T =
      realConvolution (finitePushforward f T) (finitePushforward g T) := by
  funext a
  calc
    _ = ∑ z : G, (if T z=a then (1:ℝ) else 0) * realConvolution f g z := by
      simp only [finitePushforward, sum_filter, ite_mul, one_mul, zero_mul]
    _ = ∑ x : G, ∑ y : G, (if T (x+y)=a then (1:ℝ) else 0) * f x * g y :=
      sum_test_realConvolution f g _
    _ = ∑ x : G, f x * finitePushforward g T (a-T x) := by
      apply sum_congr rfl
      intro x _
      simp only [finitePushforward, sum_filter, mul_sum]
      apply sum_congr rfl
      intro y _
      rw [map_add]
      by_cases hy : T y = a-T x
      · simp [hy]
      · have hxy : T x+T y ≠ a := by
          intro heq
          exact hy ((eq_sub_iff_add_eq').mpr heq)
        simp [hy,hxy]
    _ = _ := (convolution_pushforward_left f T _ a).symm

theorem pushforward_realConvolutionPow (f : G → ℝ) (T : G →+ H) (r : ℕ) :
    finitePushforward (realConvolutionPow f r) T =
      realConvolutionPow (finitePushforward f T) r := by
  induction r with
  | zero =>
    funext a
    simp only [realConvolutionPow, finitePushforward, sum_filter]
    have he (x : G) : (if T x=a then (if x=0 then (1:ℝ) else 0) else 0) =
        if x=0 then (if a=0 then 1 else 0) else 0 := by
      by_cases hx : x=0
      · subst x; simp [eq_comm]
      · simp [hx]
    simp_rw [he]
    simp
  | succ r ih => rw [realConvolutionPow, pushforward_realConvolution, ih, realConvolutionPow]

omit [DecidableEq G] [Fintype H] in
theorem pushforward_shift (f : G → ℝ) (T : G →+ H) (h : G) :
    finitePushforward (realShift h f) T = realShift (T h) (finitePushforward f T) := by
  funext b
  simp only [finitePushforward, realShift, sum_filter]
  refine Fintype.sum_equiv (Equiv.addRight h) _ _ ?_
  intro a
  simp [map_add]

omit [DecidableEq G] [Fintype H] in
theorem pushforward_difference (f : G → ℝ) (T : G →+ H) (h : G) :
    finitePushforward (realDifference h f) T = realDifference (T h) (finitePushforward f T) := by
  have he : finitePushforward (realDifference h f) T =
      fun b => finitePushforward f T b - finitePushforward (realShift h f) T b := by
    funext b
    simp only [finitePushforward, realDifference, realShift, sum_sub_distrib]
  rw [he, pushforward_shift]
  rfl

omit [AddCommGroup G] [AddCommGroup H] in
theorem finiteL1_pushforward_injective (f : G → ℝ) (T : G → H) (hT : Function.Injective T) :
    finiteL1 (finitePushforward f T) = finiteL1 f := by
  have he (b : H) : |finitePushforward f T b| = finitePushforward (fun a => |f a|) T b := by
    by_cases hx : ∃ a, T a=b
    · obtain ⟨a,rfl⟩ := hx
      simp [finitePushforward, hT.eq_iff, sum_filter]
    · have hn (a : G) : T a ≠ b := fun ha => hx ⟨a,ha⟩
      simp [finitePushforward, hn]
  unfold finiteL1
  simp_rw [he]
  exact finite_pushforward_sum _ _

theorem involutionBias_pushforward (f : G → ℝ) (T : G →+ H)
    (hT : Function.Injective T) (h : G) :
    involutionBias (T h) (finitePushforward f T) = involutionBias h f := by
  unfold involutionBias
  rw [← pushforward_difference, finiteL1_pushforward_injective _ T hT]

def finiteMixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ) (x : G) : ℝ :=
  ∑ i, w i * F i x

omit [AddCommGroup G] [DecidableEq G] in
theorem sum_finiteMixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ) :
    ∑ x, finiteMixture w F x = ∑ i, w i * ∑ x, F i x := by
  simp only [finiteMixture]
  rw [sum_comm]
  simp only [mul_sum]

omit [Fintype G] [AddCommGroup G] [DecidableEq G] in
theorem finiteMixture_nonneg {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hF : ∀ i x, 0 ≤ F i x) (x : G) : 0 ≤ finiteMixture w F x :=
  sum_nonneg fun i _ => mul_nonneg (hw i) (hF i x)

omit [AddCommGroup G] [DecidableEq G] [Fintype H] [AddCommGroup H] in
theorem pushforward_finiteMixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → G → ℝ) (T : G → H) :
    finitePushforward (finiteMixture w F) T = finiteMixture w (fun i => finitePushforward (F i) T) := by
  funext b
  unfold finitePushforward finiteMixture
  rw [sum_comm]
  simp only [mul_sum]

omit [DecidableEq G] in
theorem involutionBias_finiteMixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → G → ℝ) (hw : ∀ i, 0 ≤ w i) (h : G) :
    involutionBias h (finiteMixture w F) ≤ ∑ i, w i * involutionBias h (F i) := by
  have hinner (x : G) : realDifference h (finiteMixture w F) x =
      ∑ i, w i * realDifference h (F i) x := by
    simp only [finiteMixture, realDifference, mul_sub, sum_sub_distrib]
  have hb : finiteL1 (realDifference h (finiteMixture w F)) ≤
      ∑ i, w i * finiteL1 (realDifference h (F i)) := by
    unfold finiteL1
    simp_rw [hinner]
    calc
      _ ≤ ∑ x, ∑ i, |w i * realDifference h (F i) x| :=
        sum_le_sum fun x _ => abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [sum_comm]
        simp only [abs_mul, abs_of_nonneg (hw _), mul_sum]
  unfold involutionBias
  simp_rw [← mul_div_assoc]
  rw [← sum_div]
  exact div_le_div_of_nonneg_right hb (by norm_num)

theorem twice_card_cover (B : Finset G) (hcard : Fintype.card G < 2*B.card) (x : G) :
    ∃ a∈B, ∃ b∈B, a+b=x := by
  by_contra hn
  have hd : Disjoint B (B.image (fun b => x-b)) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,hb,he⟩ := mem_image.mp hb
    exact hn ⟨a,ha,b,hb,by rw [← he]; abel⟩
  have hc := card_le_card (subset_univ (B ∪ B.image (fun b => x-b)))
  rw [card_union_of_disjoint hd, card_image_of_injective B (fun a b h => by
    rw [sub_eq_add_neg,sub_eq_add_neg] at h
    exact neg_injective (add_left_cancel h))] at hc
  simp only [card_univ] at hc
  omega

theorem convolutionPow_support (f : G → ℝ) (r : ℕ) (x : G)
    (hx : realConvolutionPow f r x ≠ 0) :
    ∃ L : List G, L.length=r ∧ (∀ a∈L, f a≠0) ∧ L.sum=x := by
  induction r generalizing x with
  | zero =>
    have hx0 : x=0 := by by_contra h; simp [realConvolutionPow,h] at hx
    subst x
    exact ⟨[],rfl,by simp,by simp⟩
  | succ r ih =>
    obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
    have han : f a ≠ 0 := (mul_ne_zero_iff.mp ha).1
    have htail : realConvolutionPow f r (x-a)≠0 := (mul_ne_zero_iff.mp ha).2
    obtain ⟨L,hL,hf,hs⟩ := ih (x-a) htail
    refine ⟨a::L,by simp [hL],?_,by simp [hs]⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact han
    · exact hf b hb

#print axioms involutionBias_convolutionPow_le
end
end Erdos18c
