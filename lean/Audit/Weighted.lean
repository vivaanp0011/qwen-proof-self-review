import Mathlib

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace Pilot

private theorem weightedIntegrable (g : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r)
    (hc : ContinuousOn g (Icc l r)) (n : ℕ) :
    IntervalIntegrable (fun x => x^n*g x) volume l r := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlr]
  exact ((continuous_id.pow n).continuousOn).mul hc

/-- Bound a piece of the weighted integral by its kernel mass times a bound
for the function on that piece. -/
theorem weightedBound (g : ℝ → ℝ) {l r B : ℝ} (hl : 0 ≤ l) (hlr : l ≤ r)
    (hc : ContinuousOn g (Icc l r)) (hb : ∀ x ∈ Icc l r, |g x| ≤ B) (n : ℕ) :
    |((n:ℝ)+1)*(∫ x in l..r, x^n*g x)| ≤ B*(r^(n+1)-l^(n+1)) := by
  have hiabs : IntervalIntegrable (fun x => |x^n*g x|) volume l r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    exact (((continuous_id.pow n).continuousOn).mul hc).abs
  have hcomp : (∫ x in l..r, |x^n*g x|) ≤ ∫ x in l..r, B*x^n := by
    apply intervalIntegral.integral_mono_on hlr hiabs
      ((continuous_const.mul (continuous_id.pow n)).intervalIntegrable l r)
    intro x hx
    rw [abs_mul,abs_of_nonneg (pow_nonneg (hl.trans hx.1) n),mul_comm B]
    exact mul_le_mul_of_nonneg_left (hb x hx) (pow_nonneg (hl.trans hx.1) n)
  have h := (intervalIntegral.abs_integral_le_integral_abs (f:=fun x => x^n*g x) hlr).trans hcomp
  rw [intervalIntegral.integral_const_mul,integral_pow] at h
  rw [abs_mul,abs_of_pos (by positivity : 0 < (n:ℝ)+1)]
  refine (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n:ℝ)+1)).trans_eq ?_
  field_simp

/-- P07, with continuity required only on [0,1]. The weight's integral is
one. The mass of [0,a] is exactly a^(n+1) and tends to zero for a<1. -/
theorem weightedConcentration (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)*(∫ x in (0:ℝ)..1, x^n*f x)) atTop (𝓝 (f 1)) := by
  let g := fun x => f x - f 1
  have hg : ContinuousOn g (Icc (0:ℝ) 1) := hf.sub continuousOn_const
  obtain ⟨p,hp,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hg.abs
  let C := |g p|
  have hbound : ∀ x ∈ Icc (0:ℝ) 1, |g x| ≤ C := fun x hx => hmax hx
  have hnear := Metric.continuousWithinAt_iff.mp (hf 1 (right_mem_Icc.mpr zero_le_one))
  apply Metric.tendsto_atTop.mpr
  intro ε he
  obtain ⟨δ,hδ,H⟩ := hnear (ε/2) (half_pos he)
  let d := min (δ/2) (1/2)
  let a := 1-d
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdδ : d < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hhalf : d ≤ 1/2 := min_le_right _ _
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hleft : Icc (0:ℝ) a ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ha1.le
  have hright : Icc a (1:ℝ) ⊆ Icc 0 1 := Icc_subset_Icc ha0 le_rfl
  have hgsmall : ∀ x ∈ Icc a (1:ℝ), |g x| ≤ ε/2 := by
    intro x hx
    have hl := hx.1; have hr := hx.2
    have hdist : dist x 1 < δ := by rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hr)]; dsimp [a] at hl; linarith
    exact (H (hright hx) hdist).le
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp (tendsto_add_atTop_nat 1)
  have hvan : Tendsto (fun n : ℕ => C*a^(n+1)) atTop (𝓝 0) := by simpa using hpow.const_mul C
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hvan (ε/2) (half_pos he)
  refine ⟨N,fun n hn => ?_⟩
  let w := (n:ℝ)+1
  have hw : w ≠ 0 := by dsimp [w]; positivity
  have normConst : w*(∫ x in (0:ℝ)..1, f 1*x^n) = f 1 := by
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp [w]; field_simp
  have hdiff : w*(∫ x in (0:ℝ)..1, x^n*f x) - f 1 = w*(∫ x in (0:ℝ)..1, x^n*g x) := by
    have eqfun : (fun x : ℝ => x^n*g x) = fun x => x^n*f x - f 1*x^n := by
      funext x; dsimp [g]; ring
    have hc : IntervalIntegrable (fun x : ℝ => f 1*x^n) volume 0 1 :=
      (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 1
    rw [eqfun,intervalIntegral.integral_sub (weightedIntegrable f zero_le_one hf n) hc,mul_sub,normConst]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (weightedIntegrable g ha0 (hg.mono hleft) n) (weightedIntegrable g ha1.le (hg.mono hright) n)
  have hfar := weightedBound g le_rfl ha0 (hg.mono hleft) (fun x hx => hbound x (hleft hx)) n
  have hclose := weightedBound g ha0 ha1.le (hg.mono hright) hgsmall n
  simp only [zero_pow (Nat.succ_ne_zero n),sub_zero] at hfar
  rw [one_pow] at hclose
  have nearLe : |w*(∫ x in a..1, x^n*g x)| ≤ ε/2 := hclose.trans (by nlinarith [mul_nonneg (half_pos he).le (pow_nonneg ha0 (n+1))])
  have hlimit := hN n hn
  rw [Real.dist_eq,sub_zero] at hlimit
  change dist (w*_) (f 1) < ε
  rw [Real.dist_eq,hdiff,←hsplit,mul_add]
  exact (abs_add_le _ _).trans_lt (by linarith [hfar,nearLe,le_abs_self (C*a^(n+1))])

end Pilot
