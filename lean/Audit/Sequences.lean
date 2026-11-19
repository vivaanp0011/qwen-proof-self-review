import Mathlib

noncomputable section
open Filter Set Finset Function
open scoped Topology BigOperators
namespace Pilot

/-- Direct epsilon proof. The zero-indexed input u 0 represents the first summand a₁. -/
theorem means (u : ℕ → ℝ) (L : ℝ) (hu : Tendsto u atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, u k) / (n:ℝ)) atTop (𝓝 L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp hu (ε/2) (half_pos hε)
  let C := ∑ k ∈ range K, |u k-L|
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C/ε)
  refine ⟨max 1 (max K N),fun n hn => ?_⟩
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hk : K ≤ n := by omega
  have hc : C < (n:ℝ)*(ε/2) := by
    have hnN : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show N ≤ n by omega)
    have H := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    linarith
  have tail : (∑ k ∈ Finset.Ico K n, |u k-L|) ≤ (n:ℝ)*(ε/2) := calc
    _ ≤ ∑ k ∈ Finset.Ico K n, ε/2 := Finset.sum_le_sum fun k hk' => by
      simpa only [Real.dist_eq] using (hK k (Finset.mem_Ico.mp hk').1).le
    _ = ((n-K:ℕ):ℝ)*(ε/2) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n K) (half_pos hε).le
  have split := Finset.sum_range_add_sum_Ico (fun k => |u k-L|) hk
  have err : |∑ k ∈ range n, (u k - L)| < (n:ℝ)*ε := by
    apply lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _)
    rw [← split]; change C + _ < _; linarith
  have H : (∑ k ∈ range n, u k) / (n:ℝ) - L =
      (∑ k ∈ range n, (u k-L)) / (n:ℝ) := by
    rw [Finset.sum_sub_distrib]; simp only [Finset.sum_const,card_range,nsmul_eq_mul]
    field_simp
  rw [Real.dist_eq,H,abs_div,abs_of_pos hn0,div_lt_iff₀ hn0]
  simpa [mul_comm] using err

/-- The tail block at indices floor(n/2)+1 through n controls n*aₙ for either parity. -/
theorem monotoneSeries (a : ℕ → ℝ) (nonneg : ∀ n, 0 ≤ a n)
    (down : AntitoneOn a (Ici 1)) (hs : Summable a) :
    Tendsto (fun n : ℕ => (n:ℝ)*a n) atTop (𝓝 0) := by
  let S := fun n => ∑ j ∈ range n, a j
  have hS : Tendsto S atTop (𝓝 (∑' j, a j)) := hs.hasSum.tendsto_sum_nat
  have h1 := hS.comp (tendsto_add_atTop_nat 1)
  have h2 := hS.comp ((tendsto_add_atTop_nat 1).comp (Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0)))
  have htail : Tendsto (fun n : ℕ => 2*(S (n+1)-S (n/2+1))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (h1.sub h2).const_mul (2:ℝ)
  refine squeeze_zero' (.of_forall fun n => mul_nonneg (Nat.cast_nonneg n) (nonneg n)) ?_ htail
  filter_upwards [eventually_ge_atTop 1] with n hn
  have block : (∑ j ∈ Finset.Ico (n/2+1) (n+1), a n) ≤
      ∑ j ∈ Finset.Ico (n/2+1) (n+1), a j := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hj1,hj2⟩ := Finset.mem_Ico.mp hj
    exact down (by show 1 ≤ j; omega) hn (by omega)
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at block
  rw [Finset.sum_Ico_eq_sub _ (by omega)] at block
  have cnt : (n:ℝ) ≤ 2*((n+1-(n/2+1):ℕ):ℝ) := by
    exact_mod_cast (show n ≤ 2*(n+1-(n/2+1)) by omega)
  have h := mul_le_mul_of_nonneg_right cnt (nonneg n)
  dsimp [S]; linarith

def squareIndex (k : ℕ) := k^2
def powerIndex (k : ℕ) := 2^k
private theorem squareInc : StrictMono squareIndex := strictMono_nat_of_lt_succ fun n => by
  dsimp [squareIndex]; exact Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by decide)
private theorem powerInc : StrictMono powerIndex := strictMono_nat_of_lt_succ fun n => by
  dsimp [powerIndex]; rw [pow_succ]; have := Nat.two_pow_pos n; omega

/-- extend places h(k) at i(k) and zero at all other indices. -/
def spikes (i : ℕ → ℕ) (h : ℕ → ℝ) := Function.extend i h 0
def height (k : ℕ) : ℝ := 1/(k:ℝ)^2

private theorem spikes_nonneg (i : ℕ → ℕ) (hi : Injective i) (n : ℕ) :
    0 ≤ spikes i height n := by
  by_cases h : ∃ k, i k = n
  · obtain ⟨k,rfl⟩ := h; rw [spikes, hi.extend_apply]; dsimp [height]; positivity
  · rw [spikes,Function.extend_apply' _ _ _ h]; rfl

private theorem awayFromZero {a : ℕ → ℝ} {i : ℕ → ℕ} (hi : StrictMono i)
    (H : ∀ k ≥ 4, 1 ≤ (i k:ℝ) * a (i k)) :
    ¬ Tendsto (fun n : ℕ => (n:ℝ)*a n) atTop (𝓝 0) := by
  intro h
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp h (1:ℝ) zero_lt_one
  let k := max 4 N
  have hclose := hN (i k) ((le_max_right 4 N).trans (hi.id_le k))
  have hlarge := H k (le_max_left 4 N)
  rw [Real.dist_eq, sub_zero] at hclose
  exact (not_lt_of_ge hlarge) ((le_abs_self _).trans_lt hclose)

theorem squareCounterexample :
    (∀ n, 0 ≤ spikes squareIndex height n) ∧ Summable (spikes squareIndex height) ∧
      ¬ Tendsto (fun n : ℕ => (n:ℝ)*spikes squareIndex height n) atTop (𝓝 0) := by
  refine ⟨spikes_nonneg _ squareInc.injective, (summable_extend_zero squareInc.injective).2
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)), awayFromZero squareInc ?_⟩
  intro k hk
  rw [spikes,squareInc.injective.extend_apply]
  dsimp [squareIndex,height]; push_cast
  have hp : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

theorem powerCounterexample :
    (∀ n, 0 ≤ spikes powerIndex height n) ∧ Summable (spikes powerIndex height) ∧
      ¬ Tendsto (fun n : ℕ => (n:ℝ)*spikes powerIndex height n) atTop (𝓝 0) := by
  refine ⟨spikes_nonneg _ powerInc.injective, (summable_extend_zero powerInc.injective).2
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)), awayFromZero powerInc ?_⟩
  intro k hk
  rw [spikes,powerInc.injective.extend_apply]
  have hineq : k^2 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [pow_succ (2:ℕ)]; nlinarith [Nat.mul_le_mul_left k hk]
  dsimp [height,powerIndex]; push_cast
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hp : 0 < (k:ℝ)^2 := sq_pos_of_pos hk0
  rw [mul_one_div,le_div_iff₀ hp,one_mul]; exact_mod_cast hineq

/-- P02/B's proposed 1/k spikes have precisely the harmonic series as their sum. -/
theorem harmonicSquaresDiverge : ¬ Summable (spikes squareIndex (fun k => 1/(k:ℝ))) :=
  fun h => Real.not_summable_one_div_natCast ((summable_extend_zero squareInc.injective).1 h)

/-- Stronger numerical claim actually written in P02/A. -/
theorem exponentialProductDiverges : Tendsto (fun k : ℕ => (2:ℝ)^k/(k:ℝ)^2) atTop atTop := by
  have h : Tendsto (fun k : ℕ => (k:ℝ)^2/(2:ℝ)^k) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num),?_⟩
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
    apply Set.mem_Ioi.mpr; positivity
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp h

/-- P02/C's final missing multiplication. -/
theorem squareProductOne {k : ℕ} (h : 0 < k) :
    (squareIndex k:ℝ) * spikes squareIndex height (squareIndex k) = 1 := by
  rw [spikes,squareInc.injective.extend_apply]
  dsimp [squareIndex,height]; push_cast
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast h.ne'
  field_simp

/-- P02 reference solution, with spike label k+1 so the first nonzero term
is at index 2. The sum is one and the product at each spike is one. -/
theorem geometricReference :
    let i := fun k : ℕ => powerIndex (k+1)
    let h := fun k : ℕ => (1/(2:ℝ))^(k+1)
    HasSum (spikes i h) 1 ∧ (∀ k, (i k:ℝ) * spikes i h (i k) = 1) ∧
      (∀ n, 0 ≤ spikes i h n) ∧ ¬ Tendsto (fun n : ℕ => (n:ℝ)*spikes i h n) atTop (𝓝 0) := by
  intro i h
  have hi : StrictMono i := powerInc.comp (strictMono_nat_of_lt_succ fun _ => Nat.lt_succ_self _)
  have hg := (hasSum_geometric_of_lt_one (r:=(1/(2:ℝ))) (by norm_num) (by norm_num)).mul_left (1/2)
  have hh : HasSum h 1 := by
    norm_num at hg
    simpa [h,pow_succ,mul_comm] using hg
  have hprod (k : ℕ) : (i k:ℝ)*spikes i h (i k) = 1 := by
    rw [spikes,hi.injective.extend_apply]
    dsimp [i,h,powerIndex]; push_cast
    rw [←mul_pow]; norm_num
  refine ⟨(hasSum_extend_zero hi.injective).2 hh,hprod,?_,awayFromZero hi (fun k _ => (hprod k).ge)⟩
  intro n
  by_cases hz : ∃ k, i k = n
  · obtain ⟨k,rfl⟩ := hz; rw [spikes,hi.injective.extend_apply]; dsimp [h]; positivity
  · rw [spikes,Function.extend_apply' _ _ _ hz]; rfl

/-- In P02's first attempt the proposed forward-block inequality already
fails at M=2 for the decreasing, summable sequence (1,1,0,0,...). -/
theorem forwardBlockCounterexample :
    let a := fun n : ℕ => if n ≤ 2 then (1:ℝ) else 0
    (∀ n, 0 ≤ a n) ∧ Antitone a ∧ Summable a ∧ ¬ (2*a 2 ≤ a 2+a 3) := by
  intro a
  refine ⟨fun n => by dsimp [a]; split <;> norm_num,?_,?_,by norm_num [a]⟩
  · intro m n hmn
    by_cases h : n ≤ 2
    · simp [a,h,hmn.trans h]
    · simp [a,h]; split <;> norm_num
  · apply summable_of_ne_finset_zero (s:=range 3)
    intro n hn
    have h : ¬ n ≤ 2 := fun h => hn (Finset.mem_range.mpr (by omega))
    simp [a,h]

end Pilot
