import Mathlib

noncomputable section
open Filter Set
open scoped Topology
namespace Pilot

def moving (n : ℕ) (x : ℝ) := x/(1+(n:ℝ)*x^2)

/-- P04: exact maximum, including attainment. -/
theorem movingMaximum (n : ℕ) (hn : 0 < n) :
    IsGreatest (Set.range (fun x => |moving n x|)) (1/(2*Real.sqrt (n:ℝ))) := by
  let s := Real.sqrt (n:ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : s^2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hd (x : ℝ) : 0 < 1+(n:ℝ)*x^2 := by positivity
  constructor
  · refine ⟨1/s,?_⟩
    change |(1/s)/(1+(n:ℝ)*(1/s)^2)| = 1/(2*s)
    rw [abs_of_nonneg (by positivity),←hsq]
    field_simp
    ring
  · rintro y ⟨x,rfl⟩
    change |x/(1+(n:ℝ)*x^2)| ≤ 1/(2*s)
    rw [abs_div,abs_of_pos (hd x),div_le_div_iff₀ (hd x) (by positivity)]
    have h := sq_nonneg (s*|x|-1)
    have heq : (s*|x|)^2 = (n:ℝ)*x^2 := by rw [mul_pow,hsq,sq_abs]
    nlinarith

theorem movingDerivative (n : ℕ) (x : ℝ) :
    HasDerivAt (moving n) ((1-(n:ℝ)*x^2)/(1+(n:ℝ)*x^2)^2) x := by
  have hd : (1:ℝ)+(n:ℝ)*x^2 ≠ 0 := by positivity
  have H := (hasDerivAt_id x).div ((hasDerivAt_const x (1:ℝ)).add
    (((hasDerivAt_id x).pow 2).const_mul (n:ℝ))) hd
  convert H using 1; dsimp [moving]; ring

theorem movingUniform : TendstoUniformly moving (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε he
  obtain ⟨N,hN⟩ := exists_nat_gt ((1/ε)^2)
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  have hnpos : 0 < n := by omega
  have hnN : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show N ≤ n by omega)
  have hs := Real.sqrt_pos.2 (show 0 < (n:ℝ) by exact_mod_cast hnpos)
  have hex : 1/ε < Real.sqrt (n:ℝ) := by
    have h := hN.trans_le hnN
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),sq_nonneg (1/ε-Real.sqrt (n:ℝ))]
  have hb : 1/(2*Real.sqrt (n:ℝ)) < ε := by
    have h := (div_lt_iff₀ he).mp hex
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [mul_pos hs he]
  intro x
  simpa [Real.dist_eq] using ((movingMaximum n hnpos).2 (mem_range_self x)).trans_lt hb

/-- At epsilon = 1/2 the auxiliary ceiling cutoff in both P04 answers gives equality. -/
theorem movingCeilingEquality : |moving 1 1| = (1/2:ℝ) := by norm_num [moving]

/-- P06: the two-sided difference quotient is bounded by three times a square root. -/
theorem holderDerivative (f : ℝ → ℝ)
    (H : ∀ x, |x-2| < 1 → |f x - f 2| ≤ 3*|x-2|^(3/(2:ℝ))) : HasDerivAt f 0 2 := by
  rw [hasDerivAt_iff_tendsto_slope,Metric.tendsto_nhdsWithin_nhds]
  intro ε he
  refine ⟨min 1 ((ε/3)^2),lt_min (by norm_num) (by positivity),?_⟩
  intro x hx hnear
  have hne : x ≠ 2 := hx
  have hp : 0 < |x-2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  rw [Real.dist_eq] at hnear
  have h := H x (lt_of_lt_of_le hnear (min_le_left _ _))
  have hs := (Real.sqrt_lt' (show 0 < ε/3 by positivity)).mpr
    (lt_of_lt_of_le hnear (min_le_right _ _))
  have hpow : |x-2|^(3/(2:ℝ)) = |x-2| * Real.sqrt |x-2| := by
    rw [show (3/(2:ℝ))=1+1/2 by norm_num, Real.rpow_add hp,Real.rpow_one,Real.sqrt_eq_rpow]
  rw [hpow] at h
  rw [Real.dist_eq,sub_zero,slope_def_field,abs_div,div_lt_iff₀ hp]
  nlinarith [mul_lt_mul_of_pos_right hs hp]

/-- P09: extend by zero at both endpoints. The endpoint slope limits produce
the one-sided derivatives required by mathlib's extremum proof of Darboux's theorem. -/
theorem endpointSlopes (f : ℝ → ℝ) (a b c : ℝ)
    (hf : DifferentiableOn ℝ f (Ioo 0 1))
    (h0 : Tendsto (fun x => f x / x) (𝓝[>] 0) (𝓝 a))
    (h1 : Tendsto (fun x => f x / (x-1)) (𝓝[<] 1) (𝓝 b))
    (hc : (a < c ∧ c < b) ∨ (b < c ∧ c < a)) :
    ∃ t ∈ Ioo (0:ℝ) 1, deriv f t = c := by
  let F := fun x => if x ∈ Ioo (0:ℝ) 1 then f x else 0
  let d := fun x => if x = 0 then a else if x = 1 then b else deriv f x
  have left : HasDerivWithinAt F a (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mpr
    apply h0.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with x hx hx'
    have hxi : x ∈ Ioo (0:ℝ) 1 := ⟨hx,hx'⟩
    simp [slope_def_field,F,hxi.1,hxi.2]
  have right : HasDerivWithinAt F b (Iio 1) 1 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (show (1:ℝ) ∉ Iio 1 by simp)).mpr
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))] with x hx hx'
    have hxi : x ∈ Ioo (0:ℝ) 1 := ⟨hx',hx⟩
    simp [slope_def_field,F,hxi.1,hxi.2]
  have allD : ∀ x ∈ Icc (0:ℝ) 1, HasDerivWithinAt F (d x) (Icc 0 1) x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | hl
    · subst x; simpa [d] using left.Ici_of_Ioi.mono (Icc_subset_Ici_self : Icc (0:ℝ) 1 ⊆ Ici 0)
    rcases eq_or_lt_of_le hx.2 with h | hr
    · subst x; simpa [d] using right.Iic_of_Iio.mono (Icc_subset_Iic_self : Icc (0:ℝ) 1 ⊆ Iic 1)
    have hxi : x ∈ Ioo (0:ℝ) 1 := ⟨hl,hr⟩
    have heq : F =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
      exact if_pos hy
    have h := ((hf x hxi).differentiableAt (isOpen_Ioo.mem_nhds hxi)).hasDerivAt
    simpa [d,hl.ne',hr.ne] using (h.congr_of_eventuallyEq heq).hasDerivWithinAt (s := Icc 0 1)
  have hd0 : d 0 = a := by simp [d]
  have hd1 : d 1 = b := by simp [d]
  have hmem : c ∈ d '' Ioo (0:ℝ) 1 := by
    rcases hc with h | h
    · exact exists_hasDerivWithinAt_eq_of_gt_of_lt (by norm_num) allD (hd0.symm ▸ h.1) (hd1.symm ▸ h.2)
    · exact exists_hasDerivWithinAt_eq_of_lt_of_gt (by norm_num) allD (hd0.symm ▸ h.2) (hd1.symm ▸ h.1)
  obtain ⟨t,ht,h⟩ := hmem
  exact ⟨t,ht,by simpa [d,ht.1.ne',ht.2.ne] using h⟩

/-- P09/B: at the right endpoint subtracting g(1) matters. Concrete interior
point for f(x)=x(x-1), c=1/2; the two quotients are genuinely different. -/
theorem endpointQuotientsDiffer :
    let g := fun x : ℝ => x*(x-1)-x/2
    g (1/2) / (1/2-1) ≠ (g (1/2)-g 1) / (1/2-1) := by norm_num

/-- With f(x)=x(x-1), endpoint slopes are -1 and 1. At c=1/2 the
unsubtracted quotient used in P09/B cannot have the claimed limit 1/2. -/
theorem wrongEndpointLimit :
    let f := fun x : ℝ => x*(x-1)
    let g := fun x : ℝ => f x-x/2
    Tendsto (fun x => f x/x) (𝓝[>] 0) (𝓝 (-1)) ∧
    Tendsto (fun x => f x/(x-1)) (𝓝[<] 1) (𝓝 1) ∧
    ¬ Tendsto (fun x => g x/(x-1)) (𝓝[<] 1) (𝓝 (1/2)) := by
  intro f g
  have id0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have id1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hden : Tendsto (fun x : ℝ => x-1) (𝓝[<] 1) (𝓝 0) := by simpa using id1.sub_const 1
  constructor
  · have h : Tendsto (fun x : ℝ => x-1) (𝓝[>] 0) (𝓝 (-1)) := by simpa using id0.sub_const 1
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    dsimp [f]; field_simp [ne_of_gt (show 0 < x from hx)]
  constructor
  · apply id1.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (mul_div_cancel_right₀ _ (sub_ne_zero.mpr (ne_of_lt (show x < 1 from hx)))).symm
  · intro wrong
    have hz : Tendsto (fun x : ℝ => g x/(x-1)*(x-1)) (𝓝[<] 1) (𝓝 0) := by simpa using wrong.mul hden
    have hz' : Tendsto g (𝓝[<] 1) (𝓝 0) := by
      apply hz.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt (show x < 1 from hx)))
    have hg : Continuous g := by dsimp [g,f]; fun_prop
    have bad := tendsto_nhds_unique hz' (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    norm_num [g,f] at bad

end Pilot
