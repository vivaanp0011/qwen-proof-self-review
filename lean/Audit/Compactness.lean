import Mathlib

noncomputable section
open Filter Set Function
open scoped Topology
namespace Pilot

/-- P03, following the first answer's triangle through the cutoff. Functions are
represented on all reals, with continuity and the conclusion restricted to the half-line. -/
theorem halfLineUniform (f : ℝ → ℝ) (L : ℝ) (hc : ContinuousOn f (Ici 0))
    (ht : Tendsto f atTop (𝓝 L)) : UniformContinuousOn f (Ici 0) := by
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε he
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ht) (ε/4) (by positivity))
  let M := max 0 A
  have hM : 0 ≤ M := le_max_left _ _
  have tail {x y : ℝ} (hx : M ≤ x) (hy : M ≤ y) : dist (f x) (f y) < ε/2 := by
    have h1 := hA x ((le_max_right _ _).trans hx)
    have h2 := hA y ((le_max_right _ _).trans hy)
    have htri := dist_triangle (f x) L (f y)
    rw [dist_comm L (f y)] at htri; linarith
  have hK := isCompact_Icc.uniformContinuousOn_of_continuous
    (hc.mono (show Icc 0 M ⊆ Ici 0 from fun _ h => h.1))
  obtain ⟨δ,hδ,hK⟩ := Metric.uniformContinuousOn_iff.mp hK (ε/2) (half_pos he)
  have ordered {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hnear : dist x y < δ) :
      dist (f x) (f y) < ε := by
    by_cases hy : y ≤ M
    · exact (hK x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hnear).trans (half_lt_self he)
    by_cases hmx : M ≤ x
    · exact (tail hmx (hmx.trans hxy)).trans (half_lt_self he)
    have hxM := le_of_not_ge hmx
    have hMy := le_of_not_ge hy
    have hd : dist x M ≤ dist x y := by
      rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxM),
          abs_of_nonpos (sub_nonpos.mpr hxy)]; linarith
    have h1 := hK x ⟨hx,hxM⟩ M ⟨hM,le_rfl⟩ (hd.trans_lt hnear)
    have h2 := tail (le_rfl : M ≤ M) hMy
    linarith [dist_triangle (f x) (f M) (f y)]
  refine ⟨δ,hδ,fun x hx y hy hxy => ?_⟩
  rcases le_total x y with h | h
  · exact ordered hx h hxy
  · simpa only [dist_comm (f y) (f x)] using ordered hy h (by rwa [dist_comm])

/-- Extra check of P03/A's different crossing argument. -/
theorem crossingInLargerCompact {x y M : ℝ} (h : 0 ≤ x) (hx : x < M) (hy : M < y)
    (hxy : |x-y| < 1) : x ∈ Icc 0 (M+1) ∧ y ∈ Icc 0 (M+1) := by
  obtain ⟨l,r⟩ := abs_lt.mp hxy
  exact ⟨⟨h,by linarith⟩,⟨by linarith,by linarith⟩⟩

/-- P05, using the exact subsequence/closed-tail argument of both answers. -/
theorem nestedCompact (K : ℕ → Set ℝ) (decr : Antitone K) (hc : ∀ n, IsCompact (K n))
    (hne : ∀ n, (K n).Nonempty) : (⋂ n, K n).Nonempty := by
  choose x hx using hne
  obtain ⟨a,_,i,hi,hlim⟩ := (hc 0).tendsto_subseq
    (fun n => decr (Nat.zero_le n) (hx n))
  refine ⟨a,mem_iInter.mpr fun m => (hc m).isClosed.mem_of_tendsto hlim ?_⟩
  filter_upwards [eventually_ge_atTop m] with n hn
  exact decr (hn.trans (hi.id_le n)) (hx (i n))

theorem closedRays : (∀ n : ℕ, IsClosed (Ici (n:ℝ)) ∧ (Ici (n:ℝ)).Nonempty) ∧
    Antitone (fun n : ℕ => Ici (n:ℝ)) ∧ (⋂ n : ℕ, Ici (n:ℝ)) = ∅ := by
  refine ⟨fun n => ⟨isClosed_Ici,⟨(n:ℝ),mem_Ici.mpr le_rfl⟩⟩,fun i j hij => Ici_subset_Ici.mpr (by exact_mod_cast hij),?_⟩
  apply Set.eq_empty_of_forall_not_mem
  intro x hx
  obtain ⟨n,hn⟩ := exists_nat_gt x
  exact (not_le_of_gt hn) ((mem_iInter.mp hx) n)

/-- Full-sequence observation law implies the same law at chosen increasing indices.
Fill all unused indices with the limit point. -/
theorem selectedObservation {X : Type*} [PseudoMetricSpace X] {F : ℕ → X → ℝ} {f : X → ℝ}
    (obs : ∀ (u : ℕ → X) (x : X), Tendsto u atTop (𝓝 x) →
      Tendsto (fun n => F n (u n)) atTop (𝓝 (f x)))
    {i : ℕ → ℕ} (hi : StrictMono i) {y : ℕ → X} {x : X} (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun k => F (i k) (y k)) atTop (𝓝 (f x)) := by
  let z := Function.extend i y (fun _ => x)
  have hz : Tendsto z atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.mpr
    intro ε he
    obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp hy ε he
    refine ⟨i K,fun n hn => ?_⟩
    by_cases h : ∃ k, i k = n
    · obtain ⟨k,rfl⟩ := h; dsimp [z]; rw [hi.injective.extend_apply]
      exact hK k (hi.le_iff_le.mp hn)
    · dsimp [z]; rw [Function.extend_apply' _ _ _ h]; simpa using he
  simpa only [Function.comp_def,z,hi.injective.extend_apply] using (obs z x hz).comp hi.tendsto_atTop

/-- P08 on any compact metric space, in particular X = [0,1]. -/
theorem movingObservations {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (F : ℕ → X → ℝ) (f : X → ℝ) (hf : Continuous f)
    (obs : ∀ (u : ℕ → X) (x : X), Tendsto u atTop (𝓝 x) →
      Tendsto (fun n => F n (u n)) atTop (𝓝 (f x))) : TendstoUniformly F f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε he
  by_contra h
  have hbad : ∃ᶠ n in atTop, ∃ x : X, ε ≤ dist (f x) (F n x) := by
    simpa only [Filter.Frequently,not_exists,not_le] using h
  obtain ⟨i,hi,hbad⟩ := extraction_of_frequently_atTop hbad
  choose u hu using hbad
  obtain ⟨x,_,j,hj,hx⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (u n))
  have ha := selectedObservation obs (hi.comp hj) hx
  have hb := (hf.continuousAt.tendsto.comp hx)
  have hd : Tendsto (fun k => dist (f (u (j k))) (F (i (j k)) (u (j k)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hb.dist ha
  have le0 : ε ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hd (fun k => hu (j k))
  exact (not_le_of_gt he) le0

/-- P08/B's real-line example. At index zero division is defined as zero;
dropping that first index recovers the usual x/n for positive indices. -/
theorem unboundedExample :
    (∀ n : ℕ, Continuous (fun x : ℝ => x/(n:ℝ))) ∧
    (∀ (u : ℕ → ℝ) (x : ℝ), Tendsto u atTop (𝓝 x) →
      Tendsto (fun n => u n/(n:ℝ)) atTop (𝓝 0)) ∧
    ¬ TendstoUniformly (fun (n:ℕ) (x:ℝ) => x/(n:ℝ)) (fun _ => 0) atTop := by
  refine ⟨fun _ => continuous_id.div_const _,fun _ _ h => h.div_atTop tendsto_natCast_atTop_atTop,?_⟩
  intro h
  obtain ⟨n,hnpos,hn⟩ := ((eventually_ge_atTop 1).and
    (Metric.tendstoUniformly_iff.mp h 1 zero_lt_one)).exists
  have hzero : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simpa [Real.dist_eq,hzero] using hn (n:ℝ)

/-- P08's reference example. The tent moves to the right, so a convergent
sequence eventually misses it. Its value at its own center is always one. -/
def tent (n : ℕ) (x : ℝ) := max 0 (1 - |x-(n:ℝ)|)

theorem movingTent :
    (∀ n, Continuous (tent n)) ∧
    (∀ (u : ℕ → ℝ) (x : ℝ), Tendsto u atTop (𝓝 x) →
      Tendsto (fun n => tent n (u n)) atTop (𝓝 0)) ∧
    ¬ TendstoUniformly tent (fun _ => 0) atTop := by
  refine ⟨fun n => continuous_const.max (continuous_const.sub
    (continuous_id.sub continuous_const).abs),?_,?_⟩
  · intro u x hu
    apply tendsto_const_nhds.congr'
    have hb : ∀ᶠ n in atTop, u n < x+1 := hu (Iio_mem_nhds (lt_add_one x))
    have hN : ∀ᶠ n : ℕ in atTop, x+2 ≤ (n:ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    filter_upwards [hb,hN] with n hn hn'
    dsimp [tent]
    rw [abs_of_nonpos (by linarith : u n-(n:ℝ) ≤ 0),max_eq_left (by linarith)]
  · intro h
    obtain ⟨n,hn⟩ := (Metric.tendstoUniformly_iff.mp h 1 zero_lt_one).exists
    simpa [tent,Real.dist_eq] using hn (n:ℝ)

end Pilot
