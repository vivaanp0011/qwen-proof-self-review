import Mathlib

/-! P10. Elementary Darboux definition on [0,1]. Any finite partition of a
nondegenerate interval is a leaf or is obtained by adjoining two partitions at a cut.
Both endpoints are included when taking each cell's infimum and supremum. -/
noncomputable section
open Set
namespace Pilot.Darboux

inductive Partition : ℝ → ℝ → Type where
  | leaf {a b : ℝ} (h : a < b) : Partition a b
  | join {a c b : ℝ} : Partition a c → Partition c b → Partition a b

theorem Partition.lt {a b : ℝ} (p : Partition a b) : a < b := by
  induction p with
  | leaf h => exact h
  | join _ _ hl hr => exact hl.trans hr

def lower {a b : ℝ} (p : Partition a b) (f : ℝ → ℝ) : ℝ :=
  match p with
  | .leaf (a := a) (b := b) _ => (b - a) * sInf (f '' Icc a b)
  | .join l r => lower l f + lower r f

def upper {a b : ℝ} (p : Partition a b) (f : ℝ → ℝ) : ℝ :=
  match p with
  | .leaf (a := a) (b := b) _ => (b - a) * sSup (f '' Icc a b)
  | .join l r => upper l f + upper r f

/-- The Darboux criterion for a bounded function. All sums bracket the
integral value, and some pair of bounds is arbitrarily close. -/
def HasRiemannIntegral (f : ℝ → ℝ) (v : ℝ) : Prop :=
  (BddBelow (f '' Icc (0:ℝ) 1) ∧ BddAbove (f '' Icc (0:ℝ) 1)) ∧
  (∀ p : Partition 0 1, lower p f ≤ v ∧ v ≤ upper p f) ∧
  ∀ ε > 0, ∃ p : Partition 0 1, upper p f - lower p f < ε

def DenseZeros (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ x ∈ Ioo a b, f x = 0

theorem allLowerZero {f : ℝ → ℝ} (hn : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hd : DenseZeros f) {a b : ℝ} (p : Partition a b)
    (ha : 0 ≤ a) (hb : b ≤ 1) : lower p f = 0 := by
  induction p with
  | @leaf a b hab =>
    obtain ⟨x,hx,hzero⟩ := hd a b ha hab hb
    have hmin : IsLeast (f '' Icc a b) 0 :=
      ⟨⟨x, ⟨hx.1.le,hx.2.le⟩, hzero⟩, by
        rintro y ⟨z,hz,rfl⟩; exact hn z ⟨ha.trans hz.1,hz.2.trans hb⟩⟩
    simp [lower,hmin.csInf_eq]
  | join l r hl hr =>
    simp [lower, hl ha (r.lt.le.trans hb), hr (ha.trans l.lt.le) hb]

/-- P10/A. The last inference uses integrability essentially. -/
theorem denseIntegralZero {f : ℝ → ℝ} {v : ℝ}
    (hn : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (hd : DenseZeros f)
    (hi : HasRiemannIntegral f v) : v = 0 := by
  have hlow (p : Partition 0 1) := allLowerZero hn hd p (by norm_num) (by norm_num)
  have hv := (hi.2.1 (.leaf zero_lt_one)).1
  rw [hlow] at hv
  by_contra h
  have hp : 0 < v := lt_of_le_of_ne hv (Ne.symm h)
  obtain ⟨p,hsmall⟩ := hi.2.2 v hp
  rw [hlow,sub_zero] at hsmall
  exact (not_lt_of_ge (hi.2.1 p).2) hsmall

def spike (x : ℝ) : ℝ := if x = 1/2 then 1 else 0

theorem spike_nonneg (x : ℝ) : 0 ≤ spike x := by unfold spike; split <;> norm_num
theorem spike_le_one (x : ℝ) : spike x ≤ 1 := by unfold spike; split <;> norm_num

theorem spike_dense : DenseZeros spike := by
  intro a b _ hab _
  by_cases h : (a+b)/2 = 1/2
  · refine ⟨(2*a+b)/3, ⟨by linarith,by linarith⟩, ?_⟩
    exact if_neg (show (2*a+b)/3 ≠ 1/2 by intro h'; linarith)
  · exact ⟨(a+b)/2, ⟨by linarith,by linarith⟩, by exact if_neg h⟩

theorem spike_max : IsGreatest (spike '' Icc (0:ℝ) 1) 1 := by
  refine ⟨⟨1/2,⟨by norm_num,by norm_num⟩,by simp [spike]⟩,?_⟩
  rintro _ ⟨x,_,rfl⟩; exact spike_le_one x

private theorem cellMax {a b : ℝ} {f : ℝ → ℝ} (h : a < b) (v : ℝ)
    (hall : ∀ x ∈ Icc a b, f x ≤ v) (hv : ∃ x ∈ Icc a b, f x = v) :
    upper (.leaf h) f = (b-a)*v := by
  have hm : IsGreatest (f '' Icc a b) v := ⟨hv, by
    rintro _ ⟨x,hx,rfl⟩; exact hall x hx⟩
  simp [upper,hm.csSup_eq]

private theorem upperNonneg {f : ℝ → ℝ} (hl : ∀ x, 0 ≤ f x) (hu : ∀ x, f x ≤ 1)
    {a b : ℝ} (p : Partition a b) : 0 ≤ upper p f := by
  induction p with
  | @leaf a b h =>
    have hs : BddAbove (f '' Icc a b) := ⟨1, by rintro _ ⟨x,_,rfl⟩; exact hu x⟩
    exact mul_nonneg (sub_nonneg.mpr h.le)
      ((hl a).trans (le_csSup hs ⟨a,left_mem_Icc.mpr h.le,rfl⟩))
  | join l r hl hr => exact add_nonneg hl hr

private theorem boundedImage (f : ℝ → ℝ) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    BddBelow (f '' Icc (0:ℝ) 1) ∧ BddAbove (f '' Icc (0:ℝ) 1) := by
  refine ⟨⟨0,?_⟩,⟨1,?_⟩⟩
  · rintro _ ⟨x,_,rfl⟩; exact h0 x
  · rintro _ ⟨x,_,rfl⟩; exact h1 x

theorem spike_integral : HasRiemannIntegral spike 0 := by
  have hlow (p : Partition 0 1) := allLowerZero (fun x _ => spike_nonneg x)
    spike_dense p (by norm_num) (by norm_num)
  refine ⟨boundedImage spike spike_nonneg spike_le_one,
    fun p => ⟨(hlow p).le,upperNonneg spike_nonneg spike_le_one p⟩,?_⟩
  intro ε he
  let d := min (ε/4) (1/4:ℝ)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hε : d ≤ ε/4 := min_le_left _ _
  have hq : d ≤ 1/4 := min_le_right _ _
  let a : ℝ := 1/2-d
  let b : ℝ := 1/2+d
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  have left0 (x : ℝ) (hx : x ∈ Icc 0 a) : spike x = 0 := by
    have hx' := hx.2; dsimp [a] at hx'; exact if_neg (show x ≠ 1/2 by linarith)
  have right0 (x : ℝ) (hx : x ∈ Icc b 1) : spike x = 0 := by
    have hx' := hx.1; dsimp [b] at hx'; exact if_neg (show x ≠ 1/2 by linarith)
  let p : Partition 0 1 := .join (.leaf ha) (.join (.leaf hab) (.leaf hb))
  refine ⟨p,?_⟩
  rw [hlow,sub_zero]
  change upper (.leaf ha) spike + (upper (.leaf hab) spike + upper (.leaf hb) spike) < ε
  rw [cellMax ha 0 (fun x hx => (left0 x hx).le)
        ⟨0,left_mem_Icc.mpr ha.le,left0 0 (left_mem_Icc.mpr ha.le)⟩,
      cellMax hab 1 (fun x _ => spike_le_one x)
        ⟨1/2, ⟨by dsimp [a]; linarith,by dsimp [b]; linarith⟩,by simp [spike]⟩,
      cellMax hb 0 (fun x hx => (right0 x hx).le)
        ⟨1,right_mem_Icc.mpr hb.le,right0 1 (right_mem_Icc.mpr hb.le)⟩]
  dsimp [a,b]; linarith

/-- P10/C's endpoint example. The general part of that response stopped early. -/
def endpointSpike (x : ℝ) : ℝ := if x = 0 then 1 else 0

theorem endpointExample :
    (∀ x, 0 ≤ endpointSpike x ∧ endpointSpike x ≤ 1) ∧ DenseZeros endpointSpike ∧
    IsGreatest (endpointSpike '' Icc (0:ℝ) 1) 1 ∧ HasRiemannIntegral endpointSpike 0 := by
  have bounds (x : ℝ) : 0 ≤ endpointSpike x ∧ endpointSpike x ≤ 1 := by
    unfold endpointSpike; split <;> norm_num
  have dense : DenseZeros endpointSpike := by
    intro a b ha hab _
    exact ⟨(a+b)/2,⟨by linarith,by linarith⟩,if_neg (show (a+b)/2 ≠ 0 by linarith)⟩
  have hmax : IsGreatest (endpointSpike '' Icc (0:ℝ) 1) 1 := by
    refine ⟨⟨0,by simp,by simp [endpointSpike]⟩,?_⟩
    rintro _ ⟨x,_,rfl⟩; exact (bounds x).2
  have low (p : Partition 0 1) := allLowerZero (fun x _ => (bounds x).1) dense p (by norm_num) (by norm_num)
  refine ⟨bounds,dense,hmax,boundedImage endpointSpike (fun x => (bounds x).1) (fun x => (bounds x).2),
    fun p => ⟨(low p).le,upperNonneg (fun x => (bounds x).1) (fun x => (bounds x).2) p⟩,?_⟩
  intro ε he
  let d := min (ε/2) (1/2:ℝ)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have h1 : d < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let p : Partition 0 1 := .join (.leaf hd) (.leaf h1)
  refine ⟨p,?_⟩
  rw [low,sub_zero]
  change upper (.leaf hd) endpointSpike + upper (.leaf h1) endpointSpike < ε
  have right0 (x : ℝ) (hx : x ∈ Icc d 1) : endpointSpike x = 0 :=
    if_neg (ne_of_gt (hd.trans_le hx.1))
  rw [cellMax hd 1 (fun x _ => (bounds x).2) ⟨0,left_mem_Icc.mpr hd.le,by simp [endpointSpike]⟩,
      cellMax h1 0 (fun x hx => (right0 x hx).le)
        ⟨1,right_mem_Icc.mpr h1.le,right0 1 (right_mem_Icc.mpr h1.le)⟩]
  simpa using (show d < ε from (min_le_left _ _).trans_lt (half_lt_self he))

/-- The retry's last available bounds alone are consistent with a positive integral. -/
theorem lowerNonnegativeIsInsufficient (ε : ℝ) (he : 0 < ε) :
    ∃ L I U : ℝ, 0 ≤ L ∧ L ≤ I ∧ I ≤ U ∧ U-L < ε ∧ I ≠ 0 :=
  ⟨1,1,1,by norm_num,le_rfl,le_rfl,by simpa using he,one_ne_zero⟩

end Pilot.Darboux
