module

public import OverfullWork.CaoChenDischarging

@[expose] public section


/-! # The second Cao--Chen discharge and the global average-degree assembly

An eligible vertex has degree at least d and at most C small vertices in
its open radius-two neighbourhood. It sends one unit to every such small
vertex. This safe variant includes both distance one and distance two;
the same C pays its total outflow. We construct the transfers, prove
conservation and both pointwise cases, and assemble the average bound.
Only the unfinished R1 and structural donor estimates remain inputs.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 3000000

noncomputable def distanceTwo (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter fun w => w≠v ∧ ¬G.Adj v w ∧ ∃u,G.Adj v u ∧ G.Adj u w

noncomputable def radiusTwo (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  G.neighborFinset v ∪ distanceTwo G v

noncomputable def lowRecipients (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) : Finset V :=
  (radiusTwo G v).filter fun w => G.degree w<d

noncomputable def radiusTwoSmallCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) : ℕ := (lowRecipients G d v).card

def EligibleDonor (G : SimpleGraph V) [DecidableRel G.Adj] (d C : ℕ) (v : V) : Prop :=
  d≤G.degree v ∧ radiusTwoSmallCount G d v≤C

noncomputable def eligibleDonors (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) (x : V) : Finset V :=
  univ.filter fun v => EligibleDonor G d C v ∧ x∈radiusTwo G v

noncomputable def R2Transfer (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) (v x : V) : ℝ :=
  if EligibleDonor G d C v ∧ x∈lowRecipients G d v then 1 else 0

noncomputable def R2Charge (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (d C : ℕ) (x : V) : ℝ :=
  R1Charge G q x+(∑v : V,R2Transfer G d C v x)-(∑v : V,R2Transfer G d C x v)

/-- A two-edge walk to a distinct vertex suffices, even if its endpoints
are adjacent. This is why sending to N(v) union L(v) needs no extra lemma. -/
theorem mem_radiusTwo_of_two_step (G : SimpleGraph V) [DecidableRel G.Adj]
    {v u x : V} (hvu : G.Adj v u) (hux : G.Adj u x) (hxv : x≠v) :
    x∈radiusTwo G v := by
  by_cases hvx : G.Adj v x
  · exact mem_union_left _ ((mem_neighborFinset G _ _).mpr hvx)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hxv,hvx,u,hvu,hux⟩)

theorem R2Transfer_nonnegative (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) (v x : V) : 0≤R2Transfer G d C v x := by
  unfold R2Transfer
  split_ifs <;> norm_num

theorem sum_R2Transfer_from (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) (v : V) :
    (∑x : V,R2Transfer G d C v x)=
      if EligibleDonor G d C v then (radiusTwoSmallCount G d v:ℝ) else 0 := by
  by_cases he : EligibleDonor G d C v
  · simp only [R2Transfer,he,true_and,if_true]
    rw [←sum_filter]
    have hs : univ.filter (fun x => x∈lowRecipients G d v)=lowRecipients G d v := by
      ext x
      simp only [mem_filter,mem_univ,true_and]
    rw [hs,sum_const,nsmul_eq_mul,mul_one]
    rfl
  · simp only [R2Transfer,he,false_and,if_false,sum_const_zero]

theorem R2_outflow_le_cap (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) (v : V) : (∑x : V,R2Transfer G d C v x)≤(C:ℝ) := by
  rw [sum_R2Transfer_from]
  split_ifs with he
  · exact_mod_cast he.2
  · exact Nat.cast_nonneg _

theorem R2_low_outflow_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) {x : V} (hx : G.degree x<d) : (∑v : V,R2Transfer G d C x v)=0 := by
  have he : ¬EligibleDonor G d C x := fun hh => (not_le_of_gt hx) hh.1
  simp only [sum_R2Transfer_from,if_neg he]

theorem R2_low_inflow_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (d C : ℕ) {x : V} (hx : G.degree x<d) :
    (∑v : V,R2Transfer G d C v x)=(eligibleDonors G d C x).card := by
  simp only [R2Transfer,lowRecipients,mem_filter,hx,and_true]
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  rfl

theorem R2_low_charge_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (d C : ℕ) {x : V} (hx : G.degree x<d) :
    R2Charge G q d C x=R1Charge G q x+(eligibleDonors G d C x).card := by
  unfold R2Charge
  rw [R2_low_outflow_zero G d C hx,R2_low_inflow_eq G d C hx,sub_zero]

theorem total_R2_charge_conserved (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (d C : ℕ) :
    (∑x : V,R2Charge G q d C x)=∑x : V,(G.degree x:ℝ) := by
  simp only [R2Charge,sum_sub_distrib,sum_add_distrib]
  rw [sum_comm (f:=fun x v => R2Transfer G d C v x)]
  have hh := total_charge_conserved G q
  linarith

theorem R1Charge_nonnegative (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0≤q) (x : V) : 0≤R1Charge G q x := by
  by_cases hx : (G.degree x:ℝ)<q
  · rw [low_charge_formula G q x hx]
    exact add_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => donation_nonnegative G q _))
  · exact hq.trans (high_charge_ge_threshold G q x (le_of_not_gt hx))

/-- R2 spends at most C at every vertex, independently of its incoming flow. -/
theorem R2Charge_ge_R1_sub_cap (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (d C : ℕ) (x : V) : R1Charge G q x-(C:ℝ)≤R2Charge G q d C x := by
  have hout := R2_outflow_le_cap G d C x
  have hin : 0≤∑v : V,R2Transfer G d C v x :=
    sum_nonneg (fun v _ => R2Transfer_nonnegative G d C v x)
  unfold R2Charge
  linarith

theorem R2_high_charge_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (d C : ℕ) (x : V) (hR1 : q≤R1Charge G q x) :
    q-(C:ℝ)≤R2Charge G q d C x := by
  have hh := R2Charge_ge_R1_sub_cap G q d C x
  linarith

/-- Each counted eligible donor contributes one unit, while low vertices
send nothing. Source degree equality is not assumed. -/
theorem R2_low_charge_ge_donor_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0≤q) (d C : ℕ) {x : V} (hx : G.degree x<d) :
    ((eligibleDonors G d C x).card:ℝ)≤R2Charge G q d C x := by
  rw [R2_low_charge_eq G q d C hx]
  have hh := R1Charge_nonnegative G q hq x
  linarith

theorem R2_low_charge_ge_required (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0≤q) (d C : ℕ) {x : V} (hx : G.degree x<d)
    (hcount : G.maxDegree-d+1≤(eligibleDonors G d C x).card) :
    (G.maxDegree:ℝ)-(d:ℝ)+1≤R2Charge G q d C x := by
  have hc : G.maxDegree+1≤(eligibleDonors G d C x).card+d := by omega
  have hcR : (G.maxDegree:ℝ)+1≤((eligibleDonors G d C x).card:ℝ)+(d:ℝ) := by exact_mod_cast hc
  have hh := R2_low_charge_ge_donor_count G q hq d C hx
  linarith

/-- Theorem 3 assembly with precisely the two unfinished structural
inputs left visible: the R1 bound on vertices of degree at least d, and
enough distinct eligible donors for every smaller vertex. Everything
after those inputs is an actual charge construction and conservation. -/
theorem average_degree_from_R1_and_R2_donors (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (d C : ℕ) (hd : 1≤d)
    (hcap : (C:ℝ)≤ε*(G.maxDegree:ℝ)/2)
    (hsmall : ((d-1:ℕ):ℝ)≤ε*(G.maxDegree:ℝ))
    (hR1 : ∀x,d≤G.degree x → (1-ε/2)*(G.maxDegree:ℝ)≤
      R1Charge G ((1-ε/2)*(G.maxDegree:ℝ)) x)
    (hdonors : ∀x,G.degree x<d → G.maxDegree-d+1≤(eligibleDonors G d C x).card) :
    (1-ε)*(G.maxDegree:ℝ)*(Fintype.card V:ℝ)≤∑x : V,(G.degree x:ℝ) := by
  let q : ℝ := (1-ε/2)*(G.maxDegree:ℝ)
  have hq : 0≤q := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hsmallR : (d:ℝ)-1≤ε*(G.maxDegree:ℝ) := by
    simpa only [Nat.cast_sub hd,Nat.cast_one] using hsmall
  have hpoint : ∀x,(1-ε)*(G.maxDegree:ℝ)≤R2Charge G q d C x := by
    intro x
    by_cases hx : d≤G.degree x
    · have hh := R2_high_charge_ge G q d C x (hR1 x hx)
      dsimp [q] at hh
      linarith only [hh,hcap]
    · have hxlow : G.degree x<d := lt_of_not_ge hx
      have hh := R2_low_charge_ge_required G q hq d C hxlow (hdonors x hxlow)
      linarith only [hh,hsmallR]
  have hsum := sum_le_sum (fun x (_ : x∈(univ : Finset V)) => hpoint x)
  rw [sum_const,nsmul_eq_mul,card_univ,total_R2_charge_conserved] at hsum
  nlinarith only [hsum]

end OverfullWork.CaoChenDischarging
