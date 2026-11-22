module

public import OverfullWork.CriticalSpectrum
public import OverfullWork.CriticalAverageDegreeTarget

@[expose] public section


/-! # The R1 discharge and the first case of Cao--Chen Claim 3.1

Each vertex strictly above q distributes its surplus equally among its
neighbours strictly below q. We prove conservation, the charge bound at
high vertices, and the actual near-full-high-neighbour case of Claim 3.1
in Cao--Chen (2018). The other cases of Theorem 5 remain to be proved.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 3000000

noncomputable def lowCount (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y : V) : ℕ :=
  ((G.neighborFinset y).filter fun x => (G.degree x:ℝ)<q).card

noncomputable def highCount (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y : V) : ℕ :=
  ((G.neighborFinset y).filter fun x => q≤(G.degree x:ℝ)).card

noncomputable def donation (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y : V) : ℝ :=
  if q<(G.degree y:ℝ) then ((G.degree y:ℝ)-q)/(lowCount G q y:ℝ) else 0

noncomputable def transfer (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y x : V) : ℝ :=
  if G.Adj y x ∧ (G.degree x:ℝ)<q then donation G q y else 0

noncomputable def R1Charge (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (x : V) : ℝ :=
  (G.degree x:ℝ)+(∑y : V,transfer G q y x)-(∑y : V,transfer G q x y)

theorem lowCount_add_highCount (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y : V) :
    lowCount G q y+highCount G q y=G.degree y := by
  simpa only [lowCount,highCount,not_lt,card_neighborFinset_eq_degree] using
    card_filter_add_card_filter_not (s:=G.neighborFinset y) (fun x => (G.degree x:ℝ)<q)

theorem donation_nonnegative (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y : V) :
    0≤donation G q y := by
  unfold donation
  split_ifs with h
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact le_rfl

theorem transfer_nonnegative (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y x : V) :
    0≤transfer G q y x := by
  unfold transfer
  split_ifs
  · exact donation_nonnegative G q y
  · exact le_rfl

theorem sum_transfer_from (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (y : V) :
    (∑x : V,transfer G q y x)=(lowCount G q y:ℝ)*donation G q y := by
  unfold transfer
  rw [←sum_filter]
  have hs : univ.filter (fun x => G.Adj y x ∧ (G.degree x:ℝ)<q)=
      (G.neighborFinset y).filter (fun x => (G.degree x:ℝ)<q) := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
  rw [hs,sum_const,nsmul_eq_mul]
  rfl

theorem total_charge_conserved (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) :
    (∑x : V,R1Charge G q x)=∑x : V,(G.degree x:ℝ) := by
  simp only [R1Charge,sum_sub_distrib,sum_add_distrib]
  rw [sum_comm (f:=fun x y => transfer G q y x)]
  ring

theorem high_charge_ge_threshold (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (x : V)
    (hx : q≤(G.degree x:ℝ)) : q≤R1Charge G q x := by
  have hin : (∑y : V,transfer G q y x)=0 := by
    apply sum_eq_zero
    intro y _
    simp only [transfer,not_lt.mpr hx,and_false,if_false]
  unfold R1Charge
  rw [hin,sum_transfer_from]
  by_cases hh : q<(G.degree x:ℝ)
  · rw [donation,if_pos hh]
    by_cases hz : lowCount G q x=0
    · simp only [hz,Nat.cast_zero,zero_mul,add_zero,sub_zero]
      exact hx
    · have hr : (lowCount G q x:ℝ)≠0 := by exact_mod_cast hz
      rw [mul_div_cancel₀ _ hr]
      linarith
  · simp only [donation,if_neg hh,mul_zero,add_zero,sub_zero]
    exact hx

theorem low_charge_formula (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (x : V)
    (hx : (G.degree x:ℝ)<q) :
    R1Charge G q x=(G.degree x:ℝ)+∑y∈G.neighborFinset x,donation G q y := by
  have hout : (∑y : V,transfer G q x y)=0 := by
    rw [sum_transfer_from]
    simp only [donation,if_neg (by linarith : ¬q<(G.degree x:ℝ)),mul_zero]
  have hin : (∑y : V,transfer G q y x)=∑y∈G.neighborFinset x,donation G q y := by
    unfold transfer
    simp only [hx,and_true]
    rw [←sum_filter]
    have hs : univ.filter (fun y => G.Adj y x)=G.neighborFinset x := by
      ext y
      simp only [mem_filter,mem_univ,true_and,mem_neighborFinset,G.adj_comm]
    rw [hs]
  unfold R1Charge
  rw [hout,hin,sub_zero]

/-- A low neighbour makes the R1 denominator strictly positive. -/
theorem lowCount_positive_of_low_neighbour (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) {x y : V} (hxy : G.Adj x y) (hx : (G.degree x:ℝ)<q) :
    0<lowCount G q y := by
  apply card_pos.mpr
  exact ⟨x,mem_filter.mpr ⟨(mem_neighborFinset G _ _).mpr hxy.symm,hx⟩⟩

/-- The first structural case of Claim 3.1: when every neighbour has
nearly Delta high neighbours, the actual R1 charge already reaches q.
The hypothesis concerns explicit finite degree counts, not charges. -/
theorem charge_ge_of_near_full_high_counts (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (s : ℕ) (hs : 0<s)
    (hsmall : (s:ℝ)≤ε^2*(G.maxDegree:ℝ)) (x : V)
    (hxlo : ε*(G.maxDegree:ℝ)≤(G.degree x:ℝ))
    (hxhi : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hhigh : ∀y,G.Adj x y → (G.maxDegree:ℝ)-(s:ℝ)≤
      (highCount G ((1-ε)*(G.maxDegree:ℝ)) y:ℝ)) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q : ℝ := (1-ε)*(G.maxDegree:ℝ)
  have hsR : (0:ℝ)<(s:ℝ) := by exact_mod_cast hs
  have hD : (0:ℝ)<(G.maxDegree:ℝ) := by
    nlinarith only [hxhi,(Nat.cast_nonneg (G.degree x) : (0:ℝ)≤(G.degree x:ℝ)),
      (Nat.cast_nonneg G.maxDegree : (0:ℝ)≤(G.maxDegree:ℝ)),hε]
  have hposprod : 0<ε*(1-ε)*(G.maxDegree:ℝ) := by positivity
  have hroom : 0<(G.maxDegree:ℝ)-(s:ℝ)-q := by
    dsimp [q]
    nlinarith only [hsmall,hposprod]
  have hdon : ∀y∈G.neighborFinset x,
      ((G.maxDegree:ℝ)-(s:ℝ)-q)/(s:ℝ)≤donation G q y := by
    intro y hy
    have hxy := (mem_neighborFinset G _ _).mp hy
    have hh := hhigh y hxy
    have hc := lowCount_add_highCount G q y
    have hdy := G.degree_le_maxDegree y
    have hcR : (lowCount G q y:ℝ)+(highCount G q y:ℝ)=(G.degree y:ℝ) := by
      exact_mod_cast hc
    have hdyR : (G.degree y:ℝ)≤(G.maxDegree:ℝ) := by exact_mod_cast hdy
    have hcnt : (lowCount G q y:ℝ)≤(s:ℝ) := by change _≤_ at hh;linarith
    have hmin : (G.maxDegree:ℝ)-(s:ℝ)≤(G.degree y:ℝ) := by
      have hp : (0:ℝ)≤(lowCount G q y:ℝ) := Nat.cast_nonneg _
      linarith
    have hsource : q<(G.degree y:ℝ) := by linarith
    have hlowpos : (0:ℝ)<(lowCount G q y:ℝ) := by
      exact_mod_cast lowCount_positive_of_low_neighbour G q hxy hxhi
    rw [donation,if_pos hsource]
    apply (div_le_div_iff₀ hsR hlowpos).mpr
    have hm := mul_le_mul_of_nonneg_left hcnt hroom.le
    nlinarith only [hm,hmin,hsR]
  have hsum := sum_le_sum hdon
  rw [sum_const,nsmul_eq_mul,card_neighborFinset_eq_degree] at hsum
  have htarget : q≤(G.degree x:ℝ)*(((G.maxDegree:ℝ)-(s:ℝ)-q)/(s:ℝ)) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hsR).mpr
    have hm := mul_le_mul_of_nonneg_right hxlo hroom.le
    have hbudget := mul_le_mul_of_nonneg_right hsmall hD.le
    dsimp [q] at *
    nlinarith only [hm,hbudget]
  rw [low_charge_formula G q x hxhi]
  change q≤_
  have hdnonneg : (0:ℝ)≤(G.degree x:ℝ) := Nat.cast_nonneg _
  linarith

/-- The structural hypothesis in the preceding case is discharged by
the actual minimum high-neighbour count, exactly as in Claim 3.1. -/
theorem charge_ge_of_minimum_high_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) {x y : V} (hxy : G.Adj x y)
    (hxlo : ε*(G.maxDegree:ℝ)≤(G.degree x:ℝ))
    (hxhi : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hmin : ∀z,G.Adj x z → highCount G ((1-ε)*(G.maxDegree:ℝ)) y≤
      highCount G ((1-ε)*(G.maxDegree:ℝ)) z)
    (hsmall : ((G.maxDegree-highCount G ((1-ε)*(G.maxDegree:ℝ)) y:ℕ):ℝ)≤
      ε^2*(G.maxDegree:ℝ)) :
    (1-ε)*(G.maxDegree:ℝ)≤R1Charge G ((1-ε)*(G.maxDegree:ℝ)) x := by
  let q : ℝ := (1-ε)*(G.maxDegree:ℝ)
  let s := G.maxDegree-highCount G q y
  have hc := lowCount_add_highCount G q y
  have hlow := lowCount_positive_of_low_neighbour G q hxy hxhi
  have hd := G.degree_le_maxDegree y
  have hcount : highCount G q y≤G.maxDegree := by omega
  have hs : 0<s := by dsimp [s];omega
  apply charge_ge_of_near_full_high_counts G ε hε hεone s hs hsmall x hxlo hxhi
  intro z hxz
  have hh := hmin z hxz
  have he : s+highCount G q y=G.maxDegree := Nat.sub_add_cancel hcount
  have heR : (s:ℝ)+(highCount G q y:ℝ)=(G.maxDegree:ℝ) := by exact_mod_cast he
  have hhR : (highCount G q y:ℝ)≤(highCount G q z:ℝ) := by exact_mod_cast hh
  change (G.maxDegree:ℝ)-(s:ℝ)≤(highCount G q z:ℝ)
  linarith

end OverfullWork.CaoChenDischarging
