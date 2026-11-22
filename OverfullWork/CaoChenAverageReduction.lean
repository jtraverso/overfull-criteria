module

public import OverfullWork.CaoChenDonorCounting
public import OverfullWork.CaoChenDistanceFour

@[expose] public section


/-! # Discharging the structural donor input with Cao--Chen Theorem 2

The distance-four theorem is proved, not assumed. It supplies the actual
eligible donors in R2. Thus the only unfinished structural input to the
average-degree assembly is the high-vertex R1 estimate from Theorem 5.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenForkCounting
open scoped Classical
universe u
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 3000000

theorem radiusTwo_eq_twoStepVertices (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    radiusTwo G v=twoStepVertices G v := by
  ext x
  simp only [radiusTwo,distanceTwo,twoStepVertices,mem_union,mem_filter,mem_univ,
    true_and,mem_erase,mem_biUnion,mem_neighborFinset]
  constructor
  · rintro (h | ⟨hne,hnot,hwalk⟩)
    · exact ⟨h.ne.symm,Or.inl h⟩
    · exact ⟨hne,Or.inr hwalk⟩
  · rintro ⟨hne,h | hwalk⟩
    · exact Or.inl h
    · by_cases h : G.Adj v x
      · exact Or.inl h
      · exact Or.inr ⟨hne,h,hwalk⟩

theorem lowRecipients_subset_twoStepSmall (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) : lowRecipients G d v⊆twoStepVertices G v∩smallVertices G d := by
  intro x hx
  obtain ⟨hxR,hxd⟩ := mem_filter.mp hx
  rw [radiusTwo_eq_twoStepVertices] at hxR
  exact mem_inter.mpr ⟨hxR,mem_filter.mpr ⟨mem_univ _,hxd.le⟩⟩

/-- The proved distance-four adjacency theorem supplies eligibility,
including the donor's degree threshold and the actual recipient cap. -/
theorem eligibleDonor_of_distance_four
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {a b v : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbv : c.col b v=some α) (hα : c.IsFree a α)
    (d : ℕ) (hd : 2≤d) (hda : G.degree a≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree) :
    EligibleDonor G d (2*d^2-d-2) v := by
  obtain ⟨hdegree,hcount⟩ := CaoChenDistanceFour.distance_four_adjacency
    hcrit hcm hbv hα d hd hda hdelta
  have hdD : d≤G.maxDegree := by nlinarith only [hdelta]
  have htwod : 2*d≤G.maxDegree+2 := by nlinarith only [hdelta]
  refine ⟨by omega,?_⟩
  exact (card_le_card (lowRecipients_subset_twoStepSmall G d v)).trans hcount

/-- The remaining R1 estimate is the only structural hypothesis here.
Theorem 2 constructs the required R2 donors through their actual edge
colours; all threshold and charge computations are discharged. -/
theorem critical_average_from_R1_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcrit : IsDeltaCritical G)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (d : ℕ) (hd : 2≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree)
    (hcap : ((2*d^2-d-2:ℕ):ℝ)≤ε*(G.maxDegree:ℝ)/2)
    (hsmall : ((d-1:ℕ):ℝ)≤ε*(G.maxDegree:ℝ))
    (hR1 : ∀v,d≤G.degree v → (1-ε/2)*(G.maxDegree:ℝ)≤
      R1Charge G ((1-ε/2)*(G.maxDegree:ℝ)) v) :
    (1-ε)*(G.maxDegree:ℝ)*(Fintype.card V:ℝ)≤∑v : V,(G.degree v:ℝ) := by
  have : Nonempty V := hcrit.1.nonempty
  have hDpos : 1<G.maxDegree := by nlinarith only [hdelta,hd]
  have hcard : 1<Fintype.card V := lt_trans hDpos G.maxDegree_lt_card_verts
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  have hactive : ∀v,0<G.degree v := fun v => hcrit.1.preconnected.degree_pos_of_nontrivial v
  apply critical_average_from_R1_and_coloured_neighbours hcrit hactive ε hε hεone d
    (2*d^2-d-2) (by omega) hcap hsmall hR1
  intro a b c hda hab hcm α hα v hbv
  exact eligibleDonor_of_distance_four hcrit hcm hbv hα d hd hda.le hdelta

/-- It suffices to finish precisely the eventual high-vertex R1 estimate.
This theorem does not assert that estimate; Theorem 5 remains unfinished.
The other structural and numerical inputs are proved above or chosen
explicitly here, with every threshold preceding the graph. -/
theorem averageBound_of_eventual_R1
    (hR1 : ∀η : ℝ,0<η → η<1 → ∃d N : ℕ,2≤d ∧
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        IsDeltaCritical G → N≤G.maxDegree → ∀v,d≤G.degree v →
        (1-η)*(G.maxDegree:ℝ)≤R1Charge G ((1-η)*(G.maxDegree:ℝ)) v) :
    CriticalAverageDegree.AverageBound.{u} := by
  intro ε hε
  by_cases hεone : ε<1
  · obtain ⟨d,N,hd,hR1N⟩ := hR1 (ε/2) (by positivity) (by linarith)
    let C := 2*d^2-d-2
    obtain ⟨B,hB⟩ := exists_nat_gt (max ((2*(C:ℝ))/ε) ((d:ℝ)/ε))
    refine ⟨max N (max ((d+1)*(d+3)) B),?_⟩
    intro W _ _ G _ hcrit hthreshold
    have hN : N≤G.maxDegree := (le_max_left _ _).trans hthreshold
    have hpoly : (d+1)*(d+3)≤G.maxDegree :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hthreshold)
    have hBD : B≤G.maxDegree :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hthreshold)
    have hBDR : (B:ℝ)≤(G.maxDegree:ℝ) := by exact_mod_cast hBD
    have hcap : (C:ℝ)≤ε*(G.maxDegree:ℝ)/2 := by
      have hh : 2*(C:ℝ)/ε<(B:ℝ) := lt_of_le_of_lt (le_max_left _ _) hB
      have hm := (div_lt_iff₀ hε).mp hh
      have hscale := mul_le_mul_of_nonneg_left hBDR hε.le
      nlinarith only [hm,hscale]
    have hsmall : ((d-1:ℕ):ℝ)≤ε*(G.maxDegree:ℝ) := by
      have hh : (d:ℝ)/ε<(B:ℝ) := lt_of_le_of_lt (le_max_right _ _) hB
      have hm := (div_lt_iff₀ hε).mp hh
      have hscale := mul_le_mul_of_nonneg_left hBDR hε.le
      have hsub : ((d-1:ℕ):ℝ)≤(d:ℝ) := by exact_mod_cast Nat.sub_le d 1
      nlinarith only [hm,hscale,hsub]
    have hh := critical_average_from_R1_bound G hcrit ε hε hεone d hd hpoly hcap hsmall
      (hR1N G hcrit hN)
    simpa only [Nat.cast_sum] using hh
  · refine ⟨0,?_⟩
    intro W _ _ G _ hcrit _
    have hcoeff : 1-ε≤0 := by linarith
    have hn : (0:ℝ)≤(G.maxDegree:ℝ)*(Fintype.card W:ℝ) := by positivity
    have hleft : (1-ε)*(G.maxDegree:ℝ)*(Fintype.card W:ℝ)≤0 := by
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hcoeff hn]
    have hsum : (0:ℝ)≤((∑v : W,G.degree v:ℕ):ℝ) := Nat.cast_nonneg _
    exact hleft.trans hsum

end OverfullWork.CaoChenDischarging
