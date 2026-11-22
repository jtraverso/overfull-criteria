module

public import OverfullWork.CaoChenClaim53
public import OverfullWork.CaoChenForkAssembly

@[expose] public section


/-! # Cao--Chen's distance-four adjacency theorem

The large neighbourhood alternative constructs a rooted colouring and
distinct fork arms, then constructs the cross-missing colours by Kempe
changes. The existing fork prohibition finally rules it out. Neither a
fork nor the desired cardinality bound is assumed.
-/
namespace OverfullWork.CaoChenDistanceFour
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenForkCounting CaoChenForkSelection CaoChenForkAssembly
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

theorem spine_degree_sum_lower (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbu : c.col b u=some α) (hα : c.IsFree a α) :
    G.maxDegree+2≤G.degree a+G.degree u := by
  have hau : a≠u := by
    intro he
    have hh:=hbu
    rw [←he,c.col_symm,hcm.uncol] at hh
    cases hh
  have hub : u≠b := (c.col_adj hbu).ne.symm
  obtain ⟨haU,hbU⟩ := fan_bau hG hcm hbu hα hau
  have hab := (hcm.ab_facts hG).1
  have hdab : Disjoint (missing c a) (missing c b) := by
    apply Finset.disjoint_left.mpr
    intro γ hγa hγb
    exact hab γ (mem_missing.mp hγa) (mem_missing.mp hγb)
  have hdu : Disjoint (missing c a ∪ missing c b) (missing c u) := by
    apply Finset.disjoint_left.mpr
    intro γ hγ hγu
    rcases mem_union.mp hγ with ha|hb
    · exact haU γ (mem_missing.mp ha) (mem_missing.mp hγu)
    · exact hbU γ (mem_missing.mp hb) (mem_missing.mp hγu)
  have hcount : (missing c a).card+(missing c b).card+(missing c u).card≤G.maxDegree := by
    have hh:=card_le_card (subset_univ ((missing c a ∪ missing c b) ∪ missing c u))
    simpa only [card_union_of_disjoint hdu,card_union_of_disjoint hdab,
      card_univ,Fintype.card_fin] using hh
  have ha:=hcm.card_missing_end (Or.inl rfl : a=a ∨ a=b)
  have hb:=hcm.card_missing_end (Or.inr rfl : b=a ∨ b=b)
  have hu:=hcm.card_missing_other hau.symm hub
  have hdb:=G.degree_le_maxDegree b
  omega

/-- The extremal branch of Proposition A is impossible because its
constructed fork violates the already proved Proposition B. -/
theorem small_two_step_bound (hcrit : IsDeltaCritical G)
    (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ)
    (hroot : RootedAdmissible c a b u) (hd : 2≤d) (hda : G.degree a≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree) :
    (twoStepVertices G u ∩ smallVertices G d).card≤
      (d-1)^2+(d+1)*(d-1)+(d-2) := by
  by_contra hbad
  have hbig : (d-1)^2+(d+1)*(d-1)+(d-2)+1≤
      (twoStepVertices G u ∩ smallVertices G d).card := by omega
  obtain ⟨c₁,hroot₁,z,t,hz,ht,hconfig⟩ :=
    exists_good_anchor_family hcrit c a b u d hroot hd hda hdelta hbig
  obtain ⟨c₂,z',t',ht₀,ht',hseven,α,β₁,β₂,γ₁,γ₂,hfork⟩ :=
    exists_fork_of_good_anchor_family hcrit c₁ a b u d hd hroot₁ hda hdelta z t hz ht hconfig
  have hdeg : G.degree a+G.degree (t 0)+G.degree t'+1≤G.maxDegree := by
    nlinarith only [hda,ht₀,ht',hdelta]
  exact fork_lemma hcrit hseven hdeg c₂ α β₁ β₂ γ₁ γ₂ hfork

/-- Theorem 2, Cao--Chen, JCTB 145 (2020): the coloured neighbour on a
missing-root colour has large degree and at most 2d²−d−2 small vertices
at distance one or two. -/
theorem distance_four_adjacency (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {a b u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbu : c.col b u=some α) (hα : c.IsFree a α)
    (d : ℕ) (hd : 2≤d) (hda : G.degree a≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree) :
    G.maxDegree-d+2≤G.degree u ∧
      (twoStepVertices G u ∩ smallVertices G d).card≤2*d^2-d-2 := by
  have hdegree:=spine_degree_sum_lower hcrit.2.1 hcm hbu hα
  have hbound:=small_two_step_bound hcrit c a b u d ⟨hcm,α,hbu,hα⟩ hd hda hdelta
  have hdD : d≤G.maxDegree := by nlinarith only [hdelta]
  have hsub₁ : d-1+1=d := by omega
  have hsub₂ : d-2+2=d := by omega
  have hid : (d-1)^2+(d+1)*(d-1)+(d-2)+d+2=2*d^2 := by
    nlinarith only [hsub₁,hsub₂]
  constructor <;> omega

end OverfullWork.CaoChenDistanceFour
