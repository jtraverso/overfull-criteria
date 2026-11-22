module

public import OverfullWork.ResidualOverfullLocalization

@[expose] public section


/-! # Almost-overfull budgets certify compatibility of an actual layer

An overfull odd set in a degree-two-lowered residue spends the original
odd-set budget through the actual missing degree of the layer. The star
localization theorem bounds its complementary edges. Thus a test on the
original graph, rather than an assumed no-overfull residue, suffices.
-/
namespace OverfullWork.AlmostOverfullLayerCompatibility
open SimpleGraph Finset OddCutDeficit NearTightOddSetGeometry
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- The original and residual deficits differ by the exact missing
layer degree. All subtraction identities have their degree bounds. -/
theorem deficitMass_eq_after_layer (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hLG : L≤G)
    (hD : 2≤G.maxDegree) (hL : ∀v,L.degree v≤2)
    (hR : ∀v,(G\L).degree v≤G.maxDegree-2) (X : Finset V) :
    deficitMass G G.maxDegree X=
      deficitMass (G\L) (G.maxDegree-2) X+∑v∈X,(2-L.degree v) := by
  unfold deficitMass
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro v _
  have hs:=MaximumMatching.degree_sdiff_add_of_le G L hLG v
  have hg:=G.degree_le_maxDegree v
  have hl:=hL v
  have hr:=hR v
  omega

/-- The actual layer and its residue partition every original cut. -/
theorem cutEdges_eq_residue_add_layer (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hLG : L≤G) (X : Finset V) :
    cutEdges G X=cutEdges (G\L) X+cutEdges L X := by
  have he:crossingEdges G X=crossingEdges (G\L) X∪crossingEdges L X := by
    ext p
    simp only [crossingEdges,mem_union,mem_filter,sdiff_adj]
    constructor
    · rintro ⟨hp,hG⟩
      by_cases hL:L.Adj p.1 p.2
      · exact Or.inr ⟨hp,hL⟩
      · exact Or.inl ⟨hp,hG,hL⟩
    · rintro (⟨hp,hG,_⟩|⟨hp,hL⟩)
      · exact ⟨hp,hG⟩
      · exact ⟨hp,hLG hL⟩
  have hd:Disjoint (crossingEdges (G\L) X) (crossingEdges L X) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (mem_filter.mp hp).2.2 (mem_filter.mp hq).2
  unfold cutEdges
  rw [he,card_union_of_disjoint hd]

/-- A degree-two layer spends at most twice the complement size on its cut. -/
theorem cutEdges_layer_le_twice_complement (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : ∀v,L.degree v≤2) (X : Finset V) : cutEdges L X≤2*Xᶜ.card := by
  have hi:=internal_cut_identity L Xᶜ
  rw [cutEdges_compl] at hi
  have hs:(∑v∈Xᶜ,L.degree v)≤2*Xᶜ.card:=by
    calc
      _ ≤ ∑_v∈Xᶜ,2 := sum_le_sum (fun v _ => hL v)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- A star, including isolated vertices and the empty set, has at most
as many internal edges as vertices. -/
theorem internalEdges_le_card_of_star (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V)
    (hstar : Y=∅ ∨ ∃v∈Y,∀u∈Y,∀w∈Y,G.Adj u w → u=v ∨ w=v) :
    internalEdges G Y≤Y.card := by
  rcases hstar with he|⟨v,hv,hs⟩
  · have hh:=twice_internalEdges_le G Y
    rw [he,card_empty] at hh ⊢
    omega
  · let K:=G.induce (Y : Set V)
    let c : Y:=⟨v,hv⟩
    have hc:∀u w,K.Adj u w → u∈({c}:Finset Y) ∨ w∈({c}:Finset Y) := by
      intro u w huw
      rcases hs u.val u.property w.val w.property huw with hu|hw
      · exact Or.inl (mem_singleton.mpr (Subtype.ext hu))
      · exact Or.inr (mem_singleton.mpr (Subtype.ext hw))
    have hh:=edge_count_le_cover_degree_sum K {c} hc
    rw [sum_singleton] at hh
    have hd:K.degree c≤Y.card:=by simpa using (K.degree_lt_card_verts c).le
    rw [internalEdges,G.card_filter_edgeFinset_toFinset_subset Y]
    exact hh.trans hd

/-- The original graph's almost-overfull budget is controlled by the
actual layer defect and by the size of the star complement. -/
theorem budget_of_residual_overfull (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hLG : L≤G)
    (hL : ∀v,L.degree v≤2) (hD : 2≤G.maxDegree)
    (hR : (G\L).maxDegree=G.maxDegree-2)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X)
    (hstar : Xᶜ=∅ ∨ ∃v∈Xᶜ,∀u∈Xᶜ,∀w∈Xᶜ,G.Adj u w → u=v ∨ w=v)
    (M : ℕ) (hMissing : (∑v:V,(2-L.degree v))≤M) :
    deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+M+4*Xᶜ.card := by
  have hRdeg:∀v,(G\L).degree v≤G.maxDegree-2:=by
    intro v
    rw [←hR]
    exact (G\L).degree_le_maxDegree v
  have hdef:=deficitMass_eq_after_layer G L hLG hD hL hRdeg X
  have hmiss:(∑v∈X,(2-L.degree v))≤M :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans hMissing
  have hcut:=cutEdges_eq_residue_add_layer G L hLG X
  have hLayer:=cutEdges_layer_le_twice_complement L hL X
  have hstarCount:=internalEdges_le_card_of_star G Xᶜ hstar
  have hsum:=internal_cut_identity G Xᶜ
  rw [cutEdges_compl] at hsum
  have hbudget:=cut_deficit_le_of_near_tight (G\L) (G.maxDegree-2) 0 hRdeg X hodd
    (by omega)
  omega

/-- A tiny complement gives the displayed uniform stopping budget. -/
theorem budget_of_small_complement (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hLG : L≤G)
    (hL : ∀v,L.degree v≤2) (hD : 2≤G.maxDegree)
    (hR : (G\L).maxDegree=G.maxDegree-2)
    (X : Finset V) (hodd : Odd X.card)
    (hof : (G.maxDegree-2)*(X.card/2)< internalEdges (G\L) X)
    (hstar : Xᶜ=∅ ∨ ∃v∈Xᶜ,∀u∈Xᶜ,∀w∈Xᶜ,G.Adj u w → u=v ∨ w=v)
    (M k : ℕ) (hMissing : (∑v:V,(2-L.degree v))≤M) (htiny : Xᶜ.card≤2*k) :
    deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+M+8*k := by
  have hh:=budget_of_residual_overfull G L hLG hL hD hR X hodd hof hstar M hMissing
  omega

/-- This property concerns only the original graph and a numerical budget. -/
def HasOddAlmostOverfullSet (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℕ) : Prop :=
  ∃X:Finset V,Odd X.card ∧
    deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B

universe u

/-- Every actual overfull residue forces an almost-overfull set in the
original graph. G1 constructs the localization and its star complement;
those structural conclusions are not assumed as inputs. -/
theorem above_half_overfull_residue_implies_almost (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let k:=Fintype.card W/(4096*q^2)
        ∀(L : SimpleGraph W) [DecidableRel L.Adj],L≤G → L.maxDegree≤2 →
          (G\L).maxDegree=G.maxDegree-2 →
          ∀M:ℕ,(∑v:W,(2-L.degree v))≤M →
            (G\L).HasOverfullSubgraph → HasOddAlmostOverfullSet G (M+8*k) := by
  obtain ⟨q,hq,N,hN⟩:=ResidualOverfullLocalization.above_half_residual_overfull_stop.{u} ε hε
  refine ⟨q,hq,max N 4,?_⟩
  intro W _ _ G _ hn hc hdense
  obtain ⟨_,hstop⟩:=hN G ((le_max_left _ _).trans hn) hc hdense
  dsimp only
  intro L _ hLG hL hR M hMissing hOF
  obtain ⟨X,hodd,hof,_,_,htiny,_,hstar⟩:=hstop L hLG hL hR hOF
  have hD:2≤G.maxDegree:=by
    have hn4:4≤Fintype.card W:=(le_max_right _ _).trans hn
    have hn4R:(4:ℝ)≤(Fintype.card W:ℝ):=by exact_mod_cast hn4
    have he:0≤ε*(Fintype.card W:ℝ):=by positivity
    exact_mod_cast (show (2:ℝ)≤(G.maxDegree:ℝ) by nlinarith only [hdense,hn4R,he])
  refine ⟨X,hodd,?_⟩
  have hb:=budget_of_small_complement G L hLG
    (fun v => (L.degree_le_maxDegree v).trans hL) hD hR X hodd hof hstar
    M (Fintype.card W/(4096*q^2)) hMissing htiny
  simpa only [Nat.add_assoc] using hb

/-- An explicit test on the original graph certifies that every actual
layer with the displayed defect budget preserves absence of overfull sets.
No no-overfull statement about the residue is an input. -/
theorem above_half_no_residual_overfull_of_no_almost_set (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let k:=Fintype.card W/(4096*q^2)
        ∀M:ℕ,¬HasOddAlmostOverfullSet G (M+8*k) →
          ∀(L : SimpleGraph W) [DecidableRel L.Adj],L≤G → L.maxDegree≤2 →
            (G\L).maxDegree=G.maxDegree-2 → (∑v:W,(2-L.degree v))≤M →
            ¬(G\L).HasOverfullSubgraph := by
  obtain ⟨q,hq,N,hN⟩:=above_half_overfull_residue_implies_almost.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro W _ _ G _ hn hc hdense
  dsimp only
  intro M hNo L _ hLG hL hR hMissing hOF
  exact hNo (hN G hn hc hdense L hLG hL hR M hMissing hOF)

end OverfullWork.AlmostOverfullLayerCompatibility
