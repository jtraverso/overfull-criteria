module

public import OverfullWork.CriticalEvenLowLayer
public import OverfullWork.CriticalOddLowLayer
public import OverfullWork.SmallLowSpanningLayerUniform
public import OverfullWork.SingletonLowSpanningLayerUniform

@[expose] public section


/-! # One genuine two-colour reduction for every large critical obstruction

The empty, singleton, positive even and positive odd low-set cases are
all constructed. The result is an actual coloured layer, exact degree
demands, a maximum-degree drop by two and an uncolourable residue.
No absence of overfull subsets in the residue, repeated trimming,
canonical completion or final factorization is claimed.
-/
namespace OverfullWork.CriticalTwoColourReduction
open SimpleGraph Finset LowVertexMatchingAbsorption
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

structure Reduction (G : SimpleGraph V) [DecidableRel G.Adj] where
  layer : SimpleGraph V
  le_original : layer≤G
  acyclic : layer.IsAcyclic
  degree_le_two : ∀v,layer.degree v≤2
  colourable : layer.EdgeColorable 2
  demands : ∀v,G.degree v+2≤G.maxDegree+layer.degree v
  low_positive : ∀w∈lowVertices G,1≤layer.degree w
  residual_maxDegree : (G\layer).maxDegree=G.maxDegree-2
  residual_uncolourable : ¬(G\layer).EdgeColorable (G\layer).maxDegree

theorem degree_demands_of_exact_residue (G L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel L.Adj] (hD : 2≤G.maxDegree) (hLG : L≤G)
    (hres : (G\L).maxDegree=G.maxDegree-2) :
    ∀v,G.degree v+2≤G.maxDegree+L.degree v := by
  intro v
  have hs:=MaximumMatching.degree_sdiff_add_of_le G L hLG v
  have hr:=(G\L).degree_le_maxDegree v
  rw [hres] at hr
  omega

private theorem of_even {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} (hD : 2≤G.maxDegree)
    (c : CriticalEvenLowLayer.Certificate G U) : Nonempty (Reduction G) := by
  refine ⟨⟨c.layer,c.le_original,c.acyclic,c.degree_le_two,c.colourable,
    degree_demands_of_exact_residue G c.layer hD c.le_original c.residual_maxDegree,
    ?_,c.residual_maxDegree,c.residual_uncolourable⟩⟩
  intro w hw
  rw [c.low_one_cover w hw]

private theorem of_odd {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} (hD : 2≤G.maxDegree)
    (c : CriticalOddLowLayer.Certificate G U) : Nonempty (Reduction G) :=
  ⟨⟨c.layer,c.le_original,c.acyclic,c.degree_le_two,c.colourable,
    degree_demands_of_exact_residue G c.layer hD c.le_original c.residual_maxDegree,
    c.low_positive,c.residual_maxDegree,c.residual_uncolourable⟩⟩

omit [DecidableEq V] in
private theorem of_small {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : SmallLowSpanningLayer.Certificate G) : Nonempty (Reduction G) := by
  refine ⟨⟨c.layer,c.le_original,c.acyclic,c.degree_le_two,c.colourable,c.demands,
    ?_,c.residual_maxDegree,c.residual_uncolourable⟩⟩
  intro w hw
  rw [c.low_one_cover w hw]

/-- Both non-small parities admit the same actual reduction. -/
theorem above_half_many_low_reduction (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      2≤(lowVertices G).card → Nonempty (Reduction G) := by
  obtain ⟨_,_,NE,hE⟩:=CriticalEvenLowLayer.above_half_even_low_layer.{u} ε hε
  obtain ⟨_,_,NO,hO⟩:=CriticalOddLowLayer.above_half_odd_low_layer.{u} ε hε
  refine ⟨max 4 (max NE NO),?_⟩
  intro V _ _ G _ hn hc hdense htwo
  have hn4 : 4≤Fintype.card V := (le_max_left _ _).trans hn
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hD : 2≤G.maxDegree := by omega
  have hn' : max NE NO≤Fintype.card V := (le_max_right _ _).trans hn
  by_cases he : Even (lowVertices G).card
  · obtain ⟨c⟩:=hE G ((le_max_left _ _).trans hn') hc hdense he htwo
    exact of_even hD c
  · have ho : Odd (lowVertices G).card := Nat.not_even_iff_odd.mp he
    have hthree : 3≤(lowVertices G).card := by obtain ⟨k,hk⟩:=ho;omega
    obtain ⟨c⟩:=hO G ((le_max_right _ _).trans hn') hc hdense ho hthree
    exact of_odd hD c

/-- All low-set cardinalities and both graph orders are covered.
Only the original critical, above-half and no-overfull hypotheses are
inputs; all matchings, paths, choices and the layer are constructed. -/
theorem above_half_critical_two_colour_reduction (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph → Nonempty (Reduction G) := by
  obtain ⟨NM,hM⟩:=above_half_many_low_reduction.{u} ε hε
  obtain ⟨NZ,hZ⟩:=SmallLowSpanningLayerUniform.above_half_zero_low_layer.{u} ε hε
  obtain ⟨NS,hS⟩:=SingletonLowSpanningLayerUniform.above_half_singleton_low_layer.{u} ε hε
  refine ⟨max NM (max NZ NS),?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnM : NM≤Fintype.card V := (le_max_left _ _).trans hn
  have hnZS : max NZ NS≤Fintype.card V := (le_max_right _ _).trans hn
  by_cases hm : 2≤(lowVertices G).card
  · exact hM G hnM hc hdense hm
  · by_cases hz : lowVertices G=∅
    · obtain ⟨c⟩:=hZ G ((le_max_left _ _).trans hnZS) hc hdense hno hz
      exact of_small c
    · have hcard : (lowVertices G).card=1 := by
        have hp : 0<(lowVertices G).card:=card_pos.mpr (nonempty_iff_ne_empty.mpr hz)
        omega
      obtain ⟨w,hw⟩:=card_eq_one.mp hcard
      obtain ⟨c⟩:=hS G ((le_max_right _ _).trans hnZS) hc hdense hno w hw
      exact of_small c

end OverfullWork.CriticalTwoColourReduction
