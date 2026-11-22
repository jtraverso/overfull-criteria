module

public import OverfullWork.OddLowSmallCases
public import OverfullWork.LinearCriterion

@[expose] public section


/-! # Two actual deficient vertices in every large critical obstruction

Odd-order obstructions are handled by the proved two-exception criterion.
At even order an odd cut excludes exactly one deficient vertex; a regular
critical obstruction is excluded by the existing fixed-gap criterion.
-/
namespace OverfullWork.CriticalDeficientVertices
open SimpleGraph Finset OddCutDeficit
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- In an even no-overfull graph, a bound of one on the number of
deficient vertices forces all vertices to have maximum degree. -/
theorem regular_of_even_at_most_one_deficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : Even (Fintype.card V)) (hno : ¬G.HasOverfullSubgraph)
    (hcount : (univ.filter fun v=>G.degree v<G.maxDegree).card≤1) :
    G.IsRegularOfDegree G.maxDegree := by
  intro v
  have hle:=G.degree_le_maxDegree v
  by_contra hneq
  have hv : v∈univ.filter (fun w=>G.degree w<G.maxDegree) :=
    mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hother : ∀w,w≠v → G.degree w=G.maxDegree := by
    intro w hw
    have hd:=G.degree_le_maxDegree w
    by_contra hh
    have hw':w∈univ.filter (fun w=>G.degree w<G.maxDegree) :=
      mem_filter.mpr ⟨mem_univ _,by omega⟩
    exact hw (card_le_one.mp hcount w hw' v hv)
  let S : Finset V:={v}ᶜ
  have hcard : S.card+1=Fintype.card V := by
    have hh:=card_compl ({v}:Finset V)
    simp only [card_singleton] at hh
    have hn : 1≤Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    dsimp [S]
    omega
  have hodd : Odd S.card := by
    obtain ⟨m,hm⟩:=heven
    exact ⟨m-1,by omega⟩
  have hdef : deficitMass G G.maxDegree S=0 := by
    apply sum_eq_zero
    intro w hw
    have hwv : w≠v := by simpa [S] using hw
    rw [hother w hwv,Nat.sub_self]
  have hb:=(no_overfull_iff_odd_cut_deficit G).mp hno S hodd
  have hcut:=internal_cut_identity G ({v}:Finset V)
  have hi : internalEdges G ({v}:Finset V)=0 := by
    simpa using OddTwoExceptionDegreeSum.internalEdges_pair_eq_zero G v v G.irrefl
  rw [hi] at hcut
  simp only [mul_zero,zero_add,sum_singleton] at hcut
  change G.maxDegree≤cutEdges G ({v}:Finset V)ᶜ+deficitMass G G.maxDegree S at hb
  rw [NearTightOddSetGeometry.cutEdges_compl,hcut,hdef] at hb
  omega

/-- The existence threshold precedes the graph, and both parities are
included. No deficient vertices are selected as hypotheses. -/
theorem above_half_critical_two_deficient (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph →
      2≤(univ.filter fun v=>G.degree v<G.maxDegree).card := by
  obtain ⟨N,hodd⟩:=OddLowSmallCases.above_half_critical_three_deficient.{u} ε hε
  obtain ⟨A,_,hgap⟩:=Gate8J2I.above_half_linear_gap.{u} ε hε
  refine ⟨max N A,?_⟩
  intro V _ _ G _ hn hc hdense hno
  by_contra hcount
  have hsmall : (univ.filter fun v=>G.degree v<G.maxDegree).card≤1 := by omega
  by_cases ho : Odd (Fintype.card V)
  · have hh:=hodd G ((le_max_left _ _).trans hn) hc hno ho hdense
    omega
  · have hreg:=regular_of_even_at_most_one_deficient G (Nat.not_odd_iff_even.mp ho) hno hsmall
    have : Nonempty V:=hc.1.nonempty
    have hmin:=hreg.minDegree_eq
    have hsize : A*(G.maxDegree-G.minDegree+1)≤Fintype.card V := by
      rw [hmin]
      simpa using (le_max_right N A).trans hn
    exact hc.2.1 ((hgap G hsize hdense).mpr hno)

end OverfullWork.CriticalDeficientVertices
