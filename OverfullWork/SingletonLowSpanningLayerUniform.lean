module

public import OverfullWork.SmallLowSpanningLayerUniform
public import OverfullWork.SingletonLowSpanningLayer
public import OverfullWork.CriticalLowPartnerProjection

@[expose] public section


/-! # Uniform actual spanning layers for a singleton low set

Two deficient vertices supply one distinct from the low vertex. A genuine
low edge avoiding it, an injective projection avoiding the entire edge,
and an actual core Hamilton path discharge every construction input.
-/
namespace OverfullWork.SingletonLowSpanningLayerUniform
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open scoped Classical
universe u
set_option maxHeartbeats 4000000

/-- The unique low vertex is covered once; every maximum and near-maximum
vertex receives its required degree. Both graph-order parities are allowed. -/
theorem above_half_singleton_low_layer (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph → ∀w,lowVertices G={w} →
      Nonempty (SmallLowSpanningLayer.Certificate G) := by
  obtain ⟨q,hq,N₀,hmargins⟩:=SmallLowSpanningLayerUniform.above_half_small_low_margins.{u} ε hε
  obtain ⟨N₁,hdef⟩:=CriticalDeficientVertices.above_half_critical_two_deficient.{u} ε hε
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ G _ hn hc hdense hno w hW
  classical
  have hn₀ : N₀≤Fintype.card V := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁≤Fintype.card V := (le_max_right N₀ N₁).trans hn
  obtain ⟨hD,hexception,hbudget,hsize,hcore⟩:=hmargins G hn₀ hc hdense
  let a₀:=Fintype.card V/(8*q)
  let U:=exceptions G G.maxDegree a₀
  have hbudgetU : 3*(U.card+4)≤G.maxDegree := by convert hbudget using 1
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,he])
  have haf : 8*q*a₀≤Fintype.card V := Nat.mul_div_le (Fintype.card V) (8*q)
  have h16 : 16*a₀≤Fintype.card V :=
    (Nat.mul_le_mul_right a₀ (by omega : 16≤8*q)).trans haf
  have haD : 8*a₀≤G.maxDegree := by omega
  have hwW : w∈lowVertices G := by rw [hW];simp
  have hwU : w∈U :=
    CriticalLowPartnerProjection.lowVertices_subset_exceptions G a₀ (by omega) haD hwW
  have hdeficient:=hdef G hn₁ hc hdense hno
  obtain ⟨x,hx,y,hy,hxy⟩:=one_lt_card.mp
    (show 1<(univ.filter fun v=>G.degree v<G.maxDegree).card by omega)
  have hspare : ∃x,x≠w ∧ G.degree x+1≤G.maxDegree := by
    by_cases hxw : x=w
    · refine ⟨y,fun he=>hxy (hxw.trans he.symm),?_⟩
      have hh:=(mem_filter.mp hy).2
      omega
    · refine ⟨x,hxw,?_⟩
      have hh:=(mem_filter.mp hx).2
      omega
  obtain ⟨x,hxw,hxD⟩:=hspare
  have hwdeg:=OddLowSmallCases.critical_two_le_degree G hc w
  obtain ⟨a,hax,hwa⟩:=OddLowSmallCases.exists_singleton_edge_avoiding G w x hwdeg
  obtain ⟨P⟩ : Nonempty (LowSkeletonProjection.Projection G {a,x} U {w,a}) := by
    apply LowSkeletonProjection.exists_projection
    intro z hz
    have hzpair : z=a ∨ z=x := by
      simpa only [mem_insert,mem_singleton] using (mem_inter.mp hz).1
    have haw : a≠w := Ne.symm (G.ne_of_adj hwa)
    have hzw : z≠w := by
      rcases hzpair with rfl|rfl
      · exact haw
      · exact hxw
    have hznot : z∉lowVertices G := by rw [hW];simpa using hzw
    have hhigh : G.maxDegree<3*G.degree z := by
      simpa only [lowVertices,mem_filter,mem_univ,true_and,not_le] using hznot
    have hZ : ({w,a}:Finset V).card≤2 := by
      have hh:=card_insert_le w ({a}:Finset V)
      simpa only [card_singleton] using hh
    rw [card_pair hax]
    omega
  exact SmallLowSpanningLayer.exists_singleton_low_layer_finite
    G hc hD U w a x hW hwU hwa hax hxw hxD hexception P hsize hcore

end OverfullWork.SingletonLowSpanningLayerUniform
