module

public import OverfullWork.NormalizedCanonicalCandidate

@[expose] public section


/-! # Exact deficit control in the large-centre stopping branch

The merged complementary degree exceeds a selected core degree by s>0.
The actual almost-overfull budget then pays s and all other core deficits
at once. This supplies the high-degree core needed by the matching step,
and the independent enlarged exceptional set in the second-low-core case.
No matching-removal iteration or canonical factorization is postulated.
-/
namespace OverfullWork.LargeCentreCriticalGeometry
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

theorem deficit_erase_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) {x : V} (hx : x∈X) :
    deficitMass G G.maxDegree (X.erase x)+(G.maxDegree-G.degree x)=
      deficitMass G G.maxDegree X := by
  exact sum_erase_add X (fun v=>G.maxDegree-G.degree v) hx

/-- The excess and all remaining core deficits share the same budget. -/
theorem deficit_and_excess_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y)) :
    deficitMass G G.maxDegree (c.set.erase x)+
      ((∑y∈c.setᶜ,G.degree y)-G.degree x)≤B := by
  have he:=deficit_erase_add G c.set hx
  have hd:=G.degree_le_maxDegree x
  have hb:=c.budget
  omega

theorem excess_pos_and_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y)) :
    0<((∑y∈c.setᶜ,G.degree y)-G.degree x) ∧
      ((∑y∈c.setᶜ,G.degree y)-G.degree x)≤B := by
  have hh:=deficit_and_excess_le G c hx hLarge
  omega

/-- Every other core vertex has degree at least Delta-B+s. -/
theorem other_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y)) {v : V}
    (hv : v∈c.set) (hvx : v≠x) :
    G.maxDegree+((∑y∈c.setᶜ,G.degree y)-G.degree x)≤G.degree v+B := by
  have hh:=deficit_and_excess_le G c hx hLarge
  have hs:G.maxDegree-G.degree v≤deficitMass G G.maxDegree (c.set.erase x):=by
    unfold deficitMass
    exact single_le_sum (f:=fun z=>G.maxDegree-G.degree z)
      (fun _ _=>Nat.zero_le _) (mem_erase.mpr ⟨hvx,hv⟩)
  have hd:=G.degree_le_maxDegree v
  omega

/-- A large merged centre requires at least two complementary vertices. -/
theorem two_le_complement_card (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y)) : 2≤c.setᶜ.card := by
  by_contra hn
  have hcard:c.setᶜ.card≤1:=by omega
  by_cases hz:c.setᶜ=∅
  · rw [hz,sum_empty] at hLarge
    omega
  · have hp:0<c.setᶜ.card:=card_pos.mpr (nonempty_iff_ne_empty.mpr hz)
    obtain ⟨y,hy⟩:=card_eq_one.mp (show c.setᶜ.card=1 by omega)
    have hyY:y∈c.setᶜ:=by rw [hy];simp
    have hd:=c.ordered y hyY x hx
    rw [hy,sum_singleton] at hLarge
    omega

/-- In the second-low-core branch the selected core vertex itself is
small: its degree and the positive excess together are at most B. -/
theorem anchor_degree_add_excess_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x v : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hv : v∈c.set) (hvx : v≠x) (hLow : G.degree v≤G.maxDegree-G.degree x) :
    G.degree x+((∑y∈c.setᶜ,G.degree y)-G.degree x)≤B := by
  have hh:=other_degree_lower G c hx hLarge hv hvx
  have hd:=G.degree_le_maxDegree x
  omega

/-- VAL makes the enlarged exceptional set independent, including the
selected core vertex, under the explicit small-budget inequality. -/
theorem enlarged_complement_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x v : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hv : v∈c.set) (hvx : v≠x) (hLow : G.degree v≤G.maxDegree-G.degree x)
    (hB : 2*B<G.maxDegree+2) :
    G.IsIndepSet (↑(insert x c.setᶜ):Set V) := by
  have ha:=anchor_degree_add_excess_le G c hx hLarge hv hvx hLow
  have hDeg:∀z∈insert x c.setᶜ,G.degree z≤B:=by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · omega
    · exact (c.ordered z hz x hx).trans (by omega)
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha' b hb' _ hab
  have had:=hDeg a ha'
  have hbd:=hDeg b hb'
  have hVal:=Overfull.deg_add hc hab
  omega

/-- Finite minimization selects the actual least-degree core anchor
while retaining the large-centre comparison. -/
theorem exists_minimum_large_anchor (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K)
    (hLarge : ∃v∈c.set,G.degree v<(∑y∈c.setᶜ,G.degree y)) :
    ∃x∈c.set,(∀v∈c.set,G.degree x≤G.degree v) ∧
      G.degree x<(∑y∈c.setᶜ,G.degree y) := by
  obtain ⟨v,hv,hvLarge⟩:=hLarge
  obtain ⟨x,hx,hMin⟩:=c.set.exists_min_image (fun z=>G.degree z) ⟨v,hv⟩
  exact ⟨x,hx,hMin,(hMin v hv).trans_lt hvLarge⟩

/-- If every core vertex already has maximum degree, its complement
cannot be a large centre on only two vertices: the candidate total
degree Delta+1 would make the graph's degree sum odd. -/
theorem three_le_complement_of_maximum_core (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K)
    {x : V} (hx : x∈c.set)
    (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hCore : ∀v∈c.set,G.degree v=G.maxDegree) : 3≤c.setᶜ.card := by
  have hTwo:=two_le_complement_card G c hx hLarge
  by_contra hn
  obtain ⟨y,z,hyz,hY⟩:=card_eq_two.mp (show c.setᶜ.card=2 by omega)
  have hy:y∈c.setᶜ:=by rw [hY];simp
  have hz:z∈c.setᶜ:=by rw [hY];simp
  have hLight:=c.light_pairs y hy z hz hyz
  have hSumY:(∑v∈c.setᶜ,G.degree v)=G.degree y+G.degree z:=by rw [hY,sum_pair hyz]
  have hDx:=hCore x hx
  have hYdegree:(∑v∈c.setᶜ,G.degree v)=G.maxDegree+1:=by omega
  have hSumX:(∑v∈c.set,G.degree v)=G.maxDegree*c.set.card:=by
    rw [sum_congr rfl (fun v hv=>hCore v hv)]
    simp [Nat.mul_comm]
  have hPartition:=sum_add_sum_compl c.set (fun v=>G.degree v)
  rw [hSumX,hYdegree,G.sum_degrees_eq_twice_card_edges] at hPartition
  obtain ⟨t,ht⟩:=c.odd
  have hOdd:G.maxDegree*c.set.card+(G.maxDegree+1)=2*(G.maxDegree*(t+1))+1:=by
    rw [ht]
    ring
  omega

end OverfullWork.LargeCentreCriticalGeometry
