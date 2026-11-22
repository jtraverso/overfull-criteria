module

public import OverfullWork.CriticalCertificateResidualCases
public import OverfullWork.ClassTwoHallMatching
public import OverfullWork.ClassTwoGlobalNoOverfull

@[expose] public section


/-! Three active complementary vertices in the all-maximum odd-core case. -/
namespace OverfullWork.MaximumCoreTripleChoice
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem three_active (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
    (c : Certificate G B K) (hCore : ∀ v ∈ c.set, G.degree v=G.maxDegree)
    (hLarge : G.maxDegree < ∑ y ∈ c.setᶜ, G.degree y) :
    3 ≤ (c.setᶜ.filter (fun y => 0 < G.degree y)).card := by
  let A := c.setᶜ.filter (fun y => 0 < G.degree y)
  have hSum : (∑ y ∈ A, G.degree y)=(∑ y ∈ c.setᶜ, G.degree y) := by
    apply sum_subset (filter_subset _ _)
    intro y hy hyA
    have hz : ¬0 < G.degree y := fun hh => hyA (mem_filter.mpr ⟨hy,hh⟩)
    omega
  have hAtLeastTwo : 2 ≤ A.card := by
    have hPos : c.set.Nonempty := by
      apply card_pos.mp
      obtain ⟨t,ht⟩ := c.odd
      omega
    obtain ⟨x,hx⟩ := hPos
    apply ClassTwoGlobalNoOverfull.two_active_of_large_centre G c x hx
    rw [hCore x hx]
    exact hLarge
  by_contra! hSmall
  change A.card < 3 at hSmall
  have hTwo : A.card=2 := by omega
  obtain ⟨y,z,hyz,hA⟩ := card_eq_two.mp hTwo
  have hy : y ∈ c.setᶜ := (mem_filter.mp (show y ∈ A by rw [hA];simp)).1
  have hz : z ∈ c.setᶜ := (mem_filter.mp (show z ∈ A by rw [hA];simp)).1
  have hLight := c.light_pairs y hy z hz hyz
  rw [hA,sum_pair hyz] at hSum
  have hTotal : (∑ y ∈ c.setᶜ, G.degree y)=G.maxDegree+1 := by omega
  have hX : (∑ x ∈ c.set, G.degree x)=G.maxDegree*c.set.card := by
    rw [sum_congr rfl (fun x hx => hCore x hx)]
    simp [Nat.mul_comm]
  have hHandshake := sum_add_sum_compl c.set (fun v => G.degree v)
  rw [hX,hTotal,G.sum_degrees_eq_twice_card_edges] at hHandshake
  obtain ⟨t,ht⟩ := c.odd
  have hOdd : G.maxDegree*c.set.card+(G.maxDegree+1)=2*(G.maxDegree*(t+1))+1 := by
    rw [ht]
    ring
  omega

theorem exists_triple_edges (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V)
    (hInd : G.IsIndepSet (Y:Set V))
    (hHall : ∀ w ∈ Y, ∀ v, G.Adj w v → PrunedCore.neighboursIn G Y v < G.degree w)
    (x : V) (hx : x ∉ Y) (y z t : V) (hy : y ∈ Y) (hz : z ∈ Y) (ht : t ∈ Y)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hPos : 0 < G.degree y ∧ 0 < G.degree z ∧ 0 < G.degree t) :
    ∃ a b d, a ∈ Yᶜ ∧ b ∈ Yᶜ ∧ d ∈ Yᶜ ∧
      a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ G.Adj y a ∧ G.Adj z b ∧ G.Adj t d := by
  let W : Finset V := {y,z,t}
  have hWY : W ⊆ Y := by
    intro w hw
    simp only [W,mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl|rfl <;> assumption
  have hWInd : G.IsIndepSet (W:Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab hAdj
    exact hInd (hWY ha) (hWY hb) hab hAdj
  have hWPos : ∀ w ∈ W, 0 < G.degree w := by
    intro w hw
    simp only [W,mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl|rfl
    · exact hPos.1
    · exact hPos.2.1
    · exact hPos.2.2
  have hWHall : ∀ w ∈ W, ∀ v, G.Adj w v → PrunedCore.neighboursIn G W v < G.degree w := by
    intro w hw v hAdj
    exact (PrunedCore.neighboursIn_mono G hWY v).trans_lt (hHall w (hWY hw) v hAdj)
  obtain ⟨f,hf,hAdj,_⟩ := ClassTwoHallMatching.exists_transversal_avoiding G W hWInd hWPos hWHall
    x (fun hh => hx (hWY hh))
  let a := (f ⟨y,by simp [W]⟩).val
  let b := (f ⟨z,by simp [W]⟩).val
  let d := (f ⟨t,by simp [W]⟩).val
  have hya : G.Adj y a := hAdj ⟨y,by simp [W]⟩
  have hzb : G.Adj z b := hAdj ⟨z,by simp [W]⟩
  have htd : G.Adj t d := hAdj ⟨t,by simp [W]⟩
  refine ⟨a,b,d,mem_compl.mpr (fun ha => hInd hy ha hya.ne hya),
    mem_compl.mpr (fun hb => hInd hz hb hzb.ne hzb),
    mem_compl.mpr (fun hd => hInd ht hd htd.ne htd),?_,?_,?_,hya,hzb,htd⟩
  · intro he
    exact hyz (congrArg Subtype.val (hf (Subtype.ext he)))
  · intro he
    exact hyt (congrArg Subtype.val (hf (Subtype.ext he)))
  · intro he
    exact hzt (congrArg Subtype.val (hf (Subtype.ext he)))

end OverfullWork.MaximumCoreTripleChoice
