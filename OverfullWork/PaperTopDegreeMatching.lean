module

public import OverfullWork.MatchingOddDeficiency
public import OverfullWork.MaximumNeighbourCleanup

@[expose] public section


/-! # CMS Operation 4.2, Steps 1--3: top-degree selection and cleanup

The published proof requires the two greatest complementary degrees,
not an arbitrary selected pair. This choice is constructed by finite
maximization. After the actual matching round it keeps the complementary
vertices nonmaximum, so the real Algorithm 2 cleanup can be applied to
the class-two residue without assuming that residue is critical.
-/
namespace OverfullWork.PaperTopDegreeMatching
open SimpleGraph Finset NormalizedAlmostStoppingRun LargeCentreMatchingStep PrunedCore
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

structure IsTopPair (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (y z : V) : Prop where
  left_mem : y∈Y
  right_mem : z∈Y
  ne : y≠z
  maximum : ∀v∈Y,G.degree v≤G.degree y
  second : ∀v∈Y,v≠y → G.degree v≤G.degree z

theorem exists_top_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hTwo : 2≤Y.card) : ∃y z,IsTopPair G Y y z := by
  have hNonempty:Y.Nonempty:=card_pos.mp (by omega)
  obtain ⟨y,hy,hMaximum⟩:=Y.exists_max_image (fun v=>G.degree v) hNonempty
  have hRest:(Y.erase y).Nonempty:=by
    apply card_pos.mp
    rw [card_erase_of_mem hy]
    omega
  obtain ⟨z,hz,hSecond⟩:=(Y.erase y).exists_max_image (fun v=>G.degree v) hRest
  exact ⟨y,z,⟨hy,(mem_erase.mp hz).2,(mem_erase.mp hz).1.symm,hMaximum,
    fun v hv hvy=>hSecond v (mem_erase.mpr ⟨hvy,hv⟩)⟩⟩

/-- The first actual matching round can satisfy the exact top-degree
choice made in the paper's Step 3. -/
theorem exists_top_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hxD : G.degree x<G.maxDegree)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree) :
    ∃y z,IsTopPair G c.setᶜ y z ∧ Nonempty (Round G c x y z) := by
  obtain ⟨y,z,hTop⟩:=exists_top_pair G c.setᶜ
    (LargeCentreCriticalGeometry.two_le_complement_card G c hx hLarge)
  exact ⟨y,z,hTop,exists_round G hc c x hx hLarge hxD hMargin y z hTop.left_mem hTop.right_mem hTop.ne⟩

/-- Selecting the two largest degrees prevents an unselected
complementary vertex from becoming a new maximum after the degree drop. -/
theorem residue_complement_nonmaximum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hD : 4≤G.maxDegree) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z) :
    ∀w∈c.setᶜ,(G\r.matching).degree w<(G\r.matching).maxDegree := by
  have hLight:=c.light_pairs y hTop.left_mem z hTop.right_mem hTop.ne
  have hZY:=hTop.maximum z hTop.right_mem
  have hSecond:G.degree z+2≤G.maxDegree:=by omega
  have hNonmax:=CriticalIndependentPairMatching.complement_nonmaximum G hc c hx hLarge
  intro w hw
  have hSum:(G\r.matching).degree w+r.matching.degree w=G.degree w:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original w
  rw [r.complementary_degrees w hw] at hSum
  rw [r.residual_maxDegree]
  by_cases hSelected:w=y ∨ w=z
  · rw [if_pos hSelected] at hSum
    have hOld:=hNonmax w hw
    omega
  · rw [if_neg hSelected] at hSum
    have hWZ:=hTop.second w hw (fun he=>hSelected (Or.inl he))
    omega

/-- The matching residue receives a real Algorithm 2 cleanup and the
published local invariants. Only the SOURCE graph is assumed critical.
Global no-overfullness of the matching residue is not asserted here. -/
theorem exists_post_round_cleanup (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    {x y z : V} (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hD : 4≤G.maxDegree) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z) :
    ∃H : SimpleGraph V,
      MaximumNeighbourCleanup.DeletionRun c.setᶜ (G\r.matching) H ∧
      H≤G\r.matching ∧ H.maxDegree=G.maxDegree-1 ∧ ¬H.EdgeColorable H.maxDegree ∧
      H.induce (c.set:Set V)=(G\r.matching).induce (c.set:Set V) ∧
      (∀w∈c.setᶜ,H.degree w<H.maxDegree) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → neighboursIn H c.setᶜ v<H.degree w) ∧
      ∀w∈c.setᶜ,∀v,H.Adj w v → H.maxDegree+2≤H.degree w+H.degree v := by
  classical
  have hW:=residue_complement_nonmaximum G hc c hx hLarge hD hTop r
  obtain ⟨H,hRun,hLe,hMax,hNC,hCore,hNonmax,_,hHall,hDegree⟩:=
    MaximumNeighbourCleanup.exists_cleanup_ready (G\r.matching) r.residual_uncolourable c.setᶜ hW
  refine ⟨H,hRun,hLe,hMax.trans r.residual_maxDegree,hNC,?_,hNonmax,hHall,hDegree⟩
  have hSet:((↑(c.setᶜ):Set V)ᶜ)=(c.set:Set V):=by
    ext v
    simp only [Set.mem_compl_iff,mem_coe,mem_compl,not_not]
  rw [hSet] at hCore
  exact hCore

end OverfullWork.PaperTopDegreeMatching
