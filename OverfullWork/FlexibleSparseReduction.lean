module

public import OverfullWork.SparseLargeLowLayer
public import OverfullWork.SparseSmallLowLayer
public import OverfullWork.FlexibleCriticalExceptionCount

@[expose] public section


/-! # Actual sparse reductions with an independently prescribed budget

The preparation scales in the even, odd and small-low-set branches are
fixed before the graph.  The target budget scale Q is a separate input;
the flexible critical exception estimate controls each original
exception set at that budget without changing any constructed layer.
No absence of overfull subsets in the residue is asserted.
-/
namespace OverfullWork.FlexibleSparseReduction
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open CriticalTwoColourReduction
open scoped Classical
universe u
set_option maxHeartbeats 5000000

/-- At any prescribed fixed budget scale Q, sufficiently large critical
graphs above one half admit an actual two-colour reduction with this
missing-degree bound. Q is explicit and the threshold precedes G. -/
theorem above_half_sparse_reduction_at_budget (ε : ℝ) (hε : 0<ε)
    (Q : ℕ) (hQ : 2≤Q) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      ¬G.HasOverfullSubgraph →
      ∃ r : Reduction G,
        (∑v : V,(2-r.layer.degree v))≤2*(Fintype.card V/(4096*Q^2))+2 := by
  obtain ⟨qE,hqE,NE,hE⟩ :=
    CriticalCorePathPreparation.above_half_even_core_path_preparation.{u} ε hε
  obtain ⟨qO,hqO,NO,hO⟩ :=
    CriticalOddCorePathPreparation.above_half_odd_core_path_preparation.{u} ε hε
  obtain ⟨qS,hqS,NS,hS⟩ :=
    SparseSmallLowLayer.above_half_small_low_layer_sparse.{u} ε hε
  obtain ⟨NME,hME⟩ := FlexibleCriticalExceptionCount.exception_count_at_scales.{u} qE Q hqE hQ
  obtain ⟨NMO,hMO⟩ := FlexibleCriticalExceptionCount.exception_count_at_scales.{u} qO Q hqO hQ
  obtain ⟨NMS,hMS⟩ := FlexibleCriticalExceptionCount.exception_count_at_scales.{u} qS Q hqS hQ
  refine ⟨NE+NO+NS+NME+NMO+NMS+16*qE+16*qO,?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnE : NE≤Fintype.card V := by omega
  have hnO : NO≤Fintype.card V := by omega
  have hnS : NS≤Fintype.card V := by omega
  have hnME : NME≤Fintype.card V := by omega
  have hnMO : NMO≤Fintype.card V := by omega
  have hnMS : NMS≤Fintype.card V := by omega
  have hn16E : 16*qE≤Fintype.card V := by omega
  have hn16O : 16*qO≤Fintype.card V := by omega
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,he])
  have hD : 2≤G.maxDegree := by omega
  by_cases htwo : 2≤(lowVertices G).card
  · by_cases heven : Even (lowVertices G).card
    · obtain ⟨_,⟨s⟩⟩ := hE G hnE hc hdense heven htwo
      have ha : 2≤Fintype.card V/(8*qE) := by
        apply (Nat.le_div_iff_mul_le (by positivity)).mpr
        omega
      obtain ⟨c⟩ := CriticalEvenLowLayer.certificate_of_prepared G _ _ hc hD (by
        intro v hv
        have hh := (mem_filter.mp hv).2
        omega) s
      have hUk := hME G hnME hc hnD
      obtain ⟨r,hr⟩ := SparseLowLayer.exists_sparse_of_even_certificate G _
        (Fintype.card V/(4096*Q^2)) hD hUk c
      refine ⟨r,?_⟩
      change (∑v : V,(2-r.layer.degree v))≤_ at hr
      omega
    · have hodd : Odd (lowVertices G).card := Nat.not_even_iff_odd.mp heven
      have hthree : 3≤(lowVertices G).card := by obtain ⟨k,hk⟩ := hodd; omega
      obtain ⟨_,⟨s⟩⟩ := hO G hnO hc hdense hodd hthree
      have ha : 2≤Fintype.card V/(8*qO) := by
        apply (Nat.le_div_iff_mul_le (by positivity)).mpr
        omega
      obtain ⟨c⟩ := CriticalOddLowLayer.certificate_of_prepared G _ _ hc hD (by
        intro v hv
        have hh := (mem_filter.mp hv).2
        omega) s
      have hUk := hMO G hnMO hc hnD
      obtain ⟨r,hr⟩ := SparseLowLayer.exists_sparse_of_odd_certificate G _
        (Fintype.card V/(4096*Q^2)) hD hUk c
      refine ⟨r,?_⟩
      change (∑v : V,(2-r.layer.degree v))≤_ at hr
      omega
  · obtain ⟨c,hMissing,_⟩ := hS G hnS hc hdense hno (by omega)
    have hUk := hMS G hnMS hc hnD
    let r : Reduction G := {
      layer:=c.layer,le_original:=c.le_original,acyclic:=c.acyclic,
      degree_le_two:=c.degree_le_two,colourable:=c.colourable,demands:=c.demands,
      low_positive:=by intro w hw; rw [c.low_one_cover w hw],
      residual_maxDegree:=c.residual_maxDegree,residual_uncolourable:=c.residual_uncolourable }
    refine ⟨r,?_⟩
    have hb := hMissing.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hUk) 2)
    simpa only [r] using hb

end OverfullWork.FlexibleSparseReduction
