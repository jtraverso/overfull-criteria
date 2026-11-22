module

public import OverfullWork.MaximumDegreeCore

@[expose] public section


/-! # Degree strata and a global VAL deficit-profile inequality -/
namespace OverfullWork.Gate8J2C
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def maximumNeighbours (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℕ :=
  ((G.neighborFinset x).filter fun z => G.degree z=G.maxDegree).card

theorem deficit_le_maximumNeighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) {x y : V} (hxy : G.Adj x y) :
    G.maxDegree-G.degree y+1≤maximumNeighbours G x := by
  have hv:=Overfull.val_crit hcrit hxy
  have hs : ((G.neighborFinset x).filter fun z => z≠y ∧ G.degree z=G.maxDegree)⊆
      ((G.neighborFinset x).filter fun z => G.degree z=G.maxDegree) := by
    intro z hz
    obtain ⟨hz,_,hd⟩:=mem_filter.mp hz
    exact mem_filter.mpr ⟨hz,hd⟩
  have hc:=card_le_card hs
  have hd:=G.degree_le_maxDegree y
  change _≤maximumNeighbours G x at hc
  omega

/-- Below half the maximum degree, the low-degree stratum is independent. -/
theorem low_degree_stratum_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (t : ℕ) (ht : 2*t≤G.maxDegree+1)
    {x y : V} (hx : G.degree x≤t) (hy : G.degree y≤t) : ¬G.Adj x y := by
  intro hxy
  have h:=Overfull.deg_add hcrit hxy
  omega

/-- Its complementary high-degree stratum covers every edge. -/
theorem high_degree_stratum_vertex_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (t : ℕ) (ht : 2*t≤G.maxDegree+1)
    {x y : V} (hxy : G.Adj x y) : t<G.degree x ∨ t<G.degree y := by
  by_contra h
  have hx : G.degree x≤t:=by omega
  have hy : G.degree y≤t:=by omega
  exact low_degree_stratum_independent G hcrit t ht hx hy hxy

/-- Count incidences with maximum-degree vertices from either endpoint. -/
theorem sum_maximumNeighbours (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ x : V,maximumNeighbours G x)=G.maxDegree*Gate8J.maximumDegreeCount G := by
  let M:=univ.filter fun y => G.degree y=G.maxDegree
  have h:=sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=univ) (t:=M)
    (r:=fun x y => G.Adj x y)
  have hleft : (∑ x : V,maximumNeighbours G x)=∑ x∈univ,(bipartiteAbove (fun x y => G.Adj x y) M x).card := by
    apply sum_congr rfl
    intro x _
    change ((G.neighborFinset x).filter fun z => G.degree z=G.maxDegree).card=_
    congr 1
    ext y
    simp only [bipartiteAbove,M,mem_filter,mem_univ,true_and,mem_neighborFinset]
    tauto
  rw [hleft,h]
  have he : ∀ y∈M,(bipartiteBelow (fun x y => G.Adj x y) univ y).card=G.maxDegree := by
    intro y hy
    have hyD:=(mem_filter.mp hy).2
    have hcard : (bipartiteBelow (fun x y => G.Adj x y) univ y).card=G.degree y := by
      rw [←card_neighborFinset_eq_degree]
      congr 1
      ext x
      simp only [bipartiteBelow,mem_filter,mem_univ,true_and,mem_neighborFinset]
      exact ⟨fun hxy => hxy.symm,fun hyx => hyx.symm⟩
    exact hcard.trans hyD
  rw [sum_congr rfl he,sum_const]
  change M.card • G.maxDegree=G.maxDegree*Gate8J.maximumDegreeCount G
  simp only [nsmul_eq_mul,Gate8J.maximumDegreeCount,M,Nat.mul_comm,Nat.cast_id]

/-- Every incident edge forces enough maximum-degree neighbours at its
other end. Summing gives a global restriction on all degree deficits. -/
theorem global_deficit_profile (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) :
    (∑ y : V,G.degree y*(G.maxDegree-G.degree y+1))≤
      Gate8J.maximumDegreeCount G*G.maxDegree^2 := by
  have hrow : ∀ y : V,G.degree y*(G.maxDegree-G.degree y+1)≤
      ∑ x : V,if G.Adj x y then maximumNeighbours G x else 0 := by
    intro y
    calc
      _ = ∑ x∈G.neighborFinset y,(G.maxDegree-G.degree y+1) := by
        simp only [sum_const,card_neighborFinset_eq_degree,nsmul_eq_mul,Nat.cast_id]
      _ ≤ ∑ x∈G.neighborFinset y,maximumNeighbours G x := by
        apply sum_le_sum
        intro x hx
        exact deficit_le_maximumNeighbours G hcrit ((mem_neighborFinset G y x).mp hx).symm
      _ = _ := by
        rw [←sum_filter]
        congr 1
        ext x
        simp only [mem_neighborFinset,mem_filter,mem_univ,true_and]
        exact ⟨fun hyx => hyx.symm,fun hxy => hxy.symm⟩
  calc
    _ ≤ ∑ y : V,∑ x : V,if G.Adj x y then maximumNeighbours G x else 0 :=
      sum_le_sum (fun y _ => hrow y)
    _ = ∑ x : V,maximumNeighbours G x*G.degree x := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [←sum_filter,sum_const,nsmul_eq_mul]
      have he : (univ.filter fun y => G.Adj x y).card=G.degree x := by
        rw [←card_neighborFinset_eq_degree]
        congr 1
        ext y
        simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
      rw [he,Nat.mul_comm]
      simp only [Nat.cast_id]
    _ ≤ ∑ x : V,maximumNeighbours G x*G.maxDegree :=
      sum_le_sum (fun x _ => Nat.mul_le_mul_left _ (G.degree_le_maxDegree x))
    _ = _ := by
      rw [←sum_mul,sum_maximumNeighbours]
      ring

/-- A tail bound for every deficit stratum, obtained without choosing a
single worst-degree vertex. -/
theorem deficit_stratum_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (r : ℕ) :
    G.minDegree*(r+1)*(univ.filter fun v => G.degree v+r≤G.maxDegree).card≤
      Gate8J.maximumDegreeCount G*G.maxDegree^2 := by
  let L:=univ.filter fun v => G.degree v+r≤G.maxDegree
  have hpoint : ∀ v∈L,G.minDegree*(r+1)≤G.degree v*(G.maxDegree-G.degree v+1) := by
    intro v hv
    have hh:=(mem_filter.mp hv).2
    exact Nat.mul_le_mul (G.minDegree_le_degree v) (by omega)
  calc
    _ = ∑ _v∈L,G.minDegree*(r+1) := by
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
      ring
    _ ≤ ∑ v∈L,G.degree v*(G.maxDegree-G.degree v+1):=sum_le_sum hpoint
    _ ≤ ∑ v : V,G.degree v*(G.maxDegree-G.degree v+1) := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _:=global_deficit_profile G hcrit

end OverfullWork.Gate8J2C
