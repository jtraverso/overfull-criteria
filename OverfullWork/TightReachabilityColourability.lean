module

public import OverfullWork.TightRoleReachability
public import OverfullWork.CriticalSaturatedDegreePairs
public import OverfullWork.FournierCoreCriterion

@[expose] public section


/-! # Reachable tight degree conflicts exclude critical obstructions

Each possible maximum seed need only reach two conflicting tight anchors.
The reachability paths can depend on the seed, and do not have to visit
all vertices of the combined core.
-/
namespace OverfullWork.EdgeKernel
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- A pair of tight anchors reachable from a proposed maximum seed,
whose saturated neighbour degrees violate the CCJS degree dichotomy. -/
def SeedConflict (G : SimpleGraph V) [DecidableRel G.Adj] (b : V) : Prop :=
  ∃ c d a z : V,
    Relation.ReflTransGen (tightRoleStep G) b c ∧
    Relation.ReflTransGen (tightRoleStep G) b d ∧
    c∈DeficitCore.core G ∧ d∈DeficitCore.core G ∧
    G.Adj c a ∧ G.Adj d z ∧
    neighboursIn G (DeficitCore.core G) c=G.maxDegree-G.degree a+1 ∧
    neighboursIn G (DeficitCore.core G) d=G.maxDegree-G.degree z+1 ∧
    z≠a ∧ G.degree a+G.degree z≤G.maxDegree ∧
    Fintype.card V+2*G.degree a≤G.degree z+G.maxDegree+5

/-- A genuine maximum role in any common-Delta critical copy cannot
carry a reachable conflict certificate. This preserves every possible
critical maximum, rather than merely supplying one acceptable seed. -/
theorem not_seedConflict_of_maximum_role
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : Copy H G) (hmax : H.maxDegree=G.maxDegree)
    (hcrit : Overfull.IsDeltaCritical H) (hactive : ∀ x,0<H.degree x)
    {b : W} (hbD : H.degree b=H.maxDegree) :
    ¬SeedConflict G (f b) := by
  intro hconflict
  obtain ⟨c,d,a,z,hbc,hbd,_hc,_hd,hca,hdz,hta,htz,hne,hlo,hforbidden⟩ := hconflict
  obtain ⟨cH,hcH,hcHD⟩ := maximum_role_of_reachable f hmax hcrit hactive hbD hbc
  obtain ⟨dH,hdH,hdHD⟩ := maximum_role_of_reachable f hmax hcrit hactive hbD hbd
  have hcaG : G.Adj (f cH) a := by simpa only [hcH] using hca
  have hdzG : G.Adj (f dH) z := by simpa only [hdH] using hdz
  obtain ⟨aH,hcHaH,haH⟩ := f.exists_adj_preimage_of_maximum_degree hmax cH hcHD hcaG
  obtain ⟨zH,hdHzH,hzH⟩ := f.exists_adj_preimage_of_maximum_degree hmax dH hdHD hdzG
  have hneH : zH≠aH := by
    intro he
    have hh := congrArg (fun x => f x) he
    rw [hzH,haH] at hh
    exact hne hh
  have hT := DeficitCore.critical_maximum_image_subset_core f hmax hcrit hactive
  apply not_tight_forbidden_degree_pair f hmax hcrit hactive
    (DeficitCore.core G) hT hcHaH hdHzH hneH
  · rw [hcH,haH]
    exact hta
  · rw [hdH,hzH]
    exact htz
  · rw [haH,hzH]
    omega
  · rw [haH,hzH]
    exact hforbidden

/-- A certificate for every possible core seed excludes every critical
copy. No density, overfullness or global clique hypothesis is required. -/
theorem edgeColourable_of_tight_reachability_conflicts (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hconflict : ∀ b∈DeficitCore.core G,SeedConflict G b) :
    G.EdgeColorable G.maxDegree := by
  by_contra hnc
  obtain ⟨w⟩ := FournierCore.exists_criticalCopy G hnc
  have : Nonempty w.vertices := w.critical.1.nonempty
  obtain ⟨b,hb⟩ := w.graph.exists_maximal_degree_vertex
  have hbD : w.graph.degree b=w.graph.maxDegree := hb.symm
  have hT := DeficitCore.critical_maximum_image_subset_core
    w.embedding w.maxDegree_eq w.critical w.no_isolates
  have hbT : w.embedding b∈DeficitCore.core G :=
    hT (mem_image.mpr ⟨b,mem_filter.mpr ⟨mem_univ b,hbD⟩,rfl⟩)
  exact not_seedConflict_of_maximum_role w.embedding w.maxDegree_eq
    w.critical w.no_isolates hbD (hconflict (w.embedding b) hbT)

theorem no_overfull_of_tight_reachability_conflicts (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hconflict : ∀ b∈DeficitCore.core G,SeedConflict G b) :
    ¬G.HasOverfullSubgraph :=
  Gate8D.no_overfull_of_colourable G
    (edgeColourable_of_tight_reachability_conflicts G hconflict)

end OverfullWork.EdgeKernel
