module

public import OverfullWork.CriticalDenseCoreTrimming
public import OverfullWork.LowSkeletonProjection

@[expose] public section


/-! # Critical low partners have actual distinct core representatives

The degree budget in the finite projection construction is discharged
by VAL and the proved critical deficit theorem. This is the representative
selection in CMS Operation 4.1, Step 2; it does not require a two-matching
union that saturates every low vertex twice to be acyclic.
-/
namespace OverfullWork.CriticalLowPartnerProjection
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open scoped Classical
universe u
set_option maxHeartbeats 3000000

/-- A sufficiently high deficit threshold contains every critical low
vertex. The numerical hypotheses make the inclusion strict. -/
theorem lowVertices_subset_exceptions {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℕ)
    (hD : 0<G.maxDegree) (ha : 8*a≤G.maxDegree) :
    lowVertices G⊆exceptions G G.maxDegree a := by
  intro w hw
  have hd:=(mem_filter.mp hw).2
  exact mem_filter.mpr ⟨mem_univ _,by omega⟩

/-- The degree inequality required to construct representatives holds
for any small family of actual neighbours of low vertices. -/
theorem exists_projection_of_low_partners {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : Overfull.IsDeltaCritical G)
    (a k : ℕ) (hD : 0<G.maxDegree) (ha : 8*a≤G.maxDegree)
    (hscale : 2*k+1≤a)
    (hU : (exceptions G G.maxDegree a).card≤k) (A : Finset V)
    (hA : A.card≤(lowVertices G).card+1)
    (hpartner : ∀x∈A,∃w∈lowVertices G,G.Adj w x) :
    Nonempty (LowSkeletonProjection.Projection G A (exceptions G G.maxDegree a) ∅) := by
  classical
  apply LowSkeletonProjection.exists_projection_without_extra_forbidden
  intro x hx
  obtain ⟨hxA,_⟩:=mem_inter.mp hx
  obtain ⟨w,hw,hwx⟩:=hpartner x hxA
  have hwlow:=(mem_filter.mp hw).2
  have hval:=Overfull.deg_add hc hwx
  have hW : (lowVertices G).card≤k :=
    (card_le_card (lowVertices_subset_exceptions G a hD ha)).trans hU
  omega

/-- There is also room to forbid the whole support of a sparse skeleton,
rather than merely its degree-one endpoints. -/
theorem exists_projection_avoiding_of_low_partners {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : Overfull.IsDeltaCritical G)
    (a k : ℕ) (hD : 0<G.maxDegree) (ha : 8*a≤G.maxDegree)
    (hscale : 2*k+1≤a)
    (hU : (exceptions G G.maxDegree a).card≤k) (A Z : Finset V)
    (hA : A.card≤(lowVertices G).card+1)
    (hZ : Z.card≤2*((lowVertices G).card+1))
    (hpartner : ∀x∈A,∃w∈lowVertices G,G.Adj w x) :
    Nonempty (LowSkeletonProjection.Projection G A (exceptions G G.maxDegree a) Z) := by
  classical
  apply LowSkeletonProjection.exists_projection
  intro x hx
  obtain ⟨hxA,_⟩:=mem_inter.mp hx
  obtain ⟨w,hw,hwx⟩:=hpartner x hxA
  have hwlow:=(mem_filter.mp hw).2
  have hval:=Overfull.deg_add hc hwx
  have hW : (lowVertices G).card≤k :=
    (card_le_card (lowVertices_subset_exceptions G a hD ha)).trans hU
  omega

/-- Above one half, the critical deficit theorem supplies a core to
which every small low-partner family can be projected injectively.
The representatives and their matching are constructed, not assumed. -/
theorem above_half_low_partner_projection_avoiding (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        ∀A Z : Finset V,A.card≤(lowVertices G).card+1 →
          Z.card≤2*((lowVertices G).card+1) →
          (∀x∈A,∃w∈lowVertices G,G.Adj w x) →
          Nonempty (LowSkeletonProjection.Projection G A U Z) := by
  obtain ⟨q,hq,N,hcore⟩:=CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro V _ _ G _ hn hc hdense
  obtain ⟨hk,hU,_⟩:=hcore G hn hc hdense
  let a:=Fintype.card V/(8*q)
  let k:=Fintype.card V/(4096*q^2)
  have hkpos : 0<k := hk
  have hnscale : 4096*q^2≤Fintype.card V := by
    have hh:=(Nat.le_div_iff_mul_le (by positivity : 0<4096*q^2)).mp
      (show 1≤k by omega)
    simpa using hh
  obtain ⟨_,_,hscale,_,_⟩:=RobustExpansion.sparse_deficit_integer_scales
    (Fintype.card V) q hq hnscale
  change 2*k+1≤a at hscale
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have hafloor : 8*q*a≤Fintype.card V := Nat.mul_div_le (Fintype.card V) (8*q)
  have h16 : 16*a≤Fintype.card V :=
    (Nat.mul_le_mul_right a (by omega : 16≤8*q)).trans hafloor
  have ha : 8*a≤G.maxDegree := by omega
  have hD : 0<G.maxDegree := by omega
  dsimp only
  intro A Z hA hZ hpartner
  exact exists_projection_avoiding_of_low_partners G hc a k hD ha hscale hU A Z hA hZ hpartner

/-- The interface with no additional forbidden vertices. -/
theorem above_half_low_partner_projection (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        ∀A : Finset V,A.card≤(lowVertices G).card+1 →
          (∀x∈A,∃w∈lowVertices G,G.Adj w x) →
          Nonempty (LowSkeletonProjection.Projection G A U ∅) := by
  obtain ⟨q,hq,N,hproj⟩:=above_half_low_partner_projection_avoiding.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro V _ _ G _ hn hc hdense
  dsimp only
  intro A hA hp
  exact hproj G hn hc hdense A ∅ hA (by simp) hp

end OverfullWork.CriticalLowPartnerProjection
