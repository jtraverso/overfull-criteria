module

public import OverfullWork.AlmostOverfullLayerCompatibility
public import OverfullWork.CriticalDenseCoreTrimming

@[expose] public section


/-! # Original-graph geometry of an almost-overfull odd set

No-overfullness pays the original odd cut, leaving at most the displayed
budget for edges in the complement. Two nonexceptional complementary
vertices exceed that same budget under the explicit gap. These are
original-graph statements, with no assumed star, factorization or compatible
future layer. The uniform interface keeps all integer scales before G.
-/
namespace OverfullWork.AlmostOverfullOriginalGeometry
open SimpleGraph Finset OddCutDeficit NearTightOddSetGeometry SparseDeficitCore
open AlmostOverfullLayerCompatibility
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- Express the original almost-budget as an odd cut and complementary edges. -/
theorem budget_eq_cut_deficit_add_internal (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) :
    deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)=
      cutEdges G X+deficitMass G G.maxDegree X+2*internalEdges G Xᶜ := by
  have hh:=internal_cut_identity G Xᶜ
  rw [cutEdges_compl] at hh
  omega

theorem cut_deficit_le_of_original_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (B : ℕ)
    (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    cutEdges G X+deficitMass G G.maxDegree X≤G.maxDegree+B := by
  have hh:=budget_eq_cut_deficit_add_internal G X
  omega

/-- The odd no-overfull cut consumes Delta, leaving at most B internal
complementary incidences. -/
theorem twice_internal_complement_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hno : ¬G.HasOverfullSubgraph) (X : Finset V) (hodd : Odd X.card) (B : ℕ)
    (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    2*internalEdges G Xᶜ≤B := by
  have hlo:=(no_overfull_iff_odd_cut_deficit G).mp hno X hodd
  have hh:=budget_eq_cut_deficit_add_internal G X
  omega

/-- This part needs only the actual original budget. Two high vertices
would already spend more than Delta+B in the complement. -/
theorem nonexceptional_complement_card_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (a B : ℕ) (hgap : 2*a+B<G.maxDegree)
    (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    (Xᶜ\exceptions G G.maxDegree a).card≤1 := by
  apply card_le_one.mpr
  intro v hv w hw
  by_contra hne
  have hvY:=(mem_sdiff.mp hv).1
  have hwY:=(mem_sdiff.mp hw).1
  have hvD:=degree_add_threshold_of_not_exception G G.maxDegree a v (mem_sdiff.mp hv).2
  have hwD:=degree_add_threshold_of_not_exception G G.maxDegree a w (mem_sdiff.mp hw).2
  have hs : ({v,w}:Finset V)⊆Xᶜ := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact hvY
    · exact mem_singleton.mp hz ▸ hwY
  have hh:=(sum_le_sum_of_subset_of_nonneg hs
    (fun _ _ _=>Nat.zero_le _) : (∑z∈({v,w}:Finset V),G.degree z)≤∑z∈Xᶜ,G.degree z)
  have hpair : (∑z∈({v,w}:Finset V),G.degree z)=G.degree v+G.degree w := by simp [hne]
  rw [hpair] at hh
  omega

theorem complement_card_le_exceptions_add_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (a B : ℕ) (hgap : 2*a+B<G.maxDegree)
    (hbudget : deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B) :
    Xᶜ.card≤(exceptions G G.maxDegree a).card+1 := by
  have hh:=nonexceptional_complement_card_le_one G X a B hgap hbudget
  have hc:=card_le_card_sdiff_add_card (s:=Xᶜ) (t:=exceptions G G.maxDegree a)
  omega

/-- Unpack the almost-overfull witness and obtain all original geometry
without any residual graph hypothesis. -/
theorem exists_original_geometry (G : SimpleGraph V) [DecidableRel G.Adj]
    (a B : ℕ) (hno : ¬G.HasOverfullSubgraph) (hgap : 2*a+B<G.maxDegree)
    (halmost : HasOddAlmostOverfullSet G B) :
    ∃X : Finset V,Odd X.card ∧
      deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B ∧
      cutEdges G X+deficitMass G G.maxDegree X≤G.maxDegree+B ∧
      2*internalEdges G Xᶜ≤B ∧
      (Xᶜ\exceptions G G.maxDegree a).card≤1 ∧
      Xᶜ.card≤(exceptions G G.maxDegree a).card+1 := by
  obtain ⟨X,hodd,hbudget⟩:=halmost
  exact ⟨X,hodd,hbudget,cut_deficit_le_of_original_budget G X B hbudget,
    twice_internal_complement_le G hno X hodd B hbudget,
    nonexceptional_complement_card_le_one G X a B hgap hbudget,
    complement_card_le_exceptions_add_one G X a B hgap hbudget⟩

/-- Uniform localization of the original almost-set for any two supplied
construction/localization scales. All three scales precede the graph.
The complement is small and sparse, with no star conclusion. -/
theorem above_half_original_almost_geometry (ε : ℝ) (hε : 0<ε) :
    ∃qT : ℕ,2≤qT ∧ ∃N : ℕ,∀qR qS : ℕ,2≤qR → 2≤qS →
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let a:=Fintype.card V/(8*qT)
        let kT:=Fintype.card V/(4096*qT^2)
        let B:=2*(Fintype.card V/(4096*qR^2))+2+8*(Fintype.card V/(4096*qS^2))
        HasOddAlmostOverfullSet G B →
        ∃X : Finset V,Odd X.card ∧
          deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v)≤G.maxDegree+B ∧
          cutEdges G X+deficitMass G G.maxDegree X≤G.maxDegree+B ∧
          2*internalEdges G Xᶜ≤B ∧
          (Xᶜ\exceptions G G.maxDegree a).card≤1 ∧ Xᶜ.card≤kT+1 := by
  obtain ⟨qT,hqT,N,hprep⟩:=CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨qT,hqT,max N 16,?_⟩
  intro qR qS hqR hqS V _ _ G _ hn hc hdense hno
  obtain ⟨_,hUk,_⟩:=hprep G ((le_max_left _ _).trans hn) hc hdense
  dsimp only
  intro halmost
  let n:=Fintype.card V
  let a:=n/(8*qT)
  let kR:=n/(4096*qR^2)
  let kS:=n/(4096*qS^2)
  let B:=2*kR+2+8*kS
  have hn16 : 16≤n := (le_max_right _ _).trans hn
  have hnD : n≤2*G.maxDegree := by
    have he:0≤ε*(n:ℝ):=by positivity
    exact_mod_cast (show (n:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have ha : 16*a≤n :=
    (Nat.mul_le_mul_right a (show 16≤8*qT by omega)).trans (Nat.mul_div_le n (8*qT))
  have hkR : 64*kR≤n :=
    (Nat.mul_le_mul_right kR (show 64≤4096*qR^2 by nlinarith [sq_nonneg (qR:ℤ)])).trans
      (Nat.mul_div_le n (4096*qR^2))
  have hkS : 64*kS≤n :=
    (Nat.mul_le_mul_right kS (show 64≤4096*qS^2 by nlinarith [sq_nonneg (qS:ℤ)])).trans
      (Nat.mul_div_le n (4096*qS^2))
  have hgap : 2*a+B<G.maxDegree := by dsimp only [B];omega
  obtain ⟨X,hodd,hbudget,hcut,hsparse,hhigh,hcard⟩:=exists_original_geometry G a B hno hgap halmost
  refine ⟨X,hodd,hbudget,hcut,hsparse,hhigh,?_⟩
  exact hcard.trans (Nat.add_le_add_right hUk 1)

end OverfullWork.AlmostOverfullOriginalGeometry
