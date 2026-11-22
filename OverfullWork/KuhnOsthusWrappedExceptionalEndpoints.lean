module

public import OverfullWork.KuhnOsthusExceptionalEndpoints
public import OverfullWork.KuhnOsthusExceptionalIntervalBalance

@[expose] public section


/-! Choose exceptional endpoints directly in the quotient coordinates.
Only the degree loss at the exceptional vertex enters the endpoint
selection in Lemma 7.5(i). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The generic endpoint selection can use the physical
neighbourhoods of an interval while returning labels in its quotient.
All labels are chosen in the prescribed interior set. -/
theorem exists_wrapped_exceptional_endpoints {V W I : Type*}
    [Fintype V] [Fintype W] [Fintype I] [Inhabited W]
    (G H : Digraph V) (hH : H ≤ G) (Z : Finset V) (A : Finset W) (f : W ↪ V)
    (cluster : W → I) (m cap budget loss : ℕ)
    (hSize : ∀ i, (intervalCluster cluster i).card ≤ m)
    (hBudget : 2*Z.card < cap*(budget+1))
    (hIn : ∀ z ∈ Z, 2*Z.card+budget*m+loss < inNeighbours G (A.map f) z)
    (hOut : ∀ z ∈ Z, 2*Z.card+budget*m+loss < outTo G (A.map f) z)
    (hLoss : ∀ z ∈ Z, inDegree (G \ H) z ≤ loss ∧ outDegree (G \ H) z ≤ loss) :
    ∃ endpoint : Bool × Z → W, Function.Injective endpoint ∧
      (∀ p, endpoint p ∈ A) ∧
      (∀ z : Z, H.Adj (f (endpoint (false,z))) z ∧ H.Adj z (f (endpoint (true,z)))) ∧
      ∀ i, ((univ : Finset (Bool × Z)).filter (fun p => cluster (endpoint p) = i)).card ≤ cap := by
  classical
  let K (p : Bool × Z) :=
    A.filter (fun v => if p.1 then H.Adj p.2 (f v) else H.Adj (f v) p.2)
  have hCount (p : V → Prop) :
      (A.filter (fun v => p (f v))).card = ((A.map f).filter p).card := by
    rw [filter_map,card_map]
    congr 1
  have hCard : Fintype.card (Bool × Z) = 2*Z.card := by simp
  have hRoom (p : Bool × Z) : Fintype.card (Bool × Z)+budget*m < (K p).card := by
    obtain ⟨b,z⟩ := p
    rw [hCard]
    obtain ⟨hi,ho⟩ := exceptional_style_neighbourhood_after_deletion G H (A.map f) z loss
      hH (hLoss z z.prop).1 (hLoss z z.prop).2
    cases b
    · simp only [K,Bool.false_eq_true,ite_false]
      rw [hCount (fun x => H.Adj x z)]
      change _ < inNeighbours H (A.map f) z
      have h := hIn z z.prop
      omega
    · simp only [K,ite_true]
      rw [hCount (H.Adj z)]
      change _ < outTo H (A.map f) z
      have h := hOut z z.prop
      omega
  obtain ⟨endpoint,hInj,hK,hCap⟩ := exists_distinct_representatives_with_cluster_cap
    cluster K m cap budget hSize (by rwa [hCard]) hRoom
  refine ⟨endpoint,hInj,fun p => (mem_filter.mp (hK p)).1,fun z => ?_,hCap⟩
  exact ⟨by simpa only [Bool.false_eq_true,ite_false] using (mem_filter.mp (hK (false,z))).2,
    by simpa only [ite_true] using (mem_filter.mp (hK (true,z))).2⟩

end OverfullWork.DirectedRobustExpansion
