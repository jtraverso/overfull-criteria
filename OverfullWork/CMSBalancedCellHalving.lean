module

public import Mathlib.Data.Fintype.Option
public import OverfullWork.CellBalancedPartition
public import OverfullWork.DirectedClusterQuotient
public import OverfullWork.RegularityCompatibleCompletionPartition

@[expose] public section


/-! The pairing step in the proof of CMS Lemma 5.4, on the actual
host rather than on its pure graph. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph PrunedCore DirectedClusterQuotient
open scoped Classical
universe u

/-- For each positive linear tolerance, one balanced cut splits all
even cells and the specified pair and controls all simple-graph rows. -/
theorem exists_halving_cut (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ m₀ : ℕ, ∀ {V I : Type u} [Fintype V] [DecidableEq V] [Fintype I]
      (G : SimpleGraph V) [DecidableRel G.Adj] (m l : ℕ) (f : V → Option I) (x y : V),
      m₀ ≤ m → Fintype.card V = 2*m → x ≠ y → f x = f y →
      (∀ i, Even (Fintype.card {v : V // f v = i})) →
      (∀ i, (cluster f i).card = 2*l) →
      ∃ A : Finset V, A.card = m ∧ Aᶜ.card = m ∧ (x ∈ A ↔ y ∉ A) ∧
        (∀ i, (A ∩ cluster f i).card = l) ∧
        (∀ i, (Aᶜ ∩ cluster f i).card = l) ∧
        ∀ v, |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)| < ζ*(m:ℝ) := by
  obtain ⟨m₀,hm₀⟩ := MultiGraph.eventually_sixth_size ζ hζ
  refine ⟨m₀,?_⟩
  intro V I _ _ _ G _ m l f x y hm hcard hxy hSame hEven hF
  let w : V → V → ℝ := fun z v => if G.Adj z v then 1 else 0
  have hw (z v : V) : 0 ≤ w z v ∧ w z v ≤ 1 := by
    dsimp only [w]
    split_ifs <;> norm_num
  have hsize : 15*(Fintype.card V:ℝ)*(m:ℝ)^3 < (ζ*(m:ℝ))^6 := by
    rw [hcard]
    push_cast
    nlinarith only [hm₀ m hm]
  obtain ⟨A,hA,hAc,hSep,hCells,hDis⟩ := CellBalancedPartition.exists_matrix_partition
    f m hcard hEven x y hxy hSame w hw (ζ*(m:ℝ)) (by positivity) hsize
  have hFilter (S : Finset V) (i : I) :
      (S.filter fun z => f z = some i) = S ∩ cluster f i := by
    ext z
    rw [mem_filter,mem_inter,mem_cluster]
  have hEach (i : I) : (A ∩ cluster f i).card = l ∧ (Aᶜ ∩ cluster f i).card = l := by
    have hs := RegularityCompatibleCompletionPartition.split_filter_card f A (some i)
    have he := hCells (some i)
    rw [hFilter A i,hFilter Aᶜ i,hFilter univ i,univ_inter,hF] at hs
    rw [hFilter A i,hFilter Aᶜ i] at he
    omega
  refine ⟨A,hA,hAc,hSep,fun i => (hEach i).1,fun i => (hEach i).2,?_⟩
  intro v
  have hN (S : Finset V) : (∑ z ∈ S, w v z) = (neighboursIn G S v:ℝ) := by
    rw [RobustExpansion.neighboursIn_eq_filter_card,card_filter,Nat.cast_sum]
    exact sum_congr rfl (fun z _ => by simp only [w,Nat.cast_ite,Nat.cast_one,Nat.cast_zero])
  simpa only [hN] using hDis v

/-- Use a common index type for both halves of a balanced cut. -/
theorem exists_embeddings_of_equal_card {V : Type u} [DecidableEq V]
    (A B : Finset V) (hCard : A.card = B.card) :
    ∃ a b : (↥A) ↪ V, (univ : Finset (↥A)).map a = A ∧ (univ : Finset (↥A)).map b = B := by
  let a : (↥A) ↪ V := Function.Embedding.subtype (· ∈ A)
  let e : (↥A) ≃ (↥B) := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hCard)
  let b : (↥A) ↪ V := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ B))
  refine ⟨a,b,?_,?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨w,_,rfl⟩ := mem_map.mp hv
      exact w.property
    · intro hv
      exact mem_map.mpr ⟨⟨v,hv⟩,mem_univ _,rfl⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨w,_,rfl⟩ := mem_map.mp hv
      exact (e w).property
    · intro hv
      exact mem_map.mpr ⟨e.symm ⟨v,hv⟩,mem_univ _,by simp [b]⟩

end OverfullWork.CMSBalancedCut
