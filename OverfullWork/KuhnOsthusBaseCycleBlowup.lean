module

public import OverfullWork.KuhnOsthusRegularCyclePair
public import OverfullWork.KuhnOsthusWalkBlowup
public import OverfullWork.KuhnOsthusPreprocessingAssembly
public import OverfullWork.KuhnOsthusWrappedPairCoordinates

@[expose] public section


/-! Kühn–Osthus Lemma 9.3(i). Sample and regularize the successor
pairs of the base cycle, and assemble their common-coordinate factors
into one physical reserve. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u
variable {V I X : Type*} [Fintype V] [Fintype X]

/-- Coordinates of a physical cluster, viewed as an embedding into
the ambient vertex set. -/
def clusterEmbedding {A : Finset V} (e : X ≃ A) : X ↪ V :=
  e.toEmbedding.trans (Function.Embedding.subtype (· ∈ A))

/-- The local normalized cycle reserves fit together without changing
any successor pair. Exact degrees in the union follow from the
permutation factorization and disjoint physical cells. -/
theorem assemble_regular_cycle_pairs (G : Digraph V) (s : Equiv.Perm I)
    (A : I → Finset V) (e : ∀ i, X ≃ A i) (k : ℕ) (η : ℝ)
    (D : I → Digraph X) (hDis : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hLe : ∀ i, D i ≤ pullDirectedPair (clusterEmbedding (e i)) (clusterEmbedding (e (s i))) G)
    (hReg : ∀ i x, inDegree (D i) x = k ∧ outDegree (D i) x = k)
    (hPair : ∀ i, IsCentredSuperregular (D i) η ((k:ℝ)/Fintype.card X)) :
    ∃ B : Digraph V, B ≤ G ∧
      (∀ i, IsCentredSuperregular
        (pullDirectedPair (clusterEmbedding (e i)) (clusterEmbedding (e (s i))) B)
        η ((k:ℝ)/Fintype.card X)) ∧
      (∀ i (x : A i), inDegree B x = k ∧ outDegree B x = k) ∧
      ∀ x y, B.Adj x y → ∃ i, x ∈ A i ∧ y ∈ A (s i) := by
  choose F hF hApart using fun i => exists_permutation_factorization_of_regular (D i) k (hReg i)
  let M (i : I) (b : Fin k) : A i ≃ A (s i) := ((e i).symm.trans (F i b)).trans (e (s i))
  let B := successorCellMatchingUnion A s M
  have hArc (i : I) (b : Fin k) (x : X) :
      M i b (e i x) = e (s i) (F i b x) := by simp [M]
  have hExact (i : I) :
      pullDirectedPair (clusterEmbedding (e i)) (clusterEmbedding (e (s i))) B = D i := by
    ext x y
    rw [← hF i]
    change (∃ (j : I) (b : Fin k) (a : A j), a.val = (e i x).val ∧
      (M j b a).val = (e (s i) y).val) ↔ ∃ b, F i b x = y
    constructor
    · rintro ⟨j,b,a,ha,hb⟩
      have ha' : (e i x).val ∈ A j := ha ▸ a.prop
      have hEq : j = i := by
        by_contra hn
        exact Finset.disjoint_left.mp (hDis j i hn) ha' (e i x).prop
      subst j
      have he : a = e i x := Subtype.ext ha
      rw [he,hArc] at hb
      exact ⟨b,(e (s i)).injective (Subtype.ext hb)⟩
    · rintro ⟨b,rfl⟩
      exact ⟨i,b,e i x,rfl,congrArg Subtype.val (hArc i b x)⟩
  refine ⟨B,?_,?_,?_,?_⟩
  · rintro x y ⟨i,b,a,rfl,rfl⟩
    have ha : (D i).Adj ((e i).symm a) (F i b ((e i).symm a)) := by
      rw [←hF i]
      exact ⟨b,rfl⟩
    have ht := hLe i ha
    change G.Adj ↑(e i ((e i).symm a)) ↑(e (s i) (F i b ((e i).symm a))) at ht
    simpa only [M,Equiv.trans_apply,Equiv.apply_symm_apply] using ht
  · intro i
    rw [hExact]
    exact hPair i
  · apply successor_cell_matching_union_degrees A s M hDis
    intro i b c hbc a h
    exact hApart i b c hbc ((e i).symm a) ((e (s i)).injective h)
  · rintro x y ⟨i,b,a,rfl,rfl⟩
    exact ⟨i,a.prop,(M i b a).prop⟩

/-- Construct the regular and superregular base-cycle reserve in a
host with normalized successor pairs. The input pairs may have
different centres above the common sampling density. -/
theorem kuhn_osthus_lemma_9_3_cycle_component (ε₀ ε η δ : ℝ)
    (hε₀ : 0 ≤ ε₀) (hSmall : ε₀ ≤ ε/4) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hTol : 2*(ε+δ) ≤ η) :
    ∃ N : ℕ, ∀ {V I : Type*} {X : Type u} [Fintype V] [Fintype X]
      (G : Digraph V) (s : Equiv.Perm I) (A : I → Finset V) (e : ∀ i, X ≃ A i)
      (k r loss : ℕ) (d' : ℝ) (d : I → ℝ),
      N ≤ Fintype.card X → 0 < d' → (∀ i, d' ≤ d i) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      (∀ i, IsCentredSuperregular
        (pullDirectedPair (clusterEmbedding (e i)) (clusterEmbedding (e (s i))) G) ε₀ (d i)) →
      ((Fintype.card X:ℝ)*ε ≤ r) →
      (((k+2*r : ℕ):ℝ) ≤ (d'-ε)*(Fintype.card X:ℝ)) →
      ((k:ℝ) ≤ (d'-2*ε)*(Fintype.card X:ℝ)) →
      ((d'+ε)*(Fintype.card X:ℝ) ≤ (k:ℝ)+loss) →
      ((loss:ℝ) ≤ δ*((Fintype.card X:ℝ)*η)) →
      ∃ B : Digraph V, B ≤ G ∧
        (∀ i, IsCentredSuperregular
          (pullDirectedPair (clusterEmbedding (e i)) (clusterEmbedding (e (s i))) B)
          η ((k:ℝ)/Fintype.card X)) ∧
        (∀ i (x : A i), inDegree B x = k ∧ outDegree B x = k) ∧
        ∀ x y, B.Adj x y → ∃ i, x ∈ A i ∧ y ∈ A (s i) := by
  obtain ⟨N,hN⟩ := exists_sampled_regular_superregular_cycle_pair.{u}
    ε₀ ε η δ hε₀ hSmall hε hε1 hη hη1 hδ hTol
  refine ⟨N,?_⟩
  intro V I X _ _ G s A e k r loss d' d hn hd hFloor hDis hPair hCut hDegrees hRect hLoss hBudget
  choose D hD using fun i => hN
    (pullDirectedPair (clusterEmbedding (e i)) (clusterEmbedding (e (s i))) G)
    k r loss (d i) d' hn hd (hFloor i) (hPair i) hCut hDegrees hRect hLoss hBudget
  exact assemble_regular_cycle_pairs G s A e k η D hDis
    (fun i => (hD i).1) (fun i => (hD i).2.2) (fun i => (hD i).2.1)

end OverfullWork.DirectedRobustExpansion
