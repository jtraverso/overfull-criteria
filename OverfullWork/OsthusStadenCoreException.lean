module

public import OverfullWork.OsthusStadenSliceRegularity
public import OverfullWork.DirectedMultiwaySplit

@[expose] public section


/-! The edge split of Claim 5.3 and the overlap estimate (26) for the
core exceptional vertices in Osthus–Staden §5.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- Divide the arcs of an oriented exceptional pair into `k` disjoint
pieces with a uniform additive degree error. The source lower bound and
target upper bound have the form used in Claim 5.3. -/
theorem exists_exceptional_pair_split (η : ℝ) (hη : 0 < η) (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (A B : Finset V),
      N ≤ Fintype.card V →
      ∃ parts : Fin k → Digraph V,
        (∀ i x y, (parts i).Adj x y → D.Adj x y ∧ x ∈ A ∧ y ∈ B) ∧
        (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ i x, x ∈ A → profileCount B (outProfile D x)/(k : ℝ) - η*(Fintype.card V : ℝ) ≤
          (outDegree (parts i) x : ℝ)) ∧
        ∀ i y, y ∈ B → (inDegree (parts i) y : ℝ) ≤
          profileCount A (inProfile D y)/(k : ℝ) + η*(Fintype.card V : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition_uniform.{u} (η/(k : ℝ)) (div_pos hη hkR)
  refine ⟨N,?_⟩
  intro V _ D A B hn
  let DAB : Digraph V := ⟨fun x y => D.Adj x y ∧ x ∈ A ∧ y ∈ B⟩
  obtain ⟨parts,residue,hParts,_,hDis,_,hCover⟩ := hN k (1/(k : ℝ)) (one_div_pos.mpr hkR)
    (by rw [mul_one_div_cancel hkR.ne']) DAB hn
  have hErr : (k : ℝ)*(η/(k : ℝ)) = η := by field_simp
  have hOut (x : V) (hx : x ∈ A) : (outDegree DAB x : ℝ) = profileCount B (outProfile D x) := by
    unfold outDegree profileCount outProfile
    congr 1
    congr 1
    ext y
    simp only [mem_filter,mem_univ,true_and,mem_inter,DAB,hx]
    tauto
  have hIn (y : V) (hy : y ∈ B) : (inDegree DAB y : ℝ) = profileCount A (inProfile D y) := by
    unfold inDegree inNeighbours profileCount inProfile
    congr 1
    congr 1
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_inter,DAB,hy,and_true]
    tauto
  refine ⟨parts,fun i x y h => (hCover x y).mpr (Or.inr ⟨i,h⟩),hDis,?_,?_⟩
  · intro i x hx
    have h := hParts i (Sum.inr (Sum.inl x))
    simp only [ArcStatistic.value,ArcStatistic.scale,hErr,hOut x hx,one_div,mul_comm ((k : ℝ)⁻¹),
      ←div_eq_mul_inv] at h
    linarith only [(abs_le.mp h).1]
  · intro i y hy
    have h := hParts i (Sum.inl y)
    simp only [ArcStatistic.value,ArcStatistic.scale,hErr,hIn y hy,one_div,mul_comm ((k : ℝ)⁻¹),
      ←div_eq_mul_inv] at h
    linarith only [(abs_le.mp h).2]

/-- Restricting a prepared piece to the intersection of the base and
adapted half-cell loses at most the vertices absent from the adapted
half-cell. This is the one-sided estimate in (26). -/
theorem exceptional_overlap_loss {V : Type*} (Q X X' : Finset V) :
    profileCount X Q - ((X \ X').card : ℝ) ≤ profileCount (X ∩ X') Q := by
  have h := (abs_le.mp (profile_count_dist_le X (X ∩ X') Q)).2
  have h₁ : (X ∩ X') \ X = ∅ := by
    apply sdiff_eq_empty_iff_subset.mpr
    exact inter_subset_left
  have h₂ : X \ (X ∩ X') = X \ X' := by
    ext x
    simp only [mem_sdiff,mem_inter]
    tauto
  rw [h₁,card_empty,max_eq_left (Nat.zero_le _),h₂] at h
  unfold profileCount
  linarith only [h]

/-- Once each exceptional vertex has at least `κ` arcs in either
direction, trim its two stars to exact size. The ambient subgraph
relation preserves all upper bounds and all previously assigned arcs'
disjointness. -/
theorem exists_trimmed_exceptional_arcs {V : Type*} [Fintype V]
    (D : Digraph V) (Z : Finset V) (κ : ℕ)
    (hIndependent : ∀ x ∈ Z, ∀ y ∈ Z, ¬ D.Adj x y)
    (hIn : ∀ x ∈ Z, κ ≤ inDegree D x) (hOut : ∀ x ∈ Z, κ ≤ outDegree D x) :
    ∃ E : Digraph V, E ≤ D ∧ (∀ x y, E.Adj x y → x ∈ Z ∨ y ∈ Z) ∧
      ∀ x ∈ Z, inDegree E x = κ ∧ outDegree E x = κ := by
  have hIn' (x : Z) : κ ≤ (inProfile D (x : V)).card := hIn x x.property
  have hOut' (x : Z) : κ ≤ (outProfile D (x : V)).card := hOut x x.property
  choose incoming hi hiCard using fun x => exists_subset_card_eq (hIn' x)
  choose outgoing ho hoCard using fun x => exists_subset_card_eq (hOut' x)
  let E : Digraph V := ⟨fun u v =>
    (∃ hv : v ∈ Z, u ∈ incoming ⟨v,hv⟩) ∨ (∃ hu : u ∈ Z, v ∈ outgoing ⟨u,hu⟩)⟩
  have he : E ≤ D := by
    rintro u v (⟨hv,h⟩ | ⟨hu,h⟩)
    · exact (mem_filter.mp (hi ⟨v,hv⟩ h)).2
    · exact (mem_filter.mp (ho ⟨u,hu⟩ h)).2
  refine ⟨E,he,?_,?_⟩
  · rintro u v (⟨hv,_⟩ | ⟨hu,_⟩)
    · exact Or.inr hv
    · exact Or.inl hu
  · intro x hx
    have hI : inProfile E x = incoming ⟨x,hx⟩ := by
      ext u
      simp only [inProfile,mem_filter,mem_univ,true_and]
      constructor
      · intro hu
        rcases hu with ⟨_,h⟩ | ⟨hu,h⟩
        · exact h
        · exact (hIndependent u hu x hx (he (Or.inr ⟨hu,h⟩))).elim
      · exact fun h => Or.inl ⟨hx,h⟩
    have hO : outProfile E x = outgoing ⟨x,hx⟩ := by
      ext v
      simp only [outProfile,mem_filter,mem_univ,true_and]
      constructor
      · intro hv
        rcases hv with ⟨hv,h⟩ | ⟨_,h⟩
        · exact (hIndependent x hx v hv (he (Or.inl ⟨hv,h⟩))).elim
        · exact h
      · exact fun h => Or.inr ⟨hx,h⟩
    exact ⟨(congrArg Finset.card hI).trans (hiCard ⟨x,hx⟩),
      (congrArg Finset.card hO).trans (hoCard ⟨x,hx⟩)⟩

end OverfullWork.DirectedRobustExpansion
