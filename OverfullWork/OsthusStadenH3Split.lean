module

public import OverfullWork.RegularPairArcPartition

@[expose] public section


/-! Carve the H3 merging reserve from each successor pair as in
Osthus–Staden §5.10. The reserve and the remainder stay superregular. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical
universe u
variable {W : Type u} [Fintype W]

/-- The two sides of a balanced pair are indexed by the same type. -/
def IsCentredSuperregular (D : Digraph W) (ε d : ℝ) : Prop :=
  IsCentredRegular D ε d ∧
  ∀ v, |(inDegree D v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) ∧
    |(outDegree D v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ)

theorem exists_h3_superregular_split (p ε δ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hSmall : ε ≤ δ/4) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D : Digraph W) (d : ℝ),
      N ≤ Fintype.card W → IsCentredSuperregular D ε d →
      ∃ H R : Digraph W, IsCentredSuperregular H δ (p*d) ∧
        IsCentredSuperregular R δ ((1-p)*d) ∧ Disjoint H R ∧ D = H ⊔ R := by
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition_uniform.{u} (δ^3/4) (by positivity)
  refine ⟨max N 1,?_⟩
  intro W _ D d hn hD
  obtain ⟨F,R,hF,hR,_,hDis,hCover⟩ := hN 1 p hp (by simpa using hp1) D ((le_max_left N 1).trans hn)
  have hNpos : 0 < Fintype.card W := (le_max_right N 1).trans hn
  have hTrackF : TracksArcStatistics (F 0) D p (δ^3/4) := by simpa using hF (0 : Fin 1)
  have hTrackR : TracksArcStatistics R D (1-p) (δ^3/4) := by simpa using hR
  have hSuper (A : Digraph W) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (hA : TracksArcStatistics A D q (δ^3/4)) : IsCentredSuperregular A δ (q*d) := by
    refine ⟨centred_regular_of_tracking hA hq hq1 hD.1 hε hSmall hδ hδ1 le_rfl hNpos,?_⟩
    have ht := typical_semidegrees_of_tracking (d := d) hA hq hq1 hε hSmall hδ hδ1 le_rfl
    exact fun v => ⟨ht.1 v (hD.2 v).1,ht.2 v (hD.2 v).2⟩
  refine ⟨F 0,R,hSuper _ _ hp.le hp1 hTrackF,
    hSuper _ _ (sub_nonneg.mpr hp1) (by linarith only [hp]) hTrackR,hDis 0,?_⟩
  ext x y
  rw [Digraph.sup_adj,hCover]
  constructor
  · rintro (h | ⟨i,h⟩)
    · exact Or.inr h
    · exact Or.inl (by simpa only [show i = 0 from Subsingleton.elim _ _] using h)
  · rintro (h | h)
    · exact Or.inr ⟨0,h⟩
    · exact Or.inl h

end OverfullWork.DirectedRegularPairs
