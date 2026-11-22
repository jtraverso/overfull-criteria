module

public import OverfullWork.RealRobustOrientation
public import OverfullWork.DirectedCenteredBatchBlocks
public import OverfullWork.DirectedPackingPrefix

@[expose] public section


/-! Final remainder transfer in Gao--Shan Theorem 2.12. Fixed layout
copies are separate from the host arc graph. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*}

/-- The host edges underlying a subdigraph of an orientation. -/
def hostEdges (G : SimpleGraph V) (U : Digraph V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (U.Adj x y ∨ U.Adj y x)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

/-- Host-edge deletion and oriented host-arc deletion agree. The
orientation is what prevents the reverse arc from surviving deletion. -/
theorem orientation_after_host_deletion {G : SimpleGraph V} {D U : Digraph V}
    (hD : IsOrientationOf D G) (hU : U ≤ D) :
    IsOrientationOf (D \ U) (G \ hostEdges G U) := by
  refine ⟨?_,?_,?_⟩
  · intro x y h
    refine ⟨hD.1 x y h.1,fun he => he.2.elim h.2 (fun hRev => hD.2.2 x y ⟨h.1,hU hRev⟩)⟩
  · intro x y h
    have hXY : ¬U.Adj x y := fun hu => h.2 ⟨h.1,Or.inl hu⟩
    have hYX : ¬U.Adj y x := fun hu => h.2 ⟨h.1,Or.inr hu⟩
    exact (hD.2.1 x y h.1).elim (fun ha => Or.inl ⟨ha,hXY⟩) (fun ha => Or.inr ⟨ha,hYX⟩)
  · exact fun x y h => hD.2.2 x y ⟨h.1.1,h.2.1⟩

/-- A robust directed subgraph certifies robustness of the underlying
simple graph with the same two normalized parameters. -/
theorem real_robust_of_directed_subgraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Digraph V) (ν τ : ℝ) (hAdj : ∀ x y, D.Adj x y → G.Adj x y)
    (hR : IsRealRobust D ν τ) : RobustExpansion.IsRealRobust G ν τ := by
  intro S hlo hhi
  have hSub : realNeighbourhood D ν S ⊆ RobustExpansion.realNeighbourhood G ν S := by
    intro v hv
    have hCount : inNeighbours D S v ≤ PrunedCore.neighboursIn G S v := by
      rw [RobustExpansion.neighboursIn_eq_filter_card]
      apply card_le_card
      intro x hx
      obtain ⟨hxS,hArc⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxS,(hAdj x v hArc).symm⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,(mem_filter.mp hv).2.trans ?_⟩
    exact_mod_cast hCount
  exact (hR S hlo hhi).trans (by exact_mod_cast card_le_card hSub)

set_option maxHeartbeats 2000000 in
/-- Robustness of the unused oriented reserve gives the robust
remainder in the original simple host. -/
theorem robust_host_after_packing [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {D Γ U : Digraph V} (hD : IsOrientationOf D G) (hΓ : Γ ≤ D) (hU : U ≤ D)
    {ν τ : ℝ} (hR : IsRealRobust (Γ \ U) ν τ) :
    RobustExpansion.IsRealRobust (G \ hostEdges G U) ν τ := by
  have hOr : IsOrientationOf (D \ U) (G \ hostEdges G U) := orientation_after_host_deletion hD hU
  have hsub : ∀ x y, (Γ \ U).Adj x y → (G \ hostEdges G U).Adj x y := by
    intro x y h
    exact hOr.1 x y ⟨hΓ h.1,h.2⟩
  exact real_robust_of_directed_subgraph (G \ hostEdges G U) (Γ \ U) ν τ hsub hR

/-- The orientation and reserve split in Gao--Shan, with the absolute
semidegree errors required at the input of the sampled batch theorem. -/
theorem exists_centered_oriented_reserve (a p ν τ ε : ℝ) (ha : 0 < a)
    (hp : 0 < p) (hp₁ : p < 1) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hSmall : 8*ε ≤ a) :
    ∃ N : ℕ, ∀ {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj],
      N ≤ Fintype.card W → RobustExpansion.IsRealRobust G ν τ →
      (∀ v, |(G.degree v:ℝ)-a*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ)) →
      ∃ D Γ : Digraph W, IsOrientationOf (D ⊔ Γ) G ∧ Disjoint D Γ ∧
        SemidegreesAround D (((1-p)*a/2)*(Fintype.card W:ℝ)) (2*ε*(Fintype.card W:ℝ)) ∧
        SemidegreesAround Γ ((p*a/2)*(Fintype.card W:ℝ)) (2*ε*(Fintype.card W:ℝ)) ∧
        IsRealRobust Γ (p*ν/8) τ := by
  obtain ⟨N₀,hOrient⟩ := BalancedRobustOrientation.exists_real_relative_orientation
    ν τ (a/2) ε hν hτ (by positivity) hε
  obtain ⟨N₁,hSplit⟩ := DirectedRobustSplit.exists_real_relative_split p (ν/4) τ (a/8) ε
    hp hp₁ (by positivity) hτ (by positivity) hε
  refine ⟨max N₀ N₁,?_⟩
  intro W _ G _ hn hR hDegrees
  let n := Fintype.card W
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hBase (v : W) : (a/2)*(n:ℝ) ≤ (G.degree v:ℝ) := by
    have h := (abs_le.mp (hDegrees v)).1
    have hb := mul_le_mul_of_nonneg_right hSmall hnR
    nlinarith only [h,hb,hε,hnR]
  obtain ⟨O,hO,hOI,hOO,hOR⟩ := hOrient G (by omega) hR hBase
  have hDegree (v : W) : (G.degree v:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast ((G.card_neighborFinset_eq_degree v).symm ▸ card_le_univ (G.neighborFinset v))
  have orientError (d : ℕ) (v : W) (h : |2*(d:ℝ)-(G.degree v:ℝ)| < ε*(G.degree v:ℝ)) :
      |(d:ℝ)-(a/2)*(n:ℝ)| ≤ ε*(n:ℝ) := by
    have hb := h.le.trans (mul_le_mul_of_nonneg_left (hDegree v) hε.le)
    obtain ⟨h₁,h₂⟩ := abs_le.mp hb
    obtain ⟨h₃,h₄⟩ := abs_le.mp (hDegrees v)
    exact abs_le.mpr ⟨by linarith only [h₁,h₃],by linarith only [h₂,h₄]⟩
  have hOC : SemidegreesAround O ((a/2)*(n:ℝ)) (ε*(n:ℝ)) :=
    fun v => ⟨orientError _ v (hOI v),orientError _ v (hOO v)⟩
  have hMin (d : ℕ) (h : |(d:ℝ)-(a/2)*(n:ℝ)| ≤ ε*(n:ℝ)) : (a/8)*(n:ℝ) ≤ (d:ℝ) := by
    have hb := mul_le_mul_of_nonneg_right hSmall hnR
    have hL := (abs_le.mp h).1
    nlinarith only [hb,hL,hε,hnR]
  obtain ⟨Γ,hΓ,hΓi,hΓo,hDi,hDo,hΓR,_⟩ := hSplit O (by omega) hOR
    (fun v => hMin _ (hOC v).1) (fun v => hMin _ (hOC v).2)
  have splitError (k : ℝ) (d f : ℕ) (hk : 0 ≤ k) (hk₁ : k ≤ 1) (hd : d ≤ n)
      (h₁ : |(d:ℝ)-(a/2)*(n:ℝ)| ≤ ε*(n:ℝ))
      (h₂ : |(f:ℝ)-k*(d:ℝ)| < ε*k*(d:ℝ)) :
      |(f:ℝ)-(k*a/2)*(n:ℝ)| ≤ 2*ε*(n:ℝ) := by
    have hdR : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hd
    have hPay : ε*k*(d:ℝ) ≤ ε*(n:ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hk₁ (Nat.cast_nonneg (α := ℝ) d)
      have h := mul_le_mul_of_nonneg_left (show k*(d:ℝ) ≤ n by linarith only [hh,hdR]) hε.le
      nlinarith only [h]
    have hPay' : k*|(d:ℝ)-(a/2)*(n:ℝ)| ≤ ε*(n:ℝ) := by
      calc
        _ ≤ k*(ε*(n:ℝ)) := mul_le_mul_of_nonneg_left h₁ hk
        _ ≤ 1*(ε*(n:ℝ)) := mul_le_mul_of_nonneg_right hk₁ (mul_nonneg hε.le hnR)
        _ = _ := one_mul _
    have he : k*(d:ℝ)-(k*a/2)*(n:ℝ) = k*((d:ℝ)-(a/2)*(n:ℝ)) := by ring
    have hTri := abs_sub_le (f:ℝ) (k*(d:ℝ)) ((k*a/2)*(n:ℝ))
    rw [he,abs_mul,abs_of_nonneg hk] at hTri
    linarith only [hTri,h₂,hPay,hPay']
  have hI (v : W) : inDegree O v ≤ n := card_le_univ _
  have hOut (v : W) : outDegree O v ≤ n := card_le_univ _
  obtain ⟨hUnion,hDis⟩ := DirectedArcSelection.exact_partition O Γ hΓ
  refine ⟨O \ Γ,Γ,?_,hDis.symm,fun v => ⟨?_,?_⟩,fun v => ⟨?_,?_⟩,?_⟩
  · rwa [sup_comm,hUnion]
  · exact splitError _ _ _ (by linarith) (by linarith) (hI v) (hOC v).1 (hDi v)
  · exact splitError _ _ _ (by linarith) (by linarith) (hOut v) (hOC v).2 (hDo v)
  · exact splitError _ _ _ hp.le hp₁.le (hI v) (hOC v).1 (hΓi v)
  · exact splitError _ _ _ hp.le hp₁.le (hOut v) (hOC v).2 (hΓo v)
  · convert hΓR using 1; ring

/-- The copy transport forgets the direction of each host arc, while
retaining the round and occurrence indices of every fixed copy. -/
def unorderedCopy {J I : Type*} : ((V × V) ⊕ (J × I)) → (Sym2 V ⊕ (J × I))
  | .inl (x,y) => .inl s(x,y)
  | .inr c => .inr c

private theorem unorderedCopy_eq_of_orientation {J I : Type*} {G : SimpleGraph V} {D : Digraph V}
    (hD : IsOrientationOf D G) (p q : (V × V) ⊕ (J × I))
    (hp : match p with | .inl (x,y) => D.Adj x y | .inr _ => True)
    (hq : match q with | .inl (x,y) => D.Adj x y | .inr _ => True)
    (he : unorderedCopy p = unorderedCopy q) : p = q := by
  cases p with
  | inl p =>
    cases q with
    | inr q => cases he
    | inl q =>
      obtain ⟨x,y⟩ := p
      obtain ⟨z,w⟩ := q
      rcases Sym2.eq_iff.mp (Sum.inl.inj he) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact (hD.2.2 x y ⟨hp,hq⟩).elim
  | inr p =>
    cases q with
    | inl q => cases he
    | inr q => exact congrArg Sum.inr (Sum.inr.inj he)

/-- In the unoriented graph the rounds still use pairwise disjoint
copies. In particular, two opposite orientations of one host edge
cannot be counted as different available copies. -/
theorem PackingPrefix.unordered_copies_pairwise {J I : Type*}
    {G : SimpleGraph V} {D : Digraph V} {L : J → Layout V I} {S : Finset J}
    (P : PackingPrefix D L S) (hD : IsOrientationOf D G) :
    Pairwise (fun i j => Disjoint (unorderedCopy '' P.copiesAt i) (unorderedCopy '' P.copiesAt j)) := by
  have hArc (i : S) (c : (V × V) ⊕ (J × I)) :
      c ∈ P.copiesAt i → (match c with | .inl (x,y) => D.Adj x y | .inr _ => True) := by
    cases c with
    | inl e => exact fun hc => (P.round i).used_le hc
    | inr e => exact fun _ => True.intro
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro c ⟨p,hp,hpc⟩ ⟨q,hq,hqc⟩
  have he := unorderedCopy_eq_of_orientation hD p q (hArc i p hp) (hArc j q hq) (hpc.trans hqc.symm)
  exact Set.disjoint_left.mp (P.copies_pairwise hij) hp (he.symm ▸ hq)

/-- Every flexible route becomes a simple path of the undirected host
with its original ordered list of vertices. -/
theorem Realization.undirected_path {I : Type*} {G : SimpleGraph V} {D : Digraph V}
    {L : Layout V I} (R : Realization D L) (hD : IsOrientationOf D G)
    (i : I) (hi : i ∉ L.fixed) :
    (R.word i).IsChain G.Adj ∧ (R.word i).Nodup :=
  ⟨(R.flexible_chain i hi).imp hD.1,R.simple i⟩

end OverfullWork.DirectedSpanningConfiguration
