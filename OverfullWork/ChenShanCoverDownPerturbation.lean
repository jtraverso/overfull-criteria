module

public import OverfullWork.ChenShanCoverDownExterior
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical symmDiff

section Neighborhoods

variable {V : Type*}

noncomputable def arcNeighborsIn (U : Finset V) (G : Finset (V × V)) (v : V) : Finset V :=
  U.filter (fun w => (v,w) ∈ G ∨ (w,v) ∈ G)

@[simp] theorem mem_arcNeighborsIn (U : Finset V) (G : Finset (V × V)) (v w : V) :
    w ∈ arcNeighborsIn U G v ↔ w ∈ U ∧ ((v,w) ∈ G ∨ (w,v) ∈ G) := by
  simp only [arcNeighborsIn,mem_filter]

theorem arcNeighborsIn_card_le_incidentDegree
    (U : Finset V) (G : Finset (V × V)) (v : V) :
    (arcNeighborsIn U G v).card ≤ incidentDegree G v := by
  let f (w : V) := if (v,w) ∈ G then (v,w) else (w,v)
  have hf : Function.Injective f := by
    intro x y h
    by_cases hx : (v,x) ∈ G <;> by_cases hy : (v,y) ∈ G <;>
      simp only [f,hx,hy,ite_true,ite_false,Prod.mk.injEq] at h <;> grind
  let F : V ↪ V × V := ⟨f,hf⟩
  rw [← card_map F]
  apply card_le_card
  intro e he
  obtain ⟨w,hw,rfl⟩ := mem_map.mp he
  have hw' := (mem_arcNeighborsIn U G v w).mp hw
  by_cases h : (v,w) ∈ G
  · have hEq : F w = (v,w) := ite_eq_left h
    rw [hEq]
    exact mem_filter.mpr ⟨h,Or.inl rfl⟩
  · have hEq : F w = (w,v) := ite_eq_right h
    rw [hEq]
    exact mem_filter.mpr ⟨hw'.2.resolve_left h,Or.inr rfl⟩

/-- Deletion and addition control their respective sides of the change
in the neighborhood, regardless of the orientation of the arcs. -/
theorem arcNeighborsIn_change (U : Finset V) (R C J : Finset (V × V)) (v : V) :
    let Y := arcNeighborsIn U R v
    let Y' := arcNeighborsIn U ((R \ C) ∪ J) v
    (Y \ Y').card ≤ incidentDegree C v ∧
      (Y' \ Y).card ≤ incidentDegree J v := by
  intro Y Y'
  constructor
  · refine (card_le_card (t := arcNeighborsIn U C v) ?_).trans
      (arcNeighborsIn_card_le_incidentDegree U C v)
    intro w hw
    have h := mem_sdiff.mp hw
    have hOld := (mem_arcNeighborsIn U R v w).mp h.1
    refine (mem_arcNeighborsIn U C v w).mpr ⟨hOld.1,?_⟩
    by_contra hn
    push Not at hn
    apply h.2
    refine (mem_arcNeighborsIn U ((R \ C) ∪ J) v w).mpr ⟨hOld.1,?_⟩
    exact hOld.2.imp (fun he => mem_union_left _ (mem_sdiff.mpr ⟨he,hn.1⟩))
      (fun he => mem_union_left _ (mem_sdiff.mpr ⟨he,hn.2⟩))
  · refine (card_le_card (t := arcNeighborsIn U J v) ?_).trans
      (arcNeighborsIn_card_le_incidentDegree U J v)
    intro w hw
    have h := mem_sdiff.mp hw
    have hNew := (mem_arcNeighborsIn U ((R \ C) ∪ J) v w).mp h.1
    have hNo : ¬ ((v,w) ∈ R ∨ (w,v) ∈ R) := fun hh =>
      h.2 ((mem_arcNeighborsIn U R v w).mpr ⟨hNew.1,hh⟩)
    have hp := not_or.mp hNo
    refine (mem_arcNeighborsIn U J v w).mpr ⟨hNew.1,?_⟩
    exact hNew.2.imp (fun he => (mem_union.mp he).resolve_left (fun he => hp.1 (mem_sdiff.mp he).1))
      (fun he => (mem_union.mp he).resolve_left (fun he => hp.2 (mem_sdiff.mp he).1))

private theorem card_le_card_add_sdiff (S T : Finset V) :
    S.card ≤ T.card + (S \ T).card := by
  refine (card_le_card (t := T ∪ (S \ T)) ?_).trans (card_union_le _ _)
  intro x hx
  by_cases ht : x ∈ T
  · exact mem_union_left _ ht
  · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,ht⟩)

private theorem intersection_card_after_changes (A B A' B' : Finset V) :
    (A' ∩ B').card ≤ (A ∩ B).card + (A' \ A).card + (B' \ B).card := by
  refine (card_le_card (t := ((A ∩ B) ∪ (A' \ A)) ∪ (B' \ B)) ?_).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  intro x hx
  obtain ⟨ha,hb⟩ := mem_inter.mp hx
  by_cases ha₀ : x ∈ A
  · by_cases hb₀ : x ∈ B
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨ha₀,hb₀⟩))
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hb,hb₀⟩)
  · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨ha,ha₀⟩))

/-- The quantitative neighborhood bounds in (4.25) once the reserve
arcs consumed at each exterior vertex are bounded by the leave degree. -/
theorem cover_down_modified_neighborhood_bounds (U X : Finset V)
    (R C J : Finset (V × V)) {μ ρ n ζ : ℝ}
    (hC : ∀ v ∈ X, (incidentDegree C v : ℝ) ≤ ζ*n)
    (hJ : ∀ v, (incidentDegree J v : ℝ) ≤ ζ*n)
    (hR : ∀ v, (incidentDegree R v : ℝ) ≤ 10*μ*n)
    (hR3 : ∀ u ∈ X, ∀ v ∈ X, u ≠ v →
      (((arcNeighborsIn U R u) ∩ (arcNeighborsIn U R v)).card : ℝ) ≤ 50*μ^2*ρ*n)
    (hPair : 2*ζ*n ≤ 50*μ^2*ρ*n) (hLoad : ζ*n ≤ 10*μ*n) :
    let R' := (R \ C) ∪ J
    let Y := arcNeighborsIn U R
    let Y' := arcNeighborsIn U R'
    (∀ v ∈ X, (((Y v) ∆ (Y' v)).card : ℝ) ≤ 2*ζ*n) ∧
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v →
      (((Y' u) ∩ (Y' v)).card : ℝ) ≤ 100*μ^2*ρ*n) ∧
    (∀ v, ((arcNeighborsIn X R' v).card : ℝ) ≤ 20*μ*n) := by
  intro R' Y Y'
  have hRemoved (v) (hv : v ∈ X) : (((Y v) \ (Y' v)).card : ℝ) ≤ ζ*n := by
    have h := (arcNeighborsIn_change U R C J v).1
    have hb : (((Y v) \ (Y' v)).card : ℝ) ≤ incidentDegree C v := by exact_mod_cast h
    exact hb.trans (hC v hv)
  have hAdded (v) : (((Y' v) \ (Y v)).card : ℝ) ≤ ζ*n := by
    have h := (arcNeighborsIn_change U R C J v).2
    have hb : (((Y' v) \ (Y v)).card : ℝ) ≤ incidentDegree J v := by exact_mod_cast h
    exact hb.trans (hJ v)
  refine ⟨?_,?_,?_⟩
  · intro v hv
    rw [Finset.symmDiff_def]
    have h : ((((Y v) \ (Y' v)) ∪ ((Y' v) \ (Y v))).card : ℝ) ≤
        (((Y v) \ (Y' v)).card : ℝ) + (((Y' v) \ (Y v)).card : ℝ) := by
      exact_mod_cast card_union_le ((Y v) \ (Y' v)) ((Y' v) \ (Y v))
    linarith only [h,hRemoved v hv,hAdded v]
  · intro u hu v hv hne
    have h : (((Y' u) ∩ (Y' v)).card : ℝ) ≤ (((Y u) ∩ (Y v)).card : ℝ) +
        (((Y' u) \ (Y u)).card : ℝ) + (((Y' v) \ (Y v)).card : ℝ) := by
      exact_mod_cast intersection_card_after_changes (Y u) (Y v) (Y' u) (Y' v)
    linarith only [h,hAdded u,hAdded v,hR3 u hu v hv hne,hPair]
  · intro v
    have h₁ : ((arcNeighborsIn X R' v).card : ℝ) ≤ (arcNeighborsIn X R v).card +
        ((arcNeighborsIn X R' v \ arcNeighborsIn X R v).card : ℝ) := by
      exact_mod_cast card_le_card_add_sdiff (arcNeighborsIn X R' v) (arcNeighborsIn X R v)
    have h₂ : ((arcNeighborsIn X R v).card : ℝ) ≤ incidentDegree R v := by
      exact_mod_cast arcNeighborsIn_card_le_incidentDegree X R v
    have h₃ : ((arcNeighborsIn X R' v \ arcNeighborsIn X R v).card : ℝ) ≤ incidentDegree J v := by
      exact_mod_cast (arcNeighborsIn_change X R C J v).2
    linarith only [h₁,h₂,h₃,hJ v,hR v,hLoad]

/-- Removing the protected induced graph costs only old neighbors in the
protected set. The separate loss and gain bounds then transfer the
degree margin of (R4) to the modified neighborhood in (4.26). -/
theorem cover_down_protected_degree
    (Y Y' K : Finset V) (sourceOutside : Prop) (A : V → Prop) {η B d : ℝ}
    (hη : 0 ≤ η)
    (hOld : (1/2+8*η)*(Y.card : ℝ) ≤ (Y.filter A).card)
    (hProt : ((Y ∩ K).card : ℝ) ≤ B)
    (hLost : ((Y \ Y').card : ℝ) ≤ d) (hGain : ((Y' \ Y).card : ℝ) ≤ d)
    (hSlack : B+(3/2+η)*d ≤ 7*η*(Y.card : ℝ)) :
    (1/2+η)*(Y'.card : ℝ) ≤ (Y'.filter (fun z => A z ∧ (sourceOutside ∨ z ∉ K))).card := by
  let O := Y'.filter (fun z => A z ∧ (sourceOutside ∨ z ∉ K))
  have hSub : Y.filter A ⊆ (O ∪ (Y \ Y')) ∪ (Y ∩ K) := by
    intro z hz
    obtain ⟨hy,ha⟩ := mem_filter.mp hz
    by_cases h' : z ∈ Y'
    · by_cases hk : z ∈ K
      · exact mem_union_right _ (mem_inter.mpr ⟨hy,hk⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨h',ha,Or.inr hk⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hy,h'⟩))
  have hSum : ((Y.filter A).card : ℝ) ≤ (O.card : ℝ)+((Y \ Y').card : ℝ)+((Y ∩ K).card : ℝ) := by
    exact_mod_cast (card_le_card hSub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hSize : (Y'.card : ℝ) ≤ (Y.card : ℝ) + ((Y' \ Y).card : ℝ) := by
    exact_mod_cast card_le_card_add_sdiff Y' Y
  have hNew := mul_le_mul_of_nonneg_left
    (show (Y'.card : ℝ) ≤ (Y.card : ℝ)+d by linarith only [hSize,hGain])
    (show 0 ≤ 1/2+η by positivity)
  change (1/2+η)*(Y'.card : ℝ) ≤ (O.card : ℝ)
  linarith only [hNew,hSum,hOld,hProt,hLost,hSlack]

/-- The lower bound in (4.25) follows on each of the two eligible parts. -/
theorem cover_down_modified_part_lower (Z : Finset V) (R C J : Finset (V × V)) (u : V)
    {μ ρ n ζ : ℝ}
    (hOld : μ*(ρ*n)/4 ≤ ((arcNeighborsIn Z R u).card : ℝ))
    (hC : (incidentDegree C u : ℝ) ≤ ζ*n) (hSmall : ζ*n ≤ μ*(ρ*n)/8) :
    μ*(ρ*n)/8 ≤ ((arcNeighborsIn Z ((R \ C) ∪ J) u).card : ℝ) := by
  let Y := arcNeighborsIn Z R u
  let Y' := arcNeighborsIn Z ((R \ C) ∪ J) u
  have hLoss : ((Y \ Y').card : ℝ) ≤ incidentDegree C u := by
    exact_mod_cast (arcNeighborsIn_change Z R C J u).1
  have hSize : (Y.card : ℝ) ≤ Y'.card + ((Y \ Y').card : ℝ) := by
    exact_mod_cast card_le_card_add_sdiff Y Y'
  change μ*(ρ*n)/8 ≤ (Y'.card : ℝ)
  linarith only [hSize,hLoss,hOld,hC,hSmall]

/-- Deleting the balanced exterior cover leaves the induced interior
and the updated crossing reserve, still balanced together. -/
theorem cover_down_balance_after_exterior
    (GU R L D C : Finset (V × V)) (hD : D ⊆ L) (hC : C ⊆ R)
    (hUR : Disjoint GU R) (hUL : Disjoint GU L) (hRL : Disjoint R L)
    (hBal : ArcBalanced (GU ∪ R ∪ L)) (hCovered : ArcBalanced (D ∪ C)) :
    ArcBalanced (GU ∪ ((R \ C) ∪ (L \ D))) := by
  have hSub : D ∪ C ⊆ GU ∪ R ∪ L :=
    union_subset (fun e he => mem_union_right _ (hD he))
      (fun e he => mem_union_left _ (mem_union_right _ (hC he)))
  have hEq : ((GU ∪ R ∪ L) \ (D ∪ C)) = GU ∪ ((R \ C) ∪ (L \ D)) := by
    ext e
    have hd : e ∈ D → e ∈ L := fun h => hD h
    have hc : e ∈ C → e ∈ R := fun h => hC h
    have hUeR (h : e ∈ GU) : e ∉ R := fun he => disjoint_left.mp hUR h he
    have hUeL (h : e ∈ GU) : e ∉ L := fun he => disjoint_left.mp hUL h he
    have hReL (h : e ∈ R) : e ∉ L := fun he => disjoint_left.mp hRL h he
    simp only [mem_union,mem_sdiff]
    tauto
  rw [← hEq]
  exact arcBalanced_sdiff hSub hBal hCovered

/-- An interior arc cannot change either of the two directed degrees
of an exterior vertex. -/
theorem cover_down_exterior_out_in_card [Fintype V] (U : Finset V)
    (GU R' : Finset (V × V)) (hGU : GU ⊆ U ×ˢ U)
    (hBal : ArcBalanced (GU ∪ R')) (v : V) (hv : v ∉ U) :
    (arcOutNeighbors R' v).card = (arcInNeighbors R' v).card := by
  have hEq : arcOutNeighbors (GU ∪ R') v = arcOutNeighbors R' v := by
    ext w
    simp only [mem_arcOutNeighbors,mem_union]
    exact or_iff_right (fun he => hv (mem_product.mp (hGU he)).1)
  have hEq' : arcInNeighbors (GU ∪ R') v = arcInNeighbors R' v := by
    ext w
    simp only [mem_arcInNeighbors,mem_union]
    exact or_iff_right (fun he => hv (mem_product.mp (hGU he)).2)
  have hZero : arcDivergence (GU ∪ R') v = 0 := by
    unfold arcDivergence
    exact sub_eq_zero.mpr (congrArg (fun n : ℕ => (n:ℤ)) (hBal v))
  rw [arcDivergence_eq_neighbor_counts,hEq,hEq',sub_eq_zero] at hZero
  exact_mod_cast hZero

/-- Combining (R2), (R4), (R5) and the leave-degree budget gives
the minimum degree on the remaining part of the modified neighborhood. -/
theorem cover_down_modified_protected_part
    (Z K : Finset V) (hK : K ⊆ Z) (R C J : Finset (V × V))
    (u : V) (sourceOutside : Prop) (A : V → Prop) {μ ρ n ζ ξ η : ℝ} (hη : 0 ≤ η)
    (hOldSize : μ*(ρ*n)/4 ≤ ((arcNeighborsIn Z R u).card : ℝ))
    (hOldDeg : (1/2+8*η)*((arcNeighborsIn Z R u).card : ℝ) ≤
      ((arcNeighborsIn Z R u).filter A).card)
    (hOldProt : ((arcNeighborsIn K R u).card : ℝ) ≤ 3*μ*(K.card : ℝ)+ξ*n)
    (hC : (incidentDegree C u : ℝ) ≤ ζ*n) (hJ : (incidentDegree J u : ℝ) ≤ ζ*n)
    (hSlack : 3*μ*(K.card : ℝ)+ξ*n+(3/2+η)*(ζ*n) ≤ 7*η*(μ*(ρ*n)/4)) :
    let Y' := arcNeighborsIn Z ((R \ C) ∪ J) u
    (1/2+η)*(Y'.card : ℝ) ≤ (Y'.filter (fun z => A z ∧ (sourceOutside ∨ z ∉ K))).card := by
  let Y := arcNeighborsIn Z R u
  let Y' := arcNeighborsIn Z ((R \ C) ∪ J) u
  have hEq : Y ∩ K = arcNeighborsIn K R u := by
    ext z
    simp only [Y,mem_arcNeighborsIn,mem_inter]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hK h.1,h.2⟩,h.1⟩⟩
  have hLost : ((Y \ Y').card : ℝ) ≤ incidentDegree C u := by
    exact_mod_cast (arcNeighborsIn_change Z R C J u).1
  have hGain : ((Y' \ Y).card : ℝ) ≤ incidentDegree J u := by
    exact_mod_cast (arcNeighborsIn_change Z R C J u).2
  apply cover_down_protected_degree Y Y' K sourceOutside A (B := 3*μ*(K.card : ℝ)+ξ*n) hη hOldDeg
    (by rw [hEq]; exact hOldProt) (hLost.trans hC) (hGain.trans hJ)
  exact hSlack.trans (mul_le_mul_of_nonneg_left hOldSize (by positivity))

end Neighborhoods
universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]

/-- Perform the exterior cover and obtain the balanced residual and
the three neighborhood estimates in (4.25) on the same reserve. -/
theorem exists_updated_exterior_reserve
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (U X : Finset (TripartiteVertex A B W)) (GU R L : TripartiteArcSet A B W)
    (hXU : Disjoint X U) (hGU : GU ⊆ U ×ˢ U)
    (hL : L ⊆ tripartiteArcs E P Q) (hR : R ⊆ tripartiteArcs E P Q)
    (hUR : Disjoint GU R) (hUL : Disjoint GU L) (hRL : Disjoint R L)
    (hBal : ArcBalanced (GU ∪ R ∪ L))
    {ζ μ ρ n : ℝ} (hNonneg : 0 ≤ ζ*n) (hSlack : 2*ζ*n < μ^2*ρ*n/20) (hLoad : ζ*n ≤ 10*μ*n)
    (hLDeg : ∀ v, (incidentDegree L v : ℝ) ≤ ζ*n)
    (hRDeg : ∀ v, (incidentDegree R v : ℝ) ≤ 10*μ*n)
    (hR3 : ∀ u ∈ X, ∀ v ∈ X, u ≠ v →
      let c : ℝ := ((arcNeighborsIn U R u) ∩ (arcNeighborsIn U R v)).card
      c ≤ 50*μ^2*ρ*n ∧ (tripartiteAdjacent E P Q u v → μ^2*ρ*n/20 ≤ c)) :
    let D := L ∩ (X ×ˢ X)
    ∃ label : (TripartiteVertex A B W × TripartiteVertex A B W) → TripartiteVertex A B W,
      let C := usedExteriorReserve D label
      let R' := (R \ C) ∪ (L \ D)
      (∀ e ∈ D, label e ∈ U) ∧ C ⊆ R ∧
      (∀ e ∈ D, ∀ f ∈ D, e ≠ f →
        Disjoint (exteriorTriangle e (label e)) (exteriorTriangle f (label f))) ∧
      (∀ v ∈ X, (incidentDegree C v : ℝ) ≤ ζ*n) ∧
      ArcBalanced (GU ∪ R') ∧
      (∀ v ∈ X, (arcOutNeighbors R' v).card = (arcInNeighbors R' v).card) ∧
      (∀ v ∈ X, (((arcNeighborsIn U R v) ∆ (arcNeighborsIn U R' v)).card : ℝ) ≤ 2*ζ*n) ∧
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v →
        (((arcNeighborsIn U R' u) ∩ (arcNeighborsIn U R' v)).card : ℝ) ≤ 100*μ^2*ρ*n) ∧
      ∀ v, ((arcNeighborsIn X R' v).card : ℝ) ≤ 20*μ*n := by
  intro D
  have hLower u hu v hv hne he := (hR3 u hu v hv hne).2 he
  have hLower' (u) (hu : u ∈ X) (v) (hv : v ∈ X) (hne : u ≠ v)
      (he : tripartiteAdjacent E P Q u v) :
      μ^2*ρ*n/20 ≤ ((U.filter (fun z =>
        ((u,z) ∈ R ∨ (z,u) ∈ R) ∧ ((v,z) ∈ R ∨ (z,v) ∈ R))).card : ℝ) := by
    have hEq : arcNeighborsIn U R u ∩ arcNeighborsIn U R v =
        U.filter (fun z => ((u,z) ∈ R ∨ (z,u) ∈ R) ∧ ((v,z) ∈ R ∨ (z,v) ∈ R)) := by
      ext z
      simp only [mem_inter,mem_arcNeighborsIn,mem_filter]
      tauto
    rw [← hEq]
    exact hLower u hu v hv hne he
  obtain ⟨label,hLabel,hUsed,hDisj,hUseDeg,hCovered⟩ :=
    exists_reserve_cover_of_outer_leave U X L R hXU hL hR hRL.symm hSlack hLDeg hLower'
  let C := usedExteriorReserve D label
  let J := L \ D
  let R' := (R \ C) ∪ J
  have hOutside (v) (hv : v ∈ X) : v ∉ U := fun h => disjoint_left.mp hXU hv h
  have hC (v) (hv : v ∈ X) : (incidentDegree C v : ℝ) ≤ ζ*n := by
    have h := hUseDeg v (hOutside v hv)
    exact (show (incidentDegree C v : ℝ) ≤ incidentDegree L v by exact_mod_cast h).trans (hLDeg v)
  have hJ (v) : (incidentDegree J v : ℝ) ≤ ζ*n := by
    have h := incidentDegree_mono (show J ⊆ L from sdiff_subset) v
    exact (show (incidentDegree J v : ℝ) ≤ incidentDegree L v by exact_mod_cast h).trans (hLDeg v)
  have hBal' : ArcBalanced (GU ∪ R') := by
    have h := cover_down_balance_after_exterior GU R L D C inter_subset_left hUsed hUR hUL hRL
      (by convert hBal using 1; ext e; simp only [mem_union])
      (by convert hCovered using 1; ext e; simp only [C,D,mem_union])
    convert h using 1
    ext e
    simp only [R',J,mem_union,mem_sdiff]
  have hPair : 2*ζ*n ≤ 50*μ^2*ρ*n := by linarith only [hSlack,hNonneg]
  obtain ⟨hSymm,hInter,hMany⟩ := cover_down_modified_neighborhood_bounds U X R C J hC hJ hRDeg
    (by
      intro u hu v hv hne
      have h := (hR3 u hu v hv hne).1
      convert h using 1
      congr 2
      ext z
      simp only [mem_inter]) hPair hLoad
  refine ⟨label,hLabel,hUsed,hDisj,hC,hBal',?_,?_,?_,?_⟩
  · intro v hv
    have h := cover_down_exterior_out_in_card U GU R' hGU
      (by convert hBal' using 1; ext e; simp only [mem_union]) v (hOutside v hv)
    convert h using 1 <;> congr 4 <;>
      first | apply Subsingleton.elim | (ext e; simp only [R',J,mem_union,mem_sdiff])
  · intro v hv
    have h := hSymm v hv
    convert h using 1
    congr 2
    ext z
    simp only [C,J,Finset.symmDiff_def,mem_inter,mem_arcNeighborsIn,mem_union,mem_sdiff]
  · intro u hu v hv hne
    have h := hInter u hu v hv hne
    convert h using 1
    congr 2
    ext z
    simp only [C,J,Finset.symmDiff_def,mem_inter,mem_arcNeighborsIn,mem_union,mem_sdiff]
  · intro v
    have h := hMany v
    convert h using 1
    congr 2
    ext z
    simp only [C,J,Finset.symmDiff_def,mem_inter,mem_arcNeighborsIn,mem_union,mem_sdiff]

end OverfullWork.ChenShan
