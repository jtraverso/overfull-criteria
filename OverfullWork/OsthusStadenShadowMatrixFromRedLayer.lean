module

public import OverfullWork.OsthusStadenPhysicalRedDemands

@[expose] public section


/-! Build the capacity-limited shadow matrix of §5.8 from the actual red demands. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

set_option maxHeartbeats 1300000 in
/-- The shadow balancing sequence uses the red arcs already installed
on the layer. Its row and column equations refer to the same physical
exceptional set and the same p-cells. -/
theorem exists_shadow_balancing_matrix_from_physical_red_layer
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ ε d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ ε d R}
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 1 < p) (hs : 2 ≤ s)
    (j : RefinedFactorIndex r (2*s) p) (Q : Digraph I) (F : Digraph V)
    (erase : RefinedVertex I (2*s) p → V) (hErase : ∀ u, erase u ∈ primaryPCells (R j.1) u)
    (κ b c : ℕ) (ν t₀ α err cap : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ t₀) (hτ : t₀ ≤ 1/4) (hOrder : 2 ≤ t₀*(Fintype.card I:ℝ))
    (hQ : IsRealRobust Q ν t₀)
    (hQin : ∀ i, α*(Fintype.card I:ℝ) ≤ (inDegree Q i:ℝ))
    (hQout : ∀ i, α*(Fintype.card I:ℝ) ≤ (outDegree Q i:ℝ))
    (hAlpha : 8*t₀ ≤ α) (hErr : 0 ≤ err) (hErrSmall : 16*err ≤ ν^2/2)
    (hDemand : ((2*m-1:ℕ):ℝ)*cap ≤ err*(c:ℝ)) :
    let cell := fun u => (primaryPCells (R j.1) u).erase (erase u)
    let ordinary := univ.biUnion cell
    let demand := fun q u => cellExceptionalArcCount F ordinary (cell u) q
    let incoming := D.allPCells true j
    let outgoing := D.allPCells false j
    let T := ↥(@Union.union _ (@Finset.instUnion _ (Classical.decEq _)) incoming outgoing)
    let project := fun x : RefinedVertex I (2*s) p => x.1.1
    let send := shadowSend (A.factor j) incoming outgoing
    let receive := shadowReceive (A.factor j) incoming outgoing
    let shadow := fibrePullback Q (project ∘ send) (project ∘ receive)
    (∀ x y, x ∉ ordinary → y ∉ ordinary → ¬ F.Adj x y) →
    (∀ x, x ∉ ordinary → inDegree F x = κ ∧ outDegree F x = κ) →
    (∀ q, ordinaryRedEndpoints F ordinary q ⊆ D.vertices q j) →
    (∀ x ∈ ordinary, ∀ q : Bool, profileCount ordinaryᶜ (if q then outProfile F x else inProfile F x) ≤ cap) →
    8 ≤ α*(Fintype.card T:ℝ) →
    3*((c:ℝ)/(Fintype.card T:ℝ)) ≤ (b:ℝ)*(ν^2/2)^2 →
    ∃ M : T → T → ℕ,
      (∀ v w, M v w ≤ if shadow.Adj v w then b else 0) ∧
      (∀ v, (∑ w,M v w) = c+demand false v) ∧
      (∀ w, (∑ v,M v w) = c+demand true w) := by
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  intro cell ordinary demand incoming outgoing T project send receive shadow hInd hExact hRed hCap hTorder hCapacity
  obtain ⟨hDis,_,_,hShadow,hDeg⟩ := shadow_graph_of_unwound_primary_layer D hp hs j Q ν t₀ hν hντ hτ hOrder hQ
  obtain ⟨_,hLocal,hEqual⟩ := physical_red_demands_on_unwound_layer D j F κ cap erase hErase hInd hExact hRed
    (fun x hx q => by
      cases q
      · simpa only [Bool.false_eq_true,if_false] using hCap x hx false
      · simpa only [if_true] using hCap x hx true)
  have hCards (q : Bool) : (D.allPCells q j).card = Fintype.card I*(s-1) := by
    rw [card_eq_sum_card_fiberwise (f := project) (t := (univ : Finset I)) (fun _ _ => mem_univ _)]
    simp [project,D.allPCells_fibre,D.pCells_card]
  have hT : Fintype.card T = Fintype.card I*(2*(s-1)) := by
    rw [Fintype.card_coe,card_union_of_disjoint hDis,hCards true,hCards false]
    rw [two_mul,Nat.mul_add]
  have hTReal : (Fintype.card T:ℝ) = (Fintype.card I:ℝ)*(2*((s-1:ℕ):ℝ)) := by exact_mod_cast hT
  have hIn (x : T) : α*(Fintype.card T:ℝ) ≤ (inDegree shadow x:ℝ) := by
    have h := congrArg (fun k : ℕ => (k:ℝ)) (hDeg x).1
    change (inDegree shadow x:ℝ) = _ at h
    rw [h,hTReal]
    push_cast
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hQin (project (receive x))) (by positivity)
  have hOut (x : T) : α*(Fintype.card T:ℝ) ≤ (outDegree shadow x:ℝ) := by
    have h := congrArg (fun k : ℕ => (k:ℝ)) (hDeg x).2
    change (outDegree shadow x:ℝ) = _ at h
    rw [h,hTReal]
    push_cast
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hQout (project (send x))) (by positivity)
  have hνOne : ν ≤ 1 := by linarith only [hντ,hτ]
  have hSquare : ν^2 ≤ ν := by simpa [pow_two] using mul_le_of_le_one_right hν.le hνOne
  exact exists_shadow_balancing_matrix shadow b c (ν^2/2) (2*t₀) α err
    (fun v => demand false v) (fun v => demand true v) (by positivity)
    (by linarith only [hSquare,hνOne]) (by linarith only [hSquare,hντ,hν])
    (by linarith only [hAlpha]) hErr hErrSmall hTorder hCapacity hShadow hIn hOut
    (fun v => (hLocal false v).trans hDemand) (fun v => (hLocal true v).trans hDemand)
    ((hEqual false).trans (hEqual true).symm)

end OverfullWork.DirectedRobustExpansion
