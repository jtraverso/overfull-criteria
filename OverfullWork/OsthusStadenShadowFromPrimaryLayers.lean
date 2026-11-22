module

public import OverfullWork.OsthusStadenPrimaryBridgeCells
public import OverfullWork.OsthusStadenShadowFibres

@[expose] public section


/-! Claim 5.5 on the red labels of the actual unwound primary factors. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient
open scoped Classical

/-- Over a primary cluster, exactly its selected p-cells appear in the
corresponding fibre of the red labels. -/
theorem PrimaryRedSelection.allPCells_fibre
    {I : Type*} [Fintype I] {r s p : ℕ} [NeZero (2*s)]
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (q : Bool) (j : RefinedFactorIndex r (2*s) p) (i : I) :
    (D.allPCells q j).filter (fun x => x.1.1 = i) = D.pCells q j i := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx,hi⟩ := mem_filter.mp hx
    obtain ⟨u,z,hz,he⟩ := (D.mem_allPCells_iff q j x).mp hx
    have hu : u = i := (congrArg (fun a : RefinedVertex I (2*s) p => a.1.1) he).symm.trans hi
    subst u
    exact mem_map.mpr ⟨z,hz,he.symm⟩
  · intro hx
    obtain ⟨z,hz,he⟩ := mem_map.mp hx
    exact mem_filter.mpr ⟨(D.mem_allPCells_iff q j x).mpr ⟨i,z,hz,he.symm⟩,
      congrArg (fun a : RefinedVertex I (2*s) p => a.1.1) he.symm⟩

/-- The projected shadow graph is robust and its semidegrees are the
projected reduced semidegrees multiplied by the uniform red fibre size.
The disjointness and separation also give an injective shadow source map. -/
theorem shadow_graph_of_unwound_primary_layer
    {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
    {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
    {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ ε d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    {A : UnwoundPrimarySlices G thin E g σ τ ε d R}
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 1 < p) (hs : 2 ≤ s)
    (j : RefinedFactorIndex r (2*s) p) (Q : Digraph I) (ν t₀ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ t₀) (hτ : t₀ ≤ 1/4) (hOrder : 2 ≤ t₀*(Fintype.card I:ℝ))
    (hQ : IsRealRobust Q ν t₀) :
    let incoming := D.allPCells true j
    let outgoing := D.allPCells false j
    let send := shadowSend (A.factor j) incoming outgoing
    let receive := shadowReceive (A.factor j) incoming outgoing
    let project := fun x : RefinedVertex I (2*s) p => x.1.1
    let shadow := fibrePullback Q (project ∘ send) (project ∘ receive)
    Disjoint incoming outgoing ∧
    (∀ u ∈ outgoing, A.factor j u ∉ incoming) ∧ Function.Injective send ∧
    IsRealRobust shadow (ν^2/2) (2*t₀) ∧
      ∀ x, inDegree shadow x = inDegree Q (project (receive x))*(2*(s-1)) ∧
        outDegree shadow x = outDegree Q (project (send x))*(2*(s-1)) := by
  intro incoming outgoing send receive project shadow
  have hProj (x : RefinedVertex I (2*s) p) : project (A.factor j x) = σ j.1 (project x) := by
    rcases j with ⟨t,a,b⟩
    exact (congrArg Prod.fst (A.factor_proj t a b x)).trans (A.first_proj t a x.1)
  have hDis : Disjoint incoming outgoing := by
    apply disjoint_left.mpr
    intro x hx hy
    exact D.pCell_unique_direction j x ⟨(D.mem_allPCells_iff true j x).mp hx,(D.mem_allPCells_iff false j x).mp hy⟩
  have hSep (u : RefinedVertex I (2*s) p) (hu : u ∈ outgoing) : A.factor j u ∉ incoming := by
    intro hv
    have h := D.distance hp ((D.mem_allPCells_iff false j _).mp hu)
      ((D.mem_allPCells_iff true j _).mp hv) (k := 1) (by decide) (by rw [pow_one])
    omega
  have hFibres (q : Bool) (i : I) : ((D.allPCells q j).filter (fun x => project x = i)).card = s-1 := by
    exact (congrArg Finset.card (D.allPCells_fibre q j i)).trans (D.pCells_card q j i)
  exact ⟨hDis,hSep,shadowSend_injective _ _ _ hSep,
    shadow_realRobust_and_degrees Q (A.factor j) (σ j.1) project incoming outgoing (s-1)
      hProj hDis (hFibres true) (hFibres false) (by omega) ν t₀ hν hντ hτ hOrder hQ⟩

end OverfullWork.DirectedRobustExpansion
