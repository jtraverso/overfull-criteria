module

public import OverfullWork.OsthusStadenSpecialExceptionOccurrences
public import OverfullWork.OsthusStadenSpecialH1Profiles

@[expose] public section


/-! The two disjoint H1 reserves supply exact special exceptional degrees. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

set_option maxHeartbeats 1800000 in
/-- Claim 5.4 and the subsequent exact trimming on the physical red cells.
The original-type occurrence and the local budgets are explicit hypotheses. -/
theorem exists_special_exception_arcs_on_trimmed_layers
    (r s p capTypes : ℕ) [NeZero (2*s)] [NeZero p]
    (hs : 4 ≤ s) (hp : 0 < p) (split : ℝ) (hSplit : 0 < split) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {m₀ b mBase m : ℕ} {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {β γ η a exc : ℝ} (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
      {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {ε τ δ d : ℝ}
      (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster B.partition i) (2*s) p mBase ε ε ε)
      (R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster (g t) i) (2*s) p m τ τ τ)
      (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ δ d R)
      (D : PrimaryRedSelection (p := p) A.coordinates)
      (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
      (bridges : RefinedFactorIndex r (2*s) p → Finset V)
      (hFresh : Function.Injective (fun q : RefinedFactorIndex r (2*s) p × RefinedVertex I (2*s) p => erase q.1 q.2))
      (hTypes : ∀ x, B.partition x ≠ none → ((univ : Finset (Fin r)).filter (fun t => g t x = none)).card ≤ capTypes)
      (pos neg : Fin 5) (hne : pos ≠ neg) (κ loss : ℕ) (cap : ℝ),
      N ≤ Fintype.card V → 0 ≤ ε → 8*ε ≤ 1/9 →
      (∀ t (i : PrimaryHalfIndex I (2*s) p),
        ((primaryHalfOfIndex base i) \ primaryHalfOfIndex (R t) i).card ≤ loss) →
      let Z := specialExceptions (exceptional B.partition) (fun j => primaryPCells (R j.1)) erase bridges
      let red := specialRedTargets D base R erase
      let total := γ*a*(Fintype.card V:ℝ)
      let ell := ((2*s)*p*2:ℕ)
      let e := 8*ε
      let k := capTypes*((2*s-1)*(p-1))+1
      (Fintype.card I:ℝ)*((s-1:ℕ):ℝ)*((1-e)*(e*(B.size:ℝ)/(ell:ℝ))+((loss+1:ℕ):ℝ)) ≤ total/(180*(p:ℝ)) →
      (Fintype.card I:ℝ)*((s-1:ℕ):ℝ)*e*(B.size:ℝ) ≤ total/(3*(p:ℝ)) →
      (κ:ℝ)+split*(Fintype.card V:ℝ) ≤ (total/(20*(p:ℝ)))/(k:ℝ) →
      (∀ j, ((Z j).card:ℝ)/(k:ℝ)+split*(Fintype.card V:ℝ) ≤ cap) →
      ∃ F : RefinedFactorIndex r (2*s) p → Digraph V,
        (∀ j, F j ≤ primaryThinDigraphs B pos ⊔ primaryThinDigraphs B neg) ∧
        (∀ j j', j ≠ j' → Disjoint (F j) (F j')) ∧
        (∀ j x y, (F j).Adj x y →
          (x ∈ Z j ∧ y ∉ Z j ∧ y ∈ red true j) ∨ (y ∈ Z j ∧ x ∉ Z j ∧ x ∈ red false j)) ∧
        (∀ j x, x ∈ Z j → inDegree (F j) x = κ ∧ outDegree (F j) x = κ) ∧
        ∀ j x, x ∉ Z j → (inDegree (F j) x:ℝ) ≤ cap ∧ (outDegree (F j) x:ℝ) ≤ cap := by
  let k := capTypes*((2*s-1)*(p-1))+1
  obtain ⟨N,hN⟩ := exists_special_exception_arc_split.{u,0} (RefinedFactorIndex r (2*s) p)
    split hSplit k (by dsimp only [k]; omega)
  refine ⟨N,?_⟩
  intro V _ I _ m₀ b mBase m G H f M β γ η a exc B E g σ ε τ δ d base R A D erase bridges hFresh
    hTypes pos neg hne κ loss cap hSize hε hSmall hLoss Z red total ell e k' hLo hHi hDemand hRoom
  let reserve (q : Bool) := primaryThinDigraphs B (if q then pos else neg)
  have hCore (j : RefinedFactorIndex r (2*s) p) (x : V) (hx : x ∈ Z j) : B.partition x ≠ none :=
    fun h => (mem_sdiff.mp hx).2 (mem_union_left _ ((mem_exceptional B.partition x).mpr h))
  have hOcc := special_exception_occurrences_on_trimmed_layers A (exceptional B.partition) erase bridges
    hFresh capTypes (fun x hx => hTypes x (fun h => hx ((mem_exceptional B.partition x).mpr h)))
  have hRed (q : Bool) (j : RefinedFactorIndex r (2*s) p) (x : V) (hx : x ∈ red q j) : x ∉ Z j := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    obtain ⟨z,_,hz⟩ := mem_biUnion.mp hi
    obtain ⟨hne',hh⟩ := mem_erase.mp (mem_inter.mp hz).2
    have hc := primaryHalfCell_subset (R j.1) (redPLabel j.1.val i z) (redPhase p j.1.val).2 hh
    intro h
    exact (mem_compl.mp (mem_sdiff.mp h).1)
      (mem_biUnion.mpr ⟨redPLabel j.1.val i z,mem_univ _,mem_erase.mpr ⟨hne',hc⟩⟩)
  have hProf (q : Bool) (j : RefinedFactorIndex r (2*s) p) (x : V) (hx : x ∈ Z j) :
      (κ:ℝ)+split*(Fintype.card V:ℝ) ≤
        profileCount (red q j) (if q then outProfile (reserve q) x else inProfile (reserve q) x)/(k:ℝ) := by
    have h := (h1_profile_on_special_red_targets B E g ε τ base R D erase hs hp hε hSmall
      loss hLoss (if q then pos else neg) q j x (hCore j x hx) hLo hHi).1
    exact hDemand.trans (div_le_div_of_nonneg_right h (Nat.cast_nonneg k))
  choose Q hSupport hDis hDegree hCap using fun q =>
    hN (reserve q) q Z (red q) κ cap hSize hOcc (hProf q) hRoom
  let supply (q : Bool) (j : RefinedFactorIndex r (2*s) p) := if q then Q q j else reverseArcs (Q q j)
  refine exists_exact_layer_exception_arcs (reserve true ⊔ reserve false) Z
    (fun q j x => x ∈ red q j) supply κ cap ?_ ?_ ?_ ?_ ?_
  · intro q j x y h
    cases q
    · have hh : (Q false j).Adj y x := h
      obtain ⟨hArc,hx,hy⟩ := hSupport false j y x hh
      exact ⟨hx,hRed false j y hy,hy,Or.inr hArc⟩
    · have hh : (Q true j).Adj x y := h
      obtain ⟨hArc,hx,hy⟩ := hSupport true j x y hh
      exact ⟨hx,hRed true j y hy,hy,Or.inl hArc⟩
  · intro q j x hx
    have h := hDegree q j x hx
    cases q
    · change (κ:ℝ) ≤ (outDegree (supply false j) x:ℝ) at h
      exact_mod_cast h
    · change (κ:ℝ) ≤ (outDegree (supply true j) x:ℝ) at h
      exact_mod_cast h
  · intro q j x
    cases q
    · exact hCap false j x
    · exact hCap true j x
  · intro q j k hne'
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hx,hy⟩
    cases q
    · exact (show (⊥ : Digraph V).Adj y x from disjoint_iff_inf_le.mp (hDis false j k hne') ⟨hx,hy⟩).elim
    · exact disjoint_iff_inf_le.mp (hDis true j k hne') ⟨hx,hy⟩
  · intro j k x y hx hy
    exact disjoint_iff_inf_le.mp (B.thin_disjoint pos neg hne)
      ⟨(hSupport true j x y hx).1,(hSupport false k x y hy).1⟩

end OverfullWork.DirectedRobustExpansion
