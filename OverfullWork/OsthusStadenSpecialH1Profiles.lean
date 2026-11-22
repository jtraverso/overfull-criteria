module

public import OverfullWork.OsthusStadenCoreExceptionOnLayers
public import OverfullWork.OsthusStadenSlicesFromPrimaryFactors

@[expose] public section


/-! H1' on the physical red targets clipped by the one-vertex trim. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

/-- The target of a special exceptional request uses the base phase
as well as the corresponding adapted red half. -/
noncomputable def specialRedTargets
    {V I J : Type*} [Fintype V] [Fintype I] {r s p m₀ m : ℕ} [NeZero (2*s)] [NeZero p]
    {profiles : J → Finset V} {f : V → Option I} {g : Fin r → V → Option I} {ε τ : ℝ}
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (base : ∀ i, PrimaryNestedRefinement profiles (cluster f i) (2*s) p m₀ ε ε ε)
    (adapted : ∀ t i, PrimaryNestedRefinement profiles (cluster (g t) i) (2*s) p m τ τ τ)
    (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
    (dir : Bool) (j : RefinedFactorIndex r (2*s) p) : Finset V :=
  univ.biUnion (fun i => (D.select dir j i).biUnion (fun z =>
    primaryHalfOfIndex base (i,z,redPhase p j.1.val) ∩
      (primaryHalfOfIndex (adapted j.1) (i,z,redPhase p j.1.val)).erase (erase j (redPLabel j.1.val i z))))

/-- The two density coefficients in the H1' sum with s−1 halves on
one side of the intermediate partition into 2s cells. -/
theorem special_red_fraction_budget (s p : ℕ) (e : ℝ)
    (hs : 4 ≤ s) (hp : 0 < p) (he : 0 ≤ e) (heSmall : e ≤ 1/9) :
    1/(6*(p:ℝ)) ≤ ((s-1:ℕ):ℝ)*(1-e)/((((2*s)*p*2:ℕ):ℝ)) ∧
      ((s-1:ℕ):ℝ)*(1+e)/((((2*s)*p*2:ℕ):ℝ)) ≤ 1/(3*(p:ℝ)) := by
  have hsR : 4 ≤ (s:ℝ) := by exact_mod_cast hs
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  have hℓ : (0:ℝ) < ((2*s)*p*2:ℕ) := by
    have : 0 < (2*s)*p*2 := Nat.mul_pos (Nat.mul_pos (by omega) hp) (by decide)
    exact_mod_cast this
  have hsLe : (3/4:ℝ)*(s:ℝ) ≤ ((s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one]
    linarith only [hsR]
  have hLo := mul_le_mul hsLe (show (8/9:ℝ) ≤ 1-e by linarith only [heSmall])
    (by norm_num) (Nat.cast_nonneg _)
  have hHi := mul_le_mul (show (((s-1:ℕ):ℝ)) ≤ (s:ℝ) by exact_mod_cast Nat.sub_le s 1)
    (show 1+e ≤ (4/3:ℝ) by linarith only [heSmall]) (by positivity) (Nat.cast_nonneg _)
  constructor
  · apply (le_div_iff₀ hℓ).mpr
    have heq : (1/(6*(p:ℝ)))*((((2*s)*p*2:ℕ):ℝ)) = (3/4*(s:ℝ))*(8/9) := by
      push_cast
      field_simp
      <;> ring
    exact heq.trans_le hLo
  · apply (div_le_iff₀ hℓ).mpr
    have heq : (1/(3*(p:ℝ)))*((((2*s)*p*2:ℕ):ℝ)) = (s:ℝ)*(4/3) := by
      push_cast
      field_simp
      <;> ring
    exact hHi.trans_eq heq.symm

set_option maxHeartbeats 1250000 in
/-- H1' follows from H1 on the physical reserve, the common base
refinement, and the loss of at most one further vertex per half. -/
theorem h1_profile_on_special_red_targets
    {V I : Type*} [Fintype V] [Fintype I] {r s p m₀ b mBase m : ℕ}
    [NeZero (2*s)] [NeZero p]
    {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
    (E : Fin r → I → Digraph V) (g : Fin r → V → Option I)
    (ε τ : ℝ)
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster B.partition i) (2*s) p mBase ε ε ε)
    (adapted : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster (g t) i) (2*s) p m τ τ τ)
    {F : Fin r → UnwindingLabel (2*s) → Equiv.Perm (I × ZMod (2*s))}
    {C : ∀ t a, FactorCycleCoordinates (F t a)} (D : PrimaryRedSelection (p := p) C)
    (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
    (hs : 4 ≤ s) (hp : 0 < p) (hε : 0 ≤ ε) (hεSmall : 8*ε ≤ 1/9)
    (loss : ℕ) (hLoss : ∀ t (i : PrimaryHalfIndex I (2*s) p),
      ((primaryHalfOfIndex base i) \ primaryHalfOfIndex (adapted t) i).card ≤ loss)
    (q : Fin 5) (dir : Bool) (j : RefinedFactorIndex r (2*s) p) (x : V)
    (hx : B.partition x ≠ none) :
    let H := primaryThinDigraphs B q
    let Q := if dir then outProfile H x else inProfile H x
    let A := specialRedTargets D base adapted erase dir j
    let total := γ*a*(Fintype.card V:ℝ)
    let k := ((2*s)*p*2:ℕ)
    let e := 8*ε
    (Fintype.card I:ℝ)*((s-1:ℕ):ℝ)*((1-e)*(e*(B.size:ℝ)/(k:ℝ))+((loss+1:ℕ):ℝ)) ≤ total/(180*(p:ℝ)) →
    (Fintype.card I:ℝ)*((s-1:ℕ):ℝ)*e*(B.size:ℝ) ≤ total/(3*(p:ℝ)) →
    total/(20*(p:ℝ)) ≤ profileCount A Q ∧ profileCount A Q ≤ total/(p:ℝ) := by
  intro H₁ Q A total k e hLoErr hHiErr
  let index (i : I) (z : Fin (2*s)) : PrimaryHalfIndex I (2*s) p := (i,z,redPhase p j.1.val)
  let before (i : I) (z : Fin (2*s)) := primaryHalfOfIndex base (index i z)
  let after (i : I) (z : Fin (2*s)) := (primaryHalfOfIndex (adapted j.1) (index i z)).erase
    (erase j (redPLabel j.1.val i z))
  have hReserve := reserve_profile_on_retained_cells
    (fun i => (B.kept i).trans (B.base i))
    (fun z : ReducedCopy M => z.1.1) (fun z : ReducedCopy M => z.1.2) (B.thin q) dir x
  have hBaseCard (i : I) : (cluster B.partition i).card = B.size := by
    rw [←B.retained_cells i,card_map,card_univ,Fintype.card_fin]
  have hQ : Q ⊆ univ.biUnion (cluster B.partition) := by
    have hSup : Q ⊆ univ.biUnion (fun i => univ.map ((B.kept i).trans (B.base i))) := hReserve.1
    rwa [show (fun i => univ.map ((B.kept i).trans (B.base i))) = cluster B.partition from
      funext B.retained_cells] at hSup
  have hDx : total/3 ≤ (Q.card:ℝ) ∧ (Q.card:ℝ) ≤ 2*total := by
    cases hTag : B.partition x with
    | none => exact (hx hTag).elim
    | some i =>
      have hx' := (mem_cluster B.partition i x).mpr hTag
      rw [←B.retained_cells i] at hx'
      obtain ⟨w,_,rfl⟩ := mem_map.mp hx'
      have hc : Q.card = pairSemidegree dir H₁ ((B.kept i).trans (B.base i) w) := hReserve.2
      rw [hc]
      have h := B.h1 q dir i w
      refine ⟨h.1,?_⟩
      simpa only [H₁,primaryThinDigraphs,total,←mul_assoc] using h.2
  have hRef (i : I) (z : Fin (2*s)) :
      UniformProfileCell (fun _ : Unit => Q) (cluster B.partition i) (before i z) k e := by
    let w := (ZMod.finEquiv p).symm (redPhase p j.1.val).1
    let b : Fin 2 := if (redPhase p j.1.val).2 then 1 else 0
    have hh := ((base i).uniform_p_and_half_cells hε (by linarith only [hεSmall]) z w).2 b
    have he : before i z = (((base i).halves z w).cells b) := by
      dsimp only [before,index,primaryHalfOfIndex,primaryHalfCell,w,b]
      rw [(ZMod.finEquiv (2*s)).symm_apply_apply]
    rw [he]
    intro _
    cases dir
    · exact (hh.inProfile (Sum.inl (some q))) x
    · exact (hh.outProfile (Sum.inl (some q))) x
  exact h1_red_profile_of_aligned_halves (cluster B.partition) before after (D.select dir j) Q
    B.size k (s-1) p e ((loss+1:ℕ):ℝ) total hp (by dsimp only [e]; positivity)
    (by dsimp only [e]; linarith only [hεSmall]) (by positivity) hBaseCard
    (fun _ _ h => clusters_disjoint B.partition h) (D.size dir j)
    (fun i z _ => (primaryHalfCell_subset base (redPLabel j.1.val i z) _).trans
      ((((base i).second _).subset _).trans ((base i).first.subset _)))
    (fun i z w h => primaryHalfOfIndex_disjoint base
      (fun he => h (congrArg (fun t : PrimaryHalfIndex I (2*s) p => t.2.1) he)))
    (fun i z _ => by exact_mod_cast half_loss_after_erase _ _ _ loss (hLoss j.1 (index i z)))
    (fun i z _ => hRef i z) hQ hDx
    (special_red_fraction_budget s p e hs hp (by dsimp only [e]; positivity) hεSmall).1
    (special_red_fraction_budget s p e hs hp (by dsimp only [e]; positivity) hεSmall).2 hLoErr hHiErr

end OverfullWork.DirectedRobustExpansion
