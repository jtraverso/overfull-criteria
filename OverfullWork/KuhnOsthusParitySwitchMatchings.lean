module

public import OverfullWork.KuhnOsthusCycleAbsorberRepairPair
public import OverfullWork.KuhnOsthusCycleAbsorberMarkOrder

@[expose] public section


/-! Extend each of the prescribed two-arc matchings in Lemma 10.5.
The three matchings of a triple switch use the six arcs of a K₂,₃. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*}

structure PrescribedSwitchMatching (D : Digraph V) (A B : Finset V) where
  source : Bool ↪ A
  target : Bool ↪ B
  edge : ∀ l, D.Adj (source l) (target l)

structure ParityTripleSwitch (D : Digraph V) (A B : Finset V) where
  source : Bool ↪ A
  target : Fin 3 ↪ B
  edge : ∀ l j, D.Adj (source l) (target j)

def ParityTripleSwitch.matching {D : Digraph V} {A B : Finset V}
    (K : ParityTripleSwitch D A B) (i : Fin 3) : PrescribedSwitchMatching D A B where
  source := K.source
  target := ⟨fun l => K.target (if l then finRotate 3 i else i),by
    intro l l' h
    have hDiff := finRotate_interval_ne_self (by decide : 2 ≤ 3) i
    have h' := K.target.injective h
    cases l <;> cases l'
    · rfl
    · exact (hDiff h'.symm).elim
    · exact (hDiff h').elim
    · rfl⟩
  edge := fun l => K.edge l _

theorem ParityTripleSwitch.matching_target_next {D : Digraph V} {A B : Finset V}
    (K : ParityTripleSwitch D A B) (i : Fin 3) :
    (K.matching i).target true = (K.matching (finRotate 3 i)).target false := rfl

variable [Fintype V]

/-- Find and label all six physical arcs of the triple switch. -/
theorem IsLowerSuperregularPair.exists_parity_triple_switch {D : Digraph V} {A B : Finset V}
    {m r : ℕ} {ε d : ℝ} (hPair : IsLowerSuperregularPair D ε d A B)
    (hA : A.card = 2*m) (hB : B.card = 2*m) (hm : 0 < m) (hε : 0 ≤ ε)
    (hGap : 2*ε < d) (hd : d ≤ 1)
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    Nonempty (ParityTripleSwitch D A B) := by
  have hLarge : 2 ≤ A.card := by omega
  have hLeft : (A.card:ℝ)*ε ≤ ((A.card-1:ℕ):ℝ) := by
    have he := mul_le_mul_of_nonneg_left (show ε ≤ (1:ℝ)/2 by linarith) (Nat.cast_nonneg A.card)
    have hTwo : (2:ℝ) ≤ A.card := by exact_mod_cast hLarge
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    linarith
  have hRight : (B.card:ℝ)*ε ≤ (d-ε)*(B.card:ℝ) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hPow : (d-2*ε)^14 ≤ d-2*ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by linarith : 0 ≤ d-2*ε)
      (by linarith : d-2*ε ≤ 1) (by decide : 1 ≤ 14)
  have hScale := mul_le_mul_of_nonneg_right hPow
    (mul_nonneg (by linarith : 0 ≤ d-ε) (Nat.cast_nonneg (α := ℝ) (2*m)))
  have hSwitch : (3:ℝ) ≤ (d-2*ε)*((d-ε)*(B.card:ℝ)) := by
    rw [hB]
    linarith only [hBudget,hScale,Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨x,hx,y,hy,hxy,T,hT,hCard,hEdges⟩ :=
    hPair.exists_common_switch_targets D A B d ε 3 hGap hLarge hLeft hRight hSwitch
  let s : Bool ↪ A := ⟨fun l => if l then ⟨y,hy⟩ else ⟨x,hx⟩,by
    intro l l' he
    cases l <;> cases l' <;> try rfl
    · exact (hxy (congrArg Subtype.val he)).elim
    · exact (hxy (congrArg Subtype.val he).symm).elim⟩
  let t₀ : Fin 3 ≃ T := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hCard)).symm
  let t : Fin 3 ↪ B := ⟨fun j => ⟨t₀ j,hT (t₀ j).prop⟩,fun j k h =>
    t₀.injective (Subtype.ext (congrArg (fun a : B => a.val) h))⟩
  refine ⟨⟨s,t,?_⟩⟩
  intro l j
  cases l
  · exact (hEdges _ (t₀ j).prop).1
  · exact (hEdges _ (t₀ j).prop).2

/-- Extend a prescribed pair of arcs to a matching of the whole
successor pair, with the two prescribed arcs at the same marked
copy in the two return lanes. -/
theorem PrescribedSwitchMatching.exists_ordered_pair {D : Digraph V} {A : ℕ → Finset V}
    {m r i : ℕ} {ε d : ℝ} (P : PrescribedSwitchMatching D (A i) (A (i+1))) (j₀ : Fin m)
    (hPair : IsLowerSuperregularPair D ε d (A i) (A (i+1)))
    (hA : (A i).card = 2*m) (hB : (A (i+1)).card = 2*m)
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ M : OrderedClusterPaths D A (Fin m × Fin 2) i (i+1), ∀ l,
      M.vertex i (j₀,cycleAbsorberLane l) = (P.source l).val ∧
      M.vertex (i+1) (j₀,cycleAbsorberLane l) = (P.target l).val := by
  let s := P.source.trans (Embedding.subtype (· ∈ A i))
  let t := P.target.trans (Embedding.subtype (· ∈ A (i+1)))
  let S := (univ : Finset Bool).map s
  let T := (univ : Finset Bool).map t
  have hS : S ⊆ A i := by
    intro x hx
    obtain ⟨l,_,rfl⟩ := mem_map.mp hx
    exact (P.source l).prop
  have hT : T ⊆ A (i+1) := by
    intro x hx
    obtain ⟨l,_,rfl⟩ := mem_map.mp hx
    exact (P.target l).prop
  let eS : Bool ≃ S := Equiv.ofBijective (fun l => ⟨s l,mem_map.mpr ⟨l,mem_univ _,rfl⟩⟩)
    ⟨fun _ _ h => s.injective (congrArg (fun a : S => a.val) h),by
      intro v
      obtain ⟨l,_,he⟩ := mem_map.mp v.prop
      exact ⟨l,Subtype.ext he⟩⟩
  let eT : Bool ≃ T := Equiv.ofBijective (fun l => ⟨t l,mem_map.mpr ⟨l,mem_univ _,rfl⟩⟩)
    ⟨fun _ _ h => t.injective (congrArg (fun a : T => a.val) h),by
      intro v
      obtain ⟨l,_,he⟩ := mem_map.mp v.prop
      exact ⟨l,Subtype.ext he⟩⟩
  let f := eS.symm.trans eT
  have hFixed (a : S) : D.Adj a (f a) := by
    obtain ⟨l,rfl⟩ := eS.surjective a
    rw [show f (eS l) = eT l by simp [f]]
    exact P.edge l
  have hScale := mul_le_mul_of_nonneg_right
    (pow_le_one₀ (by linarith : 0 ≤ d-2*ε) (by linarith : d-2*ε ≤ 1) (n := 14))
    (mul_nonneg (by linarith : 0 ≤ d-ε) (Nat.cast_nonneg (α := ℝ) (2*m)))
  have hMargin : (r:ℝ)+(S.card:ℝ) ≤ (d-ε)*((A i).card:ℝ) := by
    have hSc : S.card = 2 := by simp [S]
    rw [hA,hSc]
    norm_num only [Nat.cast_ofNat]
    simp only [one_mul] at hScale
    linarith only [hBudget,hScale,Nat.cast_nonneg (α := ℝ) r]
  obtain ⟨g,hg,hgFixed⟩ := hPair.extend_prescribed_matching D (A i) (A (i+1)) S T d ε r
    hS hT (hA.trans hB.symm) f hFixed hGap hr (by rwa [hA]) hMargin
  let e : Fin m × Fin 2 ≃ A i := (cycleAbsorberSwitchSlot m).trans
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hA)).symm
  obtain ⟨e',h₀,h₁⟩ := exists_equiv_with_two_values e
    (show (j₀,cycleAbsorberLane false) ≠ (j₀,cycleAbsorberLane true) from
      fun h => Bool.false_ne_true (cycleAbsorberLane.injective (congrArg Prod.snd h)))
    (P.source.injective.ne Bool.false_ne_true)
  have hE (l : Bool) : e' (j₀,cycleAbsorberLane l) = P.source l := by cases l <;> assumption
  have hG (l : Bool) : (g (P.source l)).val = (P.target l).val := by
    have he := hgFixed (eS l)
    rw [show f (eS l) = eT l by simp [f]] at he
    exact he
  have hEdge (j : Fin m × Fin 2) : D.Adj (e' j) ((e'.trans g) j) := hg (e' j)
  refine ⟨OrderedClusterPaths.of_pair D A i e' (e'.trans g) hEdge,?_⟩
  intro l
  constructor
  · rw [OrderedClusterPaths.of_pair_left,hE]
  · rw [OrderedClusterPaths.of_pair_right,Equiv.trans_apply,hE,hG]

end OverfullWork.DirectedRobustExpansion
