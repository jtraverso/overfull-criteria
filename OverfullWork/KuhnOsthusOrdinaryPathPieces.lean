module

public import OverfullWork.KuhnOsthusFactorCycleBreaking

@[expose] public section


/-! Distribute a single style class of 1-factor arcs into acyclic pieces
of bounded size, as in the ordinary-edge part of Kühn–Osthus Lemma 8.1. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Reserve adjacent positions for each breaker and its successor. The
remaining sources fill the positions after these disjoint pairs. -/
private theorem exists_cycle_breaking_order (σ : Equiv.Perm V) (S : Finset V)
    (hFixed : ∀ x, σ x ≠ x) :
    ∃ p : S → Fin S.card, Function.Injective p ∧
      ∀ x, (∀ y, σ.SameCycle x y → y ∈ S) →
        ∃ a : S, ∃ b : S, σ.SameCycle x a ∧ σ.SameCycle x b ∧
          (p b).val = (p a).val + 1 := by
  obtain ⟨A,B,hUnion,_,_,_,hOne,hFull,hEvery⟩ := split_factor_style_class σ S hFixed
  have hAS : A ⊆ S := by rw [←hUnion]; exact subset_union_left
  let M := A.map σ.toEmbedding
  have hMS : M ⊆ S := by
    intro m hm
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hm
    exact hFull a ha _ (Equiv.Perm.SameCycle.refl σ a).apply_right
  have hDis : Disjoint A M := by
    rw [disjoint_left]
    intro m hm hM
    obtain ⟨a,ha,he⟩ := mem_map.mp hM
    change σ a = m at he
    subst m
    exact hFixed a (hOne a _ ha hm (Equiv.Perm.SameCycle.refl σ a).apply_right).symm
  let T := S \ (A ∪ M)
  have hCard : 2 * A.card + T.card = S.card := by
    have hSize := card_union_of_disjoint hDis
    rw [show M.card = A.card from card_map _] at hSize
    have ht : T.card = S.card - (A ∪ M).card := card_sdiff_of_subset (union_subset hAS hMS)
    have hle := card_le_card (union_subset hAS hMS)
    omega
  let ea := Finset.equivFin A
  let et := Finset.equivFin T
  have idxM (x : V) (hx : x ∈ M) : σ.symm x ∈ A := by
    obtain ⟨a,ha,he⟩ := mem_map.mp hx
    change σ a = x at he
    rw [←he,σ.symm_apply_apply]
    exact ha
  have idxT (x : S) (ha : (x : V) ∉ A) (hm : (x : V) ∉ M) : (x : V) ∈ T :=
    mem_sdiff.mpr ⟨x.property,fun h => (mem_union.mp h).elim ha hm⟩
  let q (x : S) : ℕ := if ha : (x : V) ∈ A then 2 * (ea ⟨x,ha⟩).val
    else if hm : (x : V) ∈ M then 2 * (ea ⟨σ.symm x,idxM x hm⟩).val + 1
    else 2 * A.card + (et ⟨x,idxT x ha hm⟩).val
  have qLt (x : S) : q x < S.card := by
    dsimp only [q]
    split
    · rename_i ha
      have := (ea ⟨x,ha⟩).isLt
      omega
    · rename_i ha
      split
      · rename_i hm
        have := (ea ⟨σ.symm x,idxM x hm⟩).isLt
        omega
      · rename_i hm
        have := (et ⟨x,idxT x ha hm⟩).isLt
        omega
  let p (x : S) : Fin S.card := ⟨q x,qLt x⟩
  refine ⟨p,?_,?_⟩
  · intro x y he
    have hq : q x = q y := congrArg Fin.val he
    have hA (x : S) (h : (x : V) ∈ A) : q x = 2 * (ea ⟨x,h⟩).val := dif_pos h
    have hM (x : S) (ha : (x : V) ∉ A) (hm : (x : V) ∈ M) :
        q x = 2 * (ea ⟨σ.symm x,idxM x hm⟩).val + 1 := by simp only [q,dif_neg ha,dif_pos hm]
    have hT (x : S) (ha : (x : V) ∉ A) (hm : (x : V) ∉ M) :
        q x = 2 * A.card + (et ⟨x,idxT x ha hm⟩).val := by simp only [q,dif_neg ha,dif_neg hm]
    rcases em ((x : V) ∈ A) with hx | hx
    · rw [hA x hx] at hq
      rcases em ((y : V) ∈ A) with hy | hy
      · rw [hA y hy] at hq
        have hi : (ea ⟨x,hx⟩).val = (ea ⟨y,hy⟩).val := by omega
        exact Subtype.ext (congrArg (fun z : A => (z : V)) (ea.injective (Fin.ext hi)))
      · rcases em ((y : V) ∈ M) with hm | hm
        · rw [hM y hy hm] at hq
          omega
        · rw [hT y hy hm] at hq
          have := (ea ⟨x,hx⟩).isLt
          omega
    · rcases em ((x : V) ∈ M) with hm | hm
      · rw [hM x hx hm] at hq
        rcases em ((y : V) ∈ A) with hy | hy
        · rw [hA y hy] at hq
          omega
        · rcases em ((y : V) ∈ M) with hn | hn
          · rw [hM y hy hn] at hq
            have hi : (ea ⟨σ.symm x,idxM x hm⟩).val = (ea ⟨σ.symm y,idxM y hn⟩).val := by omega
            exact Subtype.ext (σ.symm.injective (congrArg (fun z : A => (z : V)) (ea.injective (Fin.ext hi))))
          · rw [hT y hy hn] at hq
            have := (ea ⟨σ.symm x,idxM x hm⟩).isLt
            omega
      · rw [hT x hx hm] at hq
        rcases em ((y : V) ∈ A) with hy | hy
        · rw [hA y hy] at hq
          have := (ea ⟨y,hy⟩).isLt
          omega
        · rcases em ((y : V) ∈ M) with hn | hn
          · rw [hM y hy hn] at hq
            have := (ea ⟨σ.symm y,idxM y hn⟩).isLt
            omega
          · rw [hT y hy hn] at hq
            have hi : (et ⟨x,idxT x hx hm⟩).val = (et ⟨y,idxT y hy hn⟩).val := by omega
            exact Subtype.ext (congrArg (fun z : T => (z : V)) (et.injective (Fin.ext hi)))
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hEvery x hx
    have hm : σ a ∈ M := mem_map.mpr ⟨a,ha,rfl⟩
    have hn : σ a ∉ A := fun h => (disjoint_left.mp hDis) h hm
    refine ⟨⟨a,hAS ha⟩,⟨σ a,hMS hm⟩,hxa,hxa.apply_right,?_⟩
    change q ⟨σ a,hMS hm⟩ = q ⟨a,hAS ha⟩ + 1
    simp only [q,dif_neg hn,dif_pos hm,dif_pos ha]
    have he : (⟨σ.symm (σ a),idxM (σ a) hm⟩ : A) = ⟨a,ha⟩ :=
      Subtype.ext (σ.symm_apply_apply a)
    rw [he]

/-- Any capacity bound on the class gives the corresponding number of
acyclic pieces, with at most the prescribed capacity in each piece. -/
theorem exists_bounded_acyclic_style_pieces (σ : Equiv.Perm V) (S : Finset V)
    (hFixed : ∀ x, σ x ≠ x) {k t : ℕ} (hk : 2 ≤ k) (hSize : S.card ≤ k*t) :
    ∃ P : Fin k → Finset V,
      (∀ i, P i ⊆ S ∧ (P i).card ≤ t ∧ NoDirectedCycle (factorArcsOn σ (P i))) ∧
      ∀ x ∈ S, ∃! i, x ∈ P i := by
  obtain ⟨p,hp,hPairs⟩ := exists_cycle_breaking_order σ S hFixed
  let P (i : Fin k) := S.filter (fun x => ∃ hx : x ∈ S, (p ⟨x,hx⟩).val % k = i.val)
  have hP (i : Fin k) {x : V} (hx : x ∈ P i) :
      ∃ h : x ∈ S, (p ⟨x,h⟩).val % k = i.val := (mem_filter.mp hx).2
  refine ⟨P,?_,?_⟩
  · intro i
    refine ⟨filter_subset _ _,?_,?_⟩
    · let pick (x : P i) : S := ⟨x,(hP i x.property).choose⟩
      have hRem (x : P i) : (p (pick x)).val % k = i.val := (hP i x.property).choose_spec
      have hLt (x : P i) : (p (pick x)).val / k < t := by
        apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
        rw [Nat.mul_comm]
        exact (p (pick x)).isLt.trans_le hSize
      let f (x : P i) : Fin t := ⟨(p (pick x)).val / k,hLt x⟩
      have hf : Function.Injective f := by
        intro a b he
        have hDiv : (p (pick a)).val / k = (p (pick b)).val / k := congrArg Fin.val he
        have hEq : p (pick a) = p (pick b) := by
          apply Fin.ext
          rw [←Nat.mod_add_div (p (pick a)).val k,←Nat.mod_add_div (p (pick b)).val k,
            hRem a,hRem b,hDiv]
        exact Subtype.ext (congrArg (fun z : S => (z : V)) (hp hEq))
      simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
    · intro x hx
      have hOrbit := factor_cycle_requires_full_orbit σ (P i) x hx
      obtain ⟨a,b,ha,hb,hab⟩ := hPairs x (fun y hy => (hP i (hOrbit y hy)).choose)
      obtain ⟨_,hra⟩ := hP i (hOrbit a ha)
      obtain ⟨_,hrb⟩ := hP i (hOrbit b hb)
      change (p a).val % k = i.val at hra
      change (p b).val % k = i.val at hrb
      rw [hab,Nat.add_mod,Nat.mod_eq_of_lt (show 1 < k by omega),hra] at hrb
      have hi := i.isLt
      by_cases hLast : i.val+1 = k
      · rw [hLast,Nat.mod_self] at hrb
        omega
      · rw [Nat.mod_eq_of_lt (show i.val+1 < k by omega)] at hrb
        omega
  · intro x hx
    let i : Fin k := ⟨(p ⟨x,hx⟩).val % k,Nat.mod_lt _ (by omega)⟩
    exact ⟨i,mem_filter.mpr ⟨hx,hx,rfl⟩,fun j hj => Fin.ext (hP j hj).choose_spec.symm⟩

end OverfullWork.DirectedRobustExpansion
