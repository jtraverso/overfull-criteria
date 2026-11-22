module

public import OverfullWork.OsthusStadenDivisibleUnwinding

@[expose] public section


/-! A single finite-index statement for both branches of
Osthus–Staden Lemma 4.4. -/
namespace OverfullWork.DirectedRobustExpansion
open scoped Classical

private theorem transfer_cycle {A B : Type*} (e : A ≃ B) (σ : Equiv.Perm B)
    (h : HasSpanningCycle (fun x y => σ x = y)) :
    HasSpanningCycle (fun x y => e.permCongr.symm σ x = y) := by
  obtain ⟨T,z,hN,hAll,hHead,hCh⟩ := h
  refine ⟨T.map e.symm,e.symm z,hN.map e.symm.injective,?_,?_,?_⟩
  · intro v
    exact List.mem_map.mpr ⟨e v,hAll _,e.symm_apply_apply v⟩
  · rw [List.head?_map,hHead]
    rfl
  · rw [←List.map_singleton,←List.map_append]
    apply List.isChain_map_of_isChain e.symm _ hCh
    intro a b h
    rw [Equiv.permCongr_symm_apply,e.apply_symm_apply]
    exact congrArg e.symm h

theorem conjugate_power {A B : Type*} (e : A ≃ B) (σ : Equiv.Perm B) (k : ℕ) (x : A) :
    e (((e.permCongr.symm σ)^k) x) = (σ^k) (e x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,
      Equiv.permCongr_symm_apply,e.apply_symm_apply,ih]

/-- A prime-fold blow-up of a directed cycle has p−1 Hamilton cycles
using distinct arcs. Equal labels in the first n−2 clusters are separated
by at least p steps in each cycle. -/
theorem exists_cycle_unwinding (n p : ℕ) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : 2 < p) :
    ∃ F : {d : ZMod p // d ≠ 0} → Equiv.Perm (Fin n × ZMod p),
      (∀ d, HasSpanningCycle (fun x y => F d x = y)) ∧
      (∀ d x, (F d x).1 = finRotate n x.1) ∧
      (∀ d e, d ≠ e → ∀ x, F d x ≠ F e x) ∧
      ∀ d k (x : Fin n × ZMod p), 0 < k → x.1.val < n-2 →
        (((F d)^k) x).1.val < n-2 → (((F d)^k) x).2 = x.2 → p ≤ k := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero n := ⟨by omega⟩
  by_cases hC : n.Coprime p
  · let e := (ZMod.finEquiv n).toEquiv.prodCongr (Equiv.refl (ZMod p))
    let F := fun d : {d : ZMod p // d ≠ 0} => e.permCongr.symm (unwindingSuccessor n p d.val)
    obtain ⟨hCyc,hFirst,hDis⟩ := coprime_unwinding_family n p hp hC
    refine ⟨F,fun d => transfer_cycle e _ (hCyc d),?_,?_,?_⟩
    · intro d x
      apply (ZMod.finEquiv n).injective
      have h := congrArg Prod.fst (show e (F d x) = unwindingSuccessor n p d.val (e x) from by
        simp [F])
      rw [hFirst d] at h
      change (ZMod.finEquiv n) (F d x).1 = (ZMod.finEquiv n) x.1+1 at h
      rwa [finRotate_apply,map_add,map_one]
    · intro d d' h x hx
      exact hDis d d' h (e x) (by simpa [F] using congrArg e hx)
    · intro d k x hk _ _ he
      have h := congrArg Prod.snd (conjugate_power e (unwindingSuccessor n p d.val) k x)
      change (((F d)^k) x).2 = (((unwindingSuccessor n p d.val)^k) (e x)).2 at h
      exact unwinding_same_label_distance n p hp d.val d.prop k hk (e x) (h.symm.trans he)
  · have hDiv : p ∣ n := hp.dvd_iff_not_coprime.mpr (fun h => hC h.symm)
    have hlt : 2 < n := hp2.trans_le (Nat.le_of_dvd (by omega) hDiv)
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
    have he : n = m+2 := by omega
    clear hm
    subst n
    letI : NeZero m := ⟨by omega⟩
    obtain ⟨hCycle,hFirst,hDis,hDist⟩ := divisible_unwinding_family m p hp hp2 hDiv
    exact ⟨fun d => extendedUnwinding m p d.val,hCycle,hFirst,hDis,by simpa only [Nat.add_sub_cancel] using hDist⟩

end OverfullWork.DirectedRobustExpansion
