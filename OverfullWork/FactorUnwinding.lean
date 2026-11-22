module

public import OverfullWork.FactorCycleCoordinates
public import OverfullWork.OsthusStadenEvenUnwinding

@[expose] public section


/-! Apply Lemma 4.4 to every cycle of a reduced 1-factor. The fibre
positions and the cyclic distance bounds are retained in the answer. -/
namespace OverfullWork.DirectedRobustExpansion
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

abbrev UnwindingLabel (p : ℕ) := {d : ZMod p // d ≠ 0}

private theorem assemble_factor_unwinding (σ : Equiv.Perm V) (C : FactorCycleCoordinates σ)
    {A : Type*} (p : ℕ) [NeZero p]
    (L : ∀ i : C.Orb, A → Equiv.Perm (Fin (C.length i) × ZMod p))
    (hSame : ∀ i d x y, (L i d).SameCycle x y)
    (hStep : ∀ i d x, (L i d x).1 = finRotate (C.length i) x.1)
    (hDis : ∀ i d d', d ≠ d' → ∀ x, L i d x ≠ L i d' x) :
    ∃ F : A → Equiv.Perm (V × ZMod p),
      (∀ d x, (F d x).1 = σ x.1) ∧
      (∀ d e, d ≠ e → ∀ x, F d x ≠ F e x) ∧
      (∀ d x y, (F d).SameCycle x y ↔ σ.SameCycle x.1 y.1) ∧
      ∀ d i (x : Fin (C.length i) × ZMod p) k,
        ((F d)^k) (C.order ⟨i,x.1⟩,x.2) =
          (C.order ⟨i,(((L i d)^k) x).1⟩,(((L i d)^k) x).2) := by
  let B := Σ i, Fin (C.length i) × ZMod p
  let e : V × ZMod p ≃ B :=
    (C.order.symm.prodCongr (Equiv.refl _)).trans (Equiv.sigmaProdDistrib _ _)
  let G : A → Equiv.Perm B := fun d => Equiv.sigmaCongrRight (fun i => L i d)
  let F : A → Equiv.Perm (V × ZMod p) := fun d => e.permCongr.symm (G d)
  have hPow (d : A) (k : ℕ) (i : C.Orb) (x : Fin (C.length i) × ZMod p) :
      ((G d)^k) ((⟨i,x⟩ : B)) = ⟨i,((L i d)^k) x⟩ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,ih]; rfl
  have hConj (d : A) (k : ℕ) (i : C.Orb) (x : Fin (C.length i) × ZMod p) :
      ((F d)^k) (e.symm ⟨i,x⟩) = e.symm ⟨i,((L i d)^k) x⟩ := by
    apply e.injective
    rw [conjugate_power e (G d) k (e.symm ⟨i,x⟩),e.apply_symm_apply,hPow,e.apply_symm_apply]
  refine ⟨F,?_,?_,?_,?_⟩
  · intro d z
    obtain ⟨⟨i,x⟩,rfl⟩ := e.symm.surjective z
    have h := congrArg Prod.fst (hConj d 1 i x)
    simp only [pow_one] at h
    change (F d (e.symm ⟨i,x⟩)).1 = C.order ⟨i,(L i d x).1⟩ at h
    rw [h,hStep]
    exact (C.successor i x.1).symm
  · intro d d' h z
    obtain ⟨⟨i,x⟩,rfl⟩ := e.symm.surjective z
    intro he
    have hOne (d : A) : F d (e.symm ⟨i,x⟩) = e.symm ⟨i,L i d x⟩ := by
      simpa only [pow_one] using hConj d 1 i x
    rw [hOne,hOne] at he
    have hPair : (⟨i,L i d x⟩ : B) = ⟨i,L i d' x⟩ := e.symm.injective he
    exact hDis i d d' h x (Sigma.mk.inj_iff.mp hPair |>.2 |> eq_of_heq)
  · intro d x y
    obtain ⟨⟨i,a⟩,rfl⟩ := e.symm.surjective x
    obtain ⟨⟨j,b⟩,rfl⟩ := e.symm.surjective y
    change (F d).SameCycle (e.symm ⟨i,a⟩) (e.symm ⟨j,b⟩) ↔
      σ.SameCycle (C.order ⟨i,a.1⟩) (C.order ⟨j,b.1⟩)
    rw [C.same_orbit]
    constructor
    · intro h
      obtain ⟨k,_,hk⟩ := h.exists_pow_eq'
      rw [hConj] at hk
      exact congrArg Sigma.fst (e.symm.injective hk)
    · rintro rfl
      have h := hSame i d a b
      obtain ⟨k,_,hk⟩ := h.exists_pow_eq'
      have he := hConj d k i a
      rw [hk] at he
      rw [←he,Equiv.Perm.sameCycle_pow_right]
  · intro d i x k
    exact hConj d k i x

theorem exists_factor_unwinding (σ : Equiv.Perm V) (C : FactorCycleCoordinates σ)
    (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    ∃ F : UnwindingLabel p → Equiv.Perm (V × ZMod p),
      (∀ d x, (F d x).1 = σ x.1) ∧
      (∀ d e, d ≠ e → ∀ x, F d x ≠ F e x) ∧
      (∀ d x y, (F d).SameCycle x y ↔ σ.SameCycle x.1 y.1) ∧
      ∀ d i (x y : Fin (C.length i) × ZMod p) k, 0 < k →
        x.1.val < C.length i-2 → y.1.val < C.length i-2 → x.2 = y.2 →
        ((F d)^k) (C.order ⟨i,x.1⟩,x.2) = (C.order ⟨i,y.1⟩,y.2) → p ≤ k := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  choose L hCyc hStep hDis hDist using fun i =>
    exists_cycle_unwinding (C.length i) p (C.length_ge_two i) hp hp2
  have hSame i d a b : (L i d).SameCycle a b := by
    obtain ⟨T,z,_,hAll,_,hCh⟩ := hCyc i d
    exact sameCycle_of_successor_chain (L i d) hCh
      (List.mem_append_left _ (hAll a)) (List.mem_append_left _ (hAll b))
  obtain ⟨F,hFirst,hArc,hOrbit,hPow⟩ := assemble_factor_unwinding σ C p L hSame hStep hDis
  refine ⟨F,hFirst,hArc,hOrbit,?_⟩
  intro d i x y k hk hx hy he h
  rw [hPow] at h
  have hy' : ((L i d)^k) x = y := by
    apply Prod.ext
    · exact eq_of_heq (Sigma.mk.inj_iff.mp (C.order.injective (congrArg Prod.fst h))).2
    · exact congrArg (fun z : V × ZMod p => z.2) h
  exact hDist i d k x hk hx (by rw [hy']; exact hy) (by rw [hy']; exact he.symm)

/-- The first refinement of §5.3 uses an even number of cells. -/
theorem exists_even_factor_unwinding (σ : Equiv.Perm V) (C : FactorCycleCoordinates σ)
    (m : ℕ) (hm : 0 < m) :
    ∃ F : UnwindingLabel (2*m) → Equiv.Perm (V × ZMod (2*m)),
      (∀ d x, (F d x).1 = σ x.1) ∧
      (∀ d e, d ≠ e → ∀ x, F d x ≠ F e x) ∧
      ∀ d x y, (F d).SameCycle x y ↔ σ.SameCycle x.1 y.1 := by
  letI : NeZero (2*m) := ⟨by omega⟩
  let label := Fintype.equivFinOfCardEq (count_unwinding_increments (2*m))
  choose L hSame hStep hDis using fun i =>
    exists_even_cycle_unwinding (C.length i) m (C.length_ge_two i) hm
  obtain ⟨F,hFirst,hArc,hOrbit,_⟩ := assemble_factor_unwinding σ C (2*m)
    (fun i d => L i (label d))
    (fun i d => hSame i (label d))
    (fun i d => hStep i (label d))
    (fun i d d' he => hDis i (label d) (label d') (fun h => he (label.injective h)))
  exact ⟨F,hFirst,hArc,hOrbit⟩

end OverfullWork.DirectedRobustExpansion
