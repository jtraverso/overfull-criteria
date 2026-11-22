module

public import OverfullWork.KuhnOsthusFirstParityReserve
public import OverfullWork.KuhnOsthusLemma103

@[expose] public section


/-! The two free repair pairs of the cycle absorber are used to
build B₁ in the residual graph of Lemma 10.5. Restore the sixth
exceptional system and retain the four unused triple-switch arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Function Finset
open scoped Classical
variable {V Z : Type*} [Fintype V]

private def prescribedSwitchOfArcs {D : Digraph V} {A B : Finset V} (s t : Bool → V)
    (hs : Injective s) (ht : Injective t)
    (hA : ∀ l, s l ∈ A) (hB : ∀ l, t l ∈ B) (he : ∀ l, D.Adj (s l) (t l)) :
    PrescribedSwitchMatching D A B where
  source := ⟨fun l => ⟨s l,hA l⟩,fun _ _ h => hs (congrArg (fun v : A => v.val) h)⟩
  target := ⟨fun l => ⟨t l,hB l⟩,fun _ _ h => ht (congrArg (fun v : B => v.val) h)⟩
  edge := he

omit [Fintype V] in
/-- Reinserting one exceptional vertex per shortcut preserves the
two bicycle cycles and all marked ordinary vertices. -/
theorem restoreExceptionallyMarkedBicycle [Finite V] {σ : Equiv.Perm V} {τ : Equiv.Perm (V ⊕ Z)}
    (source : Z ↪ V) (hτ : ∀ x y, (restoreExceptionalFactor σ source id).Adj x y ↔ τ x = y)
    {x y : V} (hB : MarkedBicycle σ x y) :
    MarkedBicycle τ (.inl x) (.inl y) := by
  let _ : Finite Z := Finite.of_injective source source.injective
  let project : V ⊕ Z → V := Sum.elim id source
  have hStep (u : V) : τ.SameCycle (.inl u) (.inl (σ u)) := by
    by_cases hu : u ∈ Set.range source
    · obtain ⟨z,rfl⟩ := hu
      have hz := (hτ (.inl (source z)) (.inr z)).mp ⟨z,rfl,rfl⟩
      have hz' := (hτ (.inr z) (.inl (σ (source z)))).mp ⟨z,rfl,rfl⟩
      have h := ((Equiv.Perm.SameCycle.refl τ (.inl (source z))).apply_right).apply_right
      rwa [hz,hz'] at h
    · have he := (hτ (.inl u) (.inl (σ u))).mp ⟨rfl,hu⟩
      have h := (Equiv.Perm.SameCycle.refl τ (.inl u)).apply_right
      rwa [he] at h
  have hProjectStep {u v : V ⊕ Z} (h : τ u = v) :
      σ.SameCycle (project u) (project v) := by
    have he := (hτ u v).mpr h
    rcases u with u | z <;> rcases v with v | w
    · exact he.1 ▸ (Equiv.Perm.SameCycle.refl σ u).apply_right
    · obtain ⟨i,hi,he⟩ := he
      change i = w at he
      subst i
      change σ.SameCycle u (source w)
      rw [hi]
    · obtain ⟨i,hi,he⟩ := he
      change i = z at hi
      subst i
      exact he ▸ (Equiv.Perm.SameCycle.refl σ (source z)).apply_right
    · exact he.elim
  have hLift {u v : V} (h : σ.SameCycle u v) : τ.SameCycle (.inl u) (.inl v) := by
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hn
    have hAt (i : ℕ) : τ.SameCycle (.inl u) (.inl ((σ : V → V)^[i] u)) := by
      induction i with
      | zero => exact Equiv.Perm.SameCycle.refl _ _
      | succ i ih =>
        rw [iterate_succ_apply']
        exact ih.trans (hStep _)
    exact hn ▸ hAt n
  refine ⟨?_,?_⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hn
    have hAt (i : ℕ) : σ.SameCycle x (project ((τ : V ⊕ Z → V ⊕ Z)^[i] (.inl x))) := by
      induction i with
      | zero => exact Equiv.Perm.SameCycle.refl _ _
      | succ i ih =>
        rw [iterate_succ_apply']
        exact ih.trans (hProjectStep rfl)
    have he := hAt n
    rw [hn] at he
    exact hB.1 he
  · intro v
    cases v with
    | inl u => exact (hB.2 u).imp hLift hLift
    | inr z =>
      have hz := (hτ (.inl (source z)) (.inr z)).mp ⟨z,rfl,rfl⟩
      have hs := (Equiv.Perm.SameCycle.refl τ (.inl (source z))).apply_right
      rw [hz] at hs
      exact (hB.2 (source z)).imp (fun h => (hLift h).trans hs) (fun h => (hLift h).trans hs)

/-- The first reserve on the original host, linked to the actual repair
marks of the constructed cycle absorber. The reserved original sixth
system is added exactly, and the four remaining triple-switch arcs
are still available after deleting B₁. -/
theorem NormalizedCycleAbsorber.exists_first_parity_reserve
    {D R : Digraph (V ⊕ Z)} {H H₆ : Digraph V} {q m r : ℕ} {ε₀ ε d a : ℝ}
    (X : Fin (14*q) → Finset V) (hq : 15 ≤ q) (hm : 0 < m) (hRD : R ≤ D)
    (hCover : ∀ v, ∃ i, v ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost R) ε₀ d (X i) (X (finRotate (14*q) i)))
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (ha : 0 ≤ a) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hTol : 2*(ε₀+a) ≤ ε) (hLoss : 3 ≤ a*(((2*m:ℕ):ℝ)*ε))
    (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q}
      {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
      (N : NormalizedCycleAbsorber (G := ordinaryCycleHost R \ E.arcs) E eTop eLow)
      {P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z)}
      {P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z)}
      {P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z)}
      {P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)}
      (_hC : CycleAbsorberOriginalConclusion N D P₂ P₃ P₄ P₅)
      (E₆ : IntervalPathCover H₆ (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q)))
      (P₆ : ProjectedExceptionalArcs D E₆.digraph (id : Z → Z)),
      Disjoint R P₆.original →
      let F := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
      let U := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
      let W := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
      let R' := R \ (F ⊔ U ⊔ W)
      ∃ Q : FirstParityReserve (ordinaryCycleHost R') E₆.digraph (A (7*q+15)) (A (7*q+16)),
        let B₁ := liftOrdinaryCycleArcs Z Q.factor.ordinary ⊔ P₆.original
        B₁ ≤ D ∧ Disjoint B₁ (F ⊔ U ⊔ W) ∧
        (∀ l, Q.factor.mark (l,0) = N.upper.rows.mark (l,Fin.last (2*m)) ∧
          Q.factor.permutation (Q.factor.mark (l,0)) =
            N.upper.permutation (N.upper.rows.mark (!l,Fin.last (2*m)))) ∧
        (∀ l, Q.factor.mark (l,1) = N.lower.rows.mark (l,Fin.last (2*m)) ∧
          Q.factor.permutation (Q.factor.mark (l,1)) =
            N.lower.permutation (N.lower.rows.mark (!l,Fin.last (2*m)))) ∧
        (∃ σ : Equiv.Perm (V ⊕ Z), (∀ x y, B₁.Adj x y ↔ σ x = y) ∧
          MarkedBicycle σ (.inl (Q.factor.mark (false,2))) (.inl (Q.factor.mark (true,2)))) ∧
        (∀ i : Fin 3, i ≠ 0 → ∀ l, (R' \ B₁).Adj (.inl (Q.triple.source l).val)
          (.inl ((Q.triple.matching i).target l).val)) := by
  intro hk A B E eTop eLow N P₂ P₃ P₄ P₅ hC E₆ P₆ hReserved F U W R'
  have hPairs (i : Fin (14*q)) :
      IsLowerSuperregularPair (ordinaryCycleHost R') ε d (X i) (X (finRotate (14*q) i)) :=
    hC.residual_pair R _ _ hm (hSize _) (hSize _) ε₀ ε d a hε hε₁ ha (by linarith) hTol hLoss (hPair i)
  obtain ⟨_,_,_,_,_,_,hProject,_,_⟩ := hC
  let start₀ (l : Bool) := N.upper.rows.mark (l,Fin.last (2*m))
  let end₀ (l : Bool) := N.upper.permutation (start₀ (!l))
  let start₁ (l : Bool) := N.lower.rows.mark (l,Fin.last (2*m))
  let end₁ (l : Bool) := N.lower.permutation (start₁ (!l))
  have start₀Inj : Injective start₀ := fun _ _ h => congrArg Prod.fst (N.upper.rows.mark.injective h)
  have start₁Inj : Injective start₁ := fun _ _ h => congrArg Prod.fst (N.lower.rows.mark.injective h)
  have end₀Inj : Injective end₀ := fun l l' h => by
    have he := start₀Inj (N.upper.permutation.injective h)
    cases l <;> cases l' <;> cases he <;> rfl
  have end₁Inj : Injective end₁ := fun l l' h => by
    have he := start₁Inj (N.lower.permutation.injective h)
    cases l <;> cases l' <;> cases he <;> rfl
  have hOrigin (i : ℕ) : B i = A (7*q+i) := cyclicCluster_rotateClusterArray X hk _ _
  have h₀ (l : Bool) : (ordinaryCycleHost R').Adj (start₀ l) (end₀ l) := by
    have h := N.upper_repair l
    exact ⟨h.1.1,fun he => h.2 (hProject _ _ he)⟩
  have h₁ (l : Bool) : (ordinaryCycleHost R').Adj (start₁ l) (end₁ l) := by
    have h := N.lower_repair l
    exact ⟨h.1.1,fun he => h.2 (hProject _ _ he)⟩
  let M₀ := prescribedSwitchOfArcs start₀ end₀ start₀Inj end₀Inj N.upper.repair_start
    (fun l => N.upper.repair_end (!l)) h₀
  let M₁ := prescribedSwitchOfArcs start₁ end₁ start₁Inj end₁Inj
    (fun l => hOrigin 11 ▸ N.lower.repair_start l) (fun l => hOrigin 12 ▸ N.lower.repair_end (!l)) h₁
  obtain ⟨Q,hQ₀,hQ₁⟩ := kuhn_osthus_lemma_10_5_first_reserve X hq hm hCover hDis hSize hPairs
    hε.le hGap hd hr hCut hBudget M₀ M₁ E₆
  let B₁ := liftOrdinaryCycleArcs Z Q.factor.ordinary ⊔ P₆.original
  have lift_le {L : Digraph V} {S : Digraph (V ⊕ Z)} (h : L ≤ ordinaryCycleHost S) :
      liftOrdinaryCycleArcs Z L ≤ S := by
    rintro (x | x) (y | y) he
    · exact h he
    · exact he.elim
    · exact he.elim
    · exact he.elim
  have hMain : N.mainOrdinary ≤ ordinaryCycleHost R :=
    sup_le (sup_le N.top.paths.unionPaths_le N.topTail.unionPaths_le)
      (sup_le N.low.paths.unionPaths_le N.lowTail.unionPaths_le) |>.trans (fun _ _ h => h.1)
  have hU : N.upper.ordinary ≤ ordinaryCycleHost R :=
    N.upper.ordinary_le.trans (fun _ _ h => h.1.1)
  have hW : N.lower.ordinary ≤ ordinaryCycleHost R := N.lower_le.trans (fun _ _ h => h.1)
  have hOrd : liftOrdinaryCycleArcs Z Q.factor.ordinary ≤ R' := lift_le Q.factor.ordinary_le
  have hex {b c : ℕ} (P : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
      (O : ProjectedExceptionalArcs D P.digraph (id : Z → Z)) (hc : c ≤ 10*q) :
      Disjoint O.original P₆.original := by
    obtain ⟨hOut,hIn⟩ := IntervalPathCover.disjoint_cyclic_slots hk hDis (by omega) (by omega) hc P E₆
    exact O.original_disjoint_of_slots P₆ hOut hIn
  have hSixth : Disjoint (F ⊔ U ⊔ W) P₆.original :=
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨
      disjoint_sup_left.mpr ⟨hReserved.mono_left (lift_le hMain),
        disjoint_sup_left.mpr ⟨hex E.third P₃ (by omega),hex E.fifth P₅ le_rfl⟩⟩,
      disjoint_sup_left.mpr ⟨hReserved.mono_left (lift_le hU),hex E.fourth P₄ (by omega)⟩⟩,
      disjoint_sup_left.mpr ⟨hReserved.mono_left (lift_le hW),hex E.second P₂ (by omega)⟩⟩
  have hOrdDis : Disjoint (liftOrdinaryCycleArcs Z Q.factor.ordinary) (F ⊔ U ⊔ W) := by
    rw [disjoint_iff_inf_le]
    intro x y hh
    exact (hOrd hh.1).2 hh.2
  have hExact : restoreExceptionalFactor Q.factor.permutation P₆.source id = B₁ :=
    P₆.restore_exact Q.factor.permutation Q.factor.exact_factor Q.factor.ordinary_separate
  refine ⟨Q,sup_le (hOrd.trans (fun _ _ h => hRD h.1)) P₆.original_le,
    disjoint_sup_left.mpr ⟨hOrdDis,hSixth.symm⟩,hQ₀,hQ₁,?_,?_⟩
  · obtain ⟨τ,hτ⟩ := exists_restored_exceptional_permutation Q.factor.permutation P₆.source
    refine ⟨τ,fun x y => ?_,restoreExceptionallyMarkedBicycle P₆.source hτ ?_⟩
    · change B₁.Adj x y ↔ τ x = y
      rw [←hExact]
      exact hτ x y
    · exact pca6_initial_markedBicycle Q.factor.permutation Q.factor.mark Q.factor.order 2
  · intro i hi l
    have hFree := Q.unused i hi l
    refine ⟨hFree.1,?_⟩
    intro h
    change B₁.Adj (.inl (Q.triple.source l).val) (.inl ((Q.triple.matching i).target l).val) at h
    rw [←hExact] at h
    exact hFree.2 ((Q.factor.exact_factor _ _).mpr h.1)

/-- Removing a restored winding parity factor costs at most one
matching on each ordinary successor pair. -/
theorem WindingParityFactor.residual_pair_after_restore {D E : Digraph V}
    {H : Digraph (V ⊕ Z)} {m : ℕ}
    (F : WindingParityFactor D E) (P : ProjectedExceptionalArcs H E (id : Z → Z))
    (R : Digraph (V ⊕ Z)) (U W : Finset V) (hm : 0 < m)
    (hU : U.card = 2*m) (hW : W.card = 2*m) (ε η d a : ℝ)
    (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : 1 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPair : IsLowerSuperregularPair (ordinaryCycleHost R) ε d U W) :
    let L := liftOrdinaryCycleArcs Z F.ordinary ⊔ P.original
    IsLowerSuperregularPair (ordinaryCycleHost (R \ L)) η d U W := by
  intro L
  have hExact : restoreExceptionalFactor F.permutation P.source id = L :=
    P.restore_exact F.permutation F.exact_factor F.ordinary_separate
  let M (_ : Fin 1) : Equiv.Perm V := F.permutation
  have hBound : ordinaryCycleHost L ≤ matchingUnion M := by
    intro x y he
    rw [←hExact] at he
    change F.permutation x = y ∧ x ∉ Set.range P.source at he
    exact ⟨0,he.1⟩
  change IsLowerSuperregularPair (ordinaryCycleHost R \ ordinaryCycleHost L) η d U W
  exact residual_pairs_after_matchings M hBound U W hm hU hW ε η d a hη hη₁ ha hd hTol
    (by simpa only [Nat.cast_one] using hBudget) hPair

/-- Removing the restored first reserve costs at most one matching
on each ordinary successor pair, as required to start B₂. -/
theorem OrderedParityFactor.residual_pair_after_restore {D E : Digraph V}
    {H : Digraph (V ⊕ Z)} {m : ℕ}
    (F : OrderedParityFactor D E) (P : ProjectedExceptionalArcs H E (id : Z → Z))
    (R : Digraph (V ⊕ Z)) (U W : Finset V) (hm : 0 < m)
    (hU : U.card = 2*m) (hW : W.card = 2*m) (ε η d a : ℝ)
    (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : 1 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPair : IsLowerSuperregularPair (ordinaryCycleHost R) ε d U W) :
    let L := liftOrdinaryCycleArcs Z F.ordinary ⊔ P.original
    IsLowerSuperregularPair (ordinaryCycleHost (R \ L)) η d U W :=
  WindingParityFactor.residual_pair_after_restore
    ⟨F.ordinary,F.permutation,F.exact_factor,F.ordinary_le,F.ordinary_separate⟩
    P R U W hm hU hW ε η d a hη hη₁ ha hd hTol hBudget hPair

end OverfullWork.DirectedRobustExpansion
